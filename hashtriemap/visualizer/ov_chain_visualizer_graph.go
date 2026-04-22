package visualizer

import (
	"bytes"
	"encoding/json"
	"fmt"
	"html/template"
	"strings"
)

// RenderOvChainTraceGraphHTML simulates a trace and renders an animated graph view.
func RenderOvChainTraceGraphHTML(trace OvChainTrace) ([]byte, error) {
	result, err := SimulateOvChainTrace(trace)
	if err != nil {
		return nil, err
	}
	return RenderOvChainTraceResultGraphHTML(result)
}

// RenderOvChainTraceResultGraphHTML renders a previously simulated trace as an
// animated SVG scene with nodes, arrows, and thread reference overlays.
func RenderOvChainTraceResultGraphHTML(result *OvChainTraceResult) ([]byte, error) {
	model, err := buildOvChainGraphHTMLModel(result)
	if err != nil {
		return nil, err
	}
	var out bytes.Buffer
	if err := ovChainGraphTemplate.Execute(&out, model); err != nil {
		return nil, err
	}
	return out.Bytes(), nil
}

type ovChainGraphHTMLModel struct {
	Title          string
	ThreadPlans    []OvChainThreadPlan
	ThreadOrder    []string
	TotalFrames    int
	FinalReachable string
	FinalDetached  []string
	FramesJSON     template.JS
}

type ovChainGraphFrame struct {
	Step         int                  `json:"step"`
	ThreadID     string               `json:"threadId"`
	OpLabel      string               `json:"opLabel"`
	DisplayOp    string               `json:"displayOp"`
	Source       string               `json:"source"`
	Snippet      string               `json:"snippet"`
	Summary      string               `json:"summary"`
	Impacts      []string             `json:"impacts,omitempty"`
	LockOwner    string               `json:"lockOwner,omitempty"`
	Reachable    ovChainGraphChain    `json:"reachable"`
	Detached     []ovChainGraphChain  `json:"detached"`
	ThreadStates []ovChainGraphThread `json:"threads"`
}

type ovChainGraphChain struct {
	Label string             `json:"label"`
	Kind  string             `json:"kind"`
	Nodes []ovChainGraphNode `json:"nodes"`
}

type ovChainGraphNode struct {
	ID        string   `json:"id"`
	Key       int      `json:"key"`
	Value     int      `json:"value"`
	Refs      []string `json:"refs"`
	Shared    bool     `json:"shared,omitempty"`
	Reachable bool     `json:"reachable,omitempty"`
}

type ovChainGraphThread struct {
	ID         string   `json:"id"`
	Status     string   `json:"status"`
	Current    string   `json:"current,omitempty"`
	Locals     []string `json:"locals,omitempty"`
	LastResult string   `json:"lastResult,omitempty"`
	Active     bool     `json:"active"`
}

func buildOvChainGraphHTMLModel(result *OvChainTraceResult) (ovChainGraphHTMLModel, error) {
	model := ovChainGraphHTMLModel{
		Title:          result.Title,
		ThreadPlans:    result.ThreadPlans,
		ThreadOrder:    result.ThreadOrder,
		TotalFrames:    len(result.Events),
		FinalReachable: result.FinalReachable,
		FinalDetached:  result.FinalDetached,
	}
	if strings.TrimSpace(model.Title) == "" {
		model.Title = "OvChain Trace Graph"
	}
	frames := make([]ovChainGraphFrame, 0, len(result.Events))
	for _, event := range result.Events {
		reachable, err := parseOvRenderedChain(event.Reachable, "head", "reachable")
		if err != nil {
			return ovChainGraphHTMLModel{}, fmt.Errorf("parse reachable chain at step %d: %w", event.Step, err)
		}
		reachableIDs := make(map[string]struct{}, len(reachable.Nodes))
		for i := range reachable.Nodes {
			reachable.Nodes[i].Reachable = true
			reachableIDs[reachable.Nodes[i].ID] = struct{}{}
		}

		frame := ovChainGraphFrame{
			Step:      event.Step,
			ThreadID:  event.ThreadID,
			OpLabel:   event.OpLabel,
			DisplayOp: event.DisplayOp,
			Source:    formatOvSource(event.Source),
			Snippet:   event.Source.Snippet,
			Summary:   event.Summary,
			Impacts:   event.Impacts,
			LockOwner: event.LockOwner,
			Reachable: reachable,
			Detached:  make([]ovChainGraphChain, 0, len(event.Detached)),
		}
		for idx, raw := range event.Detached {
			chain, err := parseOvRenderedChain(raw, fmt.Sprintf("detached %d", idx+1), "detached")
			if err != nil {
				return ovChainGraphHTMLModel{}, fmt.Errorf("parse detached chain at step %d: %w", event.Step, err)
			}
			for i := range chain.Nodes {
				if _, ok := reachableIDs[chain.Nodes[i].ID]; ok {
					chain.Nodes[i].Shared = true
				}
			}
			frame.Detached = append(frame.Detached, chain)
		}
		for _, thread := range event.Threads {
			frame.ThreadStates = append(frame.ThreadStates, ovChainGraphThread{
				ID:         thread.ID,
				Status:     thread.Status,
				Current:    thread.Current,
				Locals:     thread.Locals,
				LastResult: thread.LastResult,
				Active:     thread.ID == event.ThreadID,
			})
		}
		frames = append(frames, frame)
	}
	framesJSON, err := json.Marshal(frames)
	if err != nil {
		return ovChainGraphHTMLModel{}, err
	}
	model.FramesJSON = template.JS(framesJSON)
	return model, nil
}

func parseOvRenderedChain(raw, label, kind string) (ovChainGraphChain, error) {
	chain := ovChainGraphChain{Label: label, Kind: kind, Nodes: []ovChainGraphNode{}}
	trimmed := strings.TrimSpace(raw)
	if trimmed == "" {
		return chain, nil
	}
	if strings.HasPrefix(trimmed, "head -> ") {
		trimmed = strings.TrimPrefix(trimmed, "head -> ")
	}
	parts := strings.Split(trimmed, " -> ")
	for _, part := range parts {
		part = strings.TrimSpace(part)
		if part == "" || part == "nil" {
			continue
		}
		node, err := parseOvRenderedNode(part)
		if err != nil {
			return ovChainGraphChain{}, err
		}
		chain.Nodes = append(chain.Nodes, node)
	}
	return chain, nil
}

func parseOvRenderedNode(raw string) (ovChainGraphNode, error) {
	open := strings.Index(raw, "(")
	close := strings.LastIndex(raw, ")")
	if open <= 0 || close <= open {
		return ovChainGraphNode{}, fmt.Errorf("malformed node %q", raw)
	}
	node := ovChainGraphNode{ID: strings.TrimSpace(raw[:open]), Refs: []string{}}
	body := raw[open+1 : close]
	if idx := strings.Index(body, " ["); idx >= 0 {
		refPart := strings.TrimSuffix(body[idx+2:], "]")
		body = body[:idx]
		if strings.TrimSpace(refPart) != "" {
			node.Refs = strings.Split(refPart, ", ")
		}
	}
	if _, err := fmt.Sscanf(body, "k=%d,v=%d", &node.Key, &node.Value); err != nil {
		return ovChainGraphNode{}, fmt.Errorf("malformed node payload %q: %w", raw, err)
	}
	return node, nil
}

var ovChainGraphTemplate = template.Must(template.New("ovchain-graph").Funcs(template.FuncMap{
	"dec": func(v int) int {
		if v <= 0 {
			return 0
		}
		return v - 1
	},
}).Parse(`<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>{{.Title}}</title>
  <style>
    :root {
      color-scheme: light;
      --bg: #f1eee6;
      --panel: rgba(255, 252, 247, 0.9);
      --line: rgba(56, 73, 87, 0.16);
      --ink: #1f2b37;
      --muted: #60707d;
      --accent: #0d6a72;
      --accent-soft: rgba(13, 106, 114, 0.12);
      --warm: #c96839;
      --warm-soft: rgba(201, 104, 57, 0.13);
      --gold: #b28b1a;
      --gold-soft: rgba(178, 139, 26, 0.14);
      --mono: "Iosevka", "SFMono-Regular", "Menlo", monospace;
      --sans: "IBM Plex Sans", "Segoe UI", sans-serif;
      --shadow: 0 20px 48px rgba(22, 30, 36, 0.08);
    }
    * { box-sizing: border-box; }
    body {
      margin: 0;
      color: var(--ink);
      font-family: var(--sans);
      background:
        radial-gradient(circle at 0% 0%, rgba(13, 106, 114, 0.18), transparent 28%),
        radial-gradient(circle at 100% 10%, rgba(201, 104, 57, 0.12), transparent 24%),
        linear-gradient(180deg, #f8f6f1 0%, var(--bg) 100%);
    }
    main {
      width: min(1600px, calc(100vw - 32px));
      margin: 24px auto 40px;
    }
    h1, h2, h3, p { margin: 0; }
    h1, h2 {
      letter-spacing: -0.03em;
      font-weight: 700;
    }
    p {
      line-height: 1.45;
    }
    code {
      font-family: var(--mono);
      font-size: 0.95em;
    }
    .panel {
      background: var(--panel);
      border: 1px solid var(--line);
      border-radius: 24px;
      box-shadow: var(--shadow);
      backdrop-filter: blur(14px);
    }
    .hero {
      padding: 24px 26px;
      display: grid;
      gap: 16px;
      margin-bottom: 20px;
    }
    .hero-top {
      display: flex;
      justify-content: space-between;
      align-items: flex-start;
      gap: 20px;
      flex-wrap: wrap;
    }
    .hero-meta {
      display: flex;
      gap: 10px;
      flex-wrap: wrap;
    }
    .chip {
      display: inline-flex;
      align-items: center;
      gap: 8px;
      border-radius: 999px;
      padding: 8px 12px;
      background: rgba(255, 255, 255, 0.72);
      border: 1px solid var(--line);
      color: var(--muted);
      font-size: 0.9rem;
    }
    .chip strong {
      color: var(--ink);
    }
    .controls {
      display: grid;
      grid-template-columns: auto auto auto 1fr auto;
      gap: 12px;
      align-items: center;
    }
    button, select {
      appearance: none;
      border: 1px solid rgba(13, 106, 114, 0.18);
      background: #ffffff;
      color: var(--ink);
      border-radius: 999px;
      padding: 10px 14px;
      font: inherit;
      cursor: pointer;
    }
    input[type="range"] {
      width: 100%;
      accent-color: var(--accent);
    }
    .workspace {
      display: grid;
      grid-template-columns: 320px 1fr;
      gap: 18px;
    }
    .sidebar {
      padding: 18px;
      display: grid;
      gap: 14px;
      align-content: start;
      max-height: calc(100vh - 84px);
      overflow: auto;
      position: sticky;
      top: 18px;
    }
    .plan-card {
      border: 1px solid var(--line);
      border-radius: 18px;
      padding: 14px 15px;
      background: rgba(255, 255, 255, 0.74);
    }
    .plan-card h3 {
      margin-bottom: 8px;
      font-size: 1rem;
    }
    .plan-card ul {
      margin: 0;
      padding-left: 18px;
      display: grid;
      gap: 6px;
    }
    .stage-panel {
      padding: 18px;
      display: grid;
      gap: 14px;
    }
    .frame-header {
      display: grid;
      grid-template-columns: 1fr auto;
      gap: 14px;
      align-items: start;
    }
    .frame-header h2 {
      margin-bottom: 8px;
    }
    .frame-header .meta {
      color: var(--muted);
      display: flex;
      gap: 10px;
      flex-wrap: wrap;
      justify-content: flex-end;
    }
    .stage-wrap {
      position: relative;
      min-height: 640px;
      border-radius: 22px;
      overflow: hidden;
      border: 1px solid var(--line);
      background:
        linear-gradient(180deg, rgba(255,255,255,0.92), rgba(246,242,234,0.95)),
        linear-gradient(90deg, rgba(13,106,114,0.03) 1px, transparent 1px),
        linear-gradient(rgba(13,106,114,0.03) 1px, transparent 1px);
      background-size: auto, 48px 48px, 48px 48px;
      box-shadow: inset 0 1px 0 rgba(255,255,255,0.8);
    }
    #ovchain-stage {
      display: block;
      width: 100%;
      height: auto;
      min-height: 640px;
    }
    .detail-grid {
      display: grid;
      grid-template-columns: 1.3fr 1fr;
      gap: 14px;
    }
    .detail-card {
      border: 1px solid var(--line);
      border-radius: 18px;
      background: rgba(255, 255, 255, 0.78);
      padding: 16px;
      display: grid;
      gap: 10px;
    }
    .detail-card h3 {
      font-size: 1rem;
    }
    .detail-card ul {
      margin: 0;
      padding-left: 18px;
      display: grid;
      gap: 8px;
    }
    .snippet, .final-state {
      white-space: pre-wrap;
      word-break: break-word;
      font-family: var(--mono);
      color: var(--muted);
    }
    .final-state {
      display: grid;
      gap: 8px;
      font-size: 0.9rem;
    }
    @media (max-width: 1180px) {
      .workspace {
        grid-template-columns: 1fr;
      }
      .sidebar {
        position: static;
        max-height: none;
      }
      .detail-grid {
        grid-template-columns: 1fr;
      }
    }
    @media (max-width: 720px) {
      main {
        width: calc(100vw - 16px);
        margin: 12px auto 24px;
      }
      .hero, .sidebar, .stage-panel {
        padding: 16px;
      }
      .controls {
        grid-template-columns: 1fr 1fr;
      }
      .controls button,
      .controls select,
      .controls input[type="range"] {
        width: 100%;
      }
    }
  </style>
</head>
<body>
  <main>
    <section class="hero panel">
      <div class="hero-top">
        <div>
          <h1>{{.Title}}</h1>
          <p>Animated scene view of the same source-faithful simulation. Each frame is one semantic step from <code>ov_chain.go</code>, rendered as nodes, arrows, and thread references.</p>
        </div>
        <div class="hero-meta">
          <span class="chip"><strong id="chip-step">Step 1</strong><span id="chip-op">frame</span></span>
          <span class="chip"><strong id="chip-thread">thread</strong><span id="chip-lock">lock free</span></span>
          <span class="chip"><strong>{{.TotalFrames}}</strong><span>frames</span></span>
        </div>
      </div>
      <div class="controls">
        <button id="prevBtn" type="button">Prev</button>
        <button id="playBtn" type="button">Play</button>
        <button id="nextBtn" type="button">Next</button>
        <input id="frameSlider" type="range" min="0" max="{{if gt .TotalFrames 0}}{{dec .TotalFrames}}{{else}}0{{end}}" value="0">
        <select id="speedSelect">
          <option value="1800">0.55x</option>
          <option value="1200" selected>1x</option>
          <option value="700">1.7x</option>
          <option value="400">3x</option>
        </select>
      </div>
    </section>

    <section class="workspace">
      <aside class="sidebar panel">
        <h2>Thread Plans</h2>
        {{range .ThreadPlans}}
        <section class="plan-card">
          <h3><code>{{.ID}}</code></h3>
          <ul>
            {{range .Ops}}<li><code>{{.}}</code></li>{{end}}
          </ul>
        </section>
        {{end}}
        <section class="plan-card">
          <h3>Final State</h3>
          <div class="final-state">
            <div><strong>Reachable</strong></div>
            <code>{{.FinalReachable}}</code>
            {{if .FinalDetached}}
            <div><strong>Detached</strong></div>
            {{range .FinalDetached}}<code>{{.}}</code>{{end}}
            {{else}}
            <div><strong>Detached</strong></div>
            <code>none</code>
            {{end}}
          </div>
        </section>
      </aside>

      <section class="stage-panel panel">
        <div class="frame-header">
          <div>
            <h2 id="frame-title">Frame</h2>
            <p id="frame-summary"></p>
          </div>
          <div class="meta">
            <span id="frame-source"></span>
            <span id="frame-display-op"></span>
          </div>
        </div>
        <div class="stage-wrap">
          <svg id="ovchain-stage" viewBox="0 0 1600 760" aria-label="OvChain animated graph view"></svg>
        </div>
        <div class="detail-grid">
          <section class="detail-card">
            <h3>Source</h3>
            <div id="frame-snippet" class="snippet"></div>
          </section>
          <section class="detail-card">
            <h3>Cross-Thread Impact</h3>
            <ul id="impact-list"></ul>
          </section>
        </div>
      </section>
    </section>
  </main>

  <script>
    const frames = {{.FramesJSON}};
    const svg = document.getElementById("ovchain-stage");
    const slider = document.getElementById("frameSlider");
    const prevBtn = document.getElementById("prevBtn");
    const playBtn = document.getElementById("playBtn");
    const nextBtn = document.getElementById("nextBtn");
    const speedSelect = document.getElementById("speedSelect");
    const chipStep = document.getElementById("chip-step");
    const chipOp = document.getElementById("chip-op");
    const chipThread = document.getElementById("chip-thread");
    const chipLock = document.getElementById("chip-lock");
    const frameTitle = document.getElementById("frame-title");
    const frameSummary = document.getElementById("frame-summary");
    const frameSource = document.getElementById("frame-source");
    const frameDisplayOp = document.getElementById("frame-display-op");
    const frameSnippet = document.getElementById("frame-snippet");
    const impactList = document.getElementById("impact-list");

    const SVG_NS = "http://www.w3.org/2000/svg";
    const threadPalette = [
      "#0d6a72", "#c96839", "#805ad5", "#2f855a", "#dd6b20",
      "#2b6cb0", "#b83280", "#718096"
    ];
    const threadColors = new Map();
    const threadOrder = frames.length ? frames[0].threads.map(thread => thread.id) : [];
    threadOrder.forEach((id, index) => threadColors.set(id, threadPalette[index % threadPalette.length]));

    let frameIndex = 0;
    let timer = null;

    const mk = (name, attrs = {}, text = "") => {
      const node = document.createElementNS(SVG_NS, name);
      for (const [key, value] of Object.entries(attrs)) {
        if (value !== undefined && value !== null) {
          node.setAttribute(key, String(value));
        }
      }
      if (text) {
        node.textContent = text;
      }
      return node;
    };

    function clearChildren(node) {
      while (node.firstChild) node.removeChild(node.firstChild);
    }

    function roundedRect(group, x, y, width, height, radius, fill, stroke, strokeWidth) {
      group.appendChild(mk("rect", { x, y, width, height, rx: radius, fill, stroke, "stroke-width": strokeWidth }));
    }

    function drawText(group, x, y, text, attrs = {}) {
      const node = mk("text", { x, y, ...attrs }, text);
      group.appendChild(node);
      return node;
    }

    function threadAnchorY(index) {
      return 110 + index * 112;
    }

    function nodeFill(chainKind, node) {
      if (chainKind === "reachable") return "rgba(13, 106, 114, 0.14)";
      if (node.shared) return "rgba(178, 139, 26, 0.16)";
      return "rgba(201, 104, 57, 0.14)";
    }

    function nodeStroke(chainKind, node) {
      if (chainKind === "reachable") return "#0d6a72";
      if (node.shared) return "#b28b1a";
      return "#c96839";
    }

    function computeStageHeight(frame) {
      const chains = 1 + frame.detached.length;
      const diagramHeight = 260 + Math.max(0, chains - 1) * 180;
      const threadHeight = 110 + frame.threads.length * 112;
      return Math.max(760, diagramHeight, threadHeight + 80);
    }

    function buildDefs() {
      const defs = mk("defs");
      const markerSolid = mk("marker", {
        id: "arrow-solid",
        markerWidth: 12,
        markerHeight: 12,
        refX: 10,
        refY: 6,
        orient: "auto",
        markerUnits: "strokeWidth"
      });
      markerSolid.appendChild(mk("path", {
        d: "M 0 0 L 12 6 L 0 12 z",
        fill: "#64748b"
      }));
      defs.appendChild(markerSolid);

      const markerThread = mk("marker", {
        id: "arrow-thread",
        markerWidth: 12,
        markerHeight: 12,
        refX: 10,
        refY: 6,
        orient: "auto",
        markerUnits: "strokeWidth"
      });
      markerThread.appendChild(mk("path", {
        d: "M 0 0 L 12 6 L 0 12 z",
        fill: "#0d6a72"
      }));
      defs.appendChild(markerThread);
      return defs;
    }

    function drawThreadCards(root, frame) {
      const positions = new Map();
      const group = mk("g");
      roundedRect(group, 24, 24, 260, computeStageHeight(frame) - 48, 24, "rgba(255,255,255,0.58)", "rgba(56,73,87,0.12)", 1.2);
      drawText(group, 44, 58, "Threads", { "font-size": 24, "font-weight": "700", fill: "#1f2b37" });
      frame.threads.forEach((thread, index) => {
        const x = 42;
        const y = threadAnchorY(index);
        const stroke = threadColors.get(thread.id) || "#0d6a72";
        const fill = thread.active ? "rgba(255, 240, 199, 0.95)" :
          thread.status === "blocked" ? "rgba(249, 215, 210, 0.95)" :
          thread.status === "done" ? "rgba(223, 232, 245, 0.92)" : "rgba(255,255,255,0.88)";
        roundedRect(group, x, y, 224, 88, 22, fill, stroke, thread.active ? 2.6 : 1.4);
        drawText(group, x + 18, y + 26, thread.id, { "font-size": 17, "font-weight": "700", fill: stroke });
        drawText(group, x + 18, y + 48, thread.status, { "font-size": 13, fill: "#60707d" });
        drawText(group, x + 18, y + 68, thread.current || "idle", { "font-size": 13, fill: "#1f2b37" });
        if (thread.lastResult) {
          drawText(group, x + 18, y + 84, thread.lastResult, { "font-size": 11, fill: "#60707d" });
        }
        if (frame.lockOwner === thread.id) {
          roundedRect(group, x + 148, y + 12, 62, 20, 10, "rgba(13,106,114,0.12)", stroke, 1);
          drawText(group, x + 160, y + 26, "LOCK", { "font-size": 11, "font-weight": "700", fill: stroke });
        }
        positions.set(thread.id, { x: x + 224, y: y + 44, color: stroke });
      });
      root.appendChild(group);
      return positions;
    }

    function drawChain(root, chain, y, labelX, startX) {
      const group = mk("g");
      const positions = [];
      const labelFill = chain.kind === "reachable" ? "rgba(13,106,114,0.12)" : "rgba(201,104,57,0.12)";
      const labelStroke = chain.kind === "reachable" ? "#0d6a72" : "#c96839";
      roundedRect(group, labelX, y + 14, 126, 42, 18, labelFill, labelStroke, 1.6);
      drawText(group, labelX + 22, y + 40, chain.label, { "font-size": 18, "font-weight": "700", fill: labelStroke });
      const arrowStartX = labelX + 126;
      const arrowY = y + 35;
      const nodeWidth = 152;
      const nodeHeight = 92;
      const gap = 176;
      if (!chain.nodes.length) {
        group.appendChild(mk("path", {
          d: "M " + arrowStartX + " " + arrowY + " C " + (arrowStartX + 24) + " " + arrowY + ", " + (arrowStartX + 40) + " " + arrowY + ", " + (arrowStartX + 62) + " " + arrowY,
          fill: "none",
          stroke: "#64748b",
          "stroke-width": 2.2,
          "marker-end": "url(#arrow-solid)"
        }));
        roundedRect(group, arrowStartX + 74, y + 15, 74, 40, 16, "rgba(100,116,139,0.08)", "#64748b", 1.2);
        drawText(group, arrowStartX + 96, y + 40, "nil", { "font-size": 18, "font-weight": "700", fill: "#475569" });
        root.appendChild(group);
        return { positions, width: 240 };
      }
      chain.nodes.forEach((node, index) => {
        const x = startX + index * gap;
        const width = nodeWidth;
        const stroke = nodeStroke(chain.kind, node);
        roundedRect(group, x, y, width, nodeHeight, 22, nodeFill(chain.kind, node), stroke, 1.8);
        roundedRect(group, x + 12, y + 12, 44, 24, 12, "rgba(255,255,255,0.8)", stroke, 1.1);
        drawText(group, x + 24, y + 29, node.id, { "font-size": 13, "font-weight": "700", fill: stroke });
        drawText(group, x + 72, y + 34, "key " + node.key, { "font-size": 14, "font-weight": "700", fill: "#1f2b37" });
        drawText(group, x + 72, y + 56, "val " + node.value, { "font-size": 14, fill: "#334155" });
        if (node.shared) {
          roundedRect(group, x + 12, y + 58, 56, 22, 11, "rgba(178,139,26,0.14)", "#b28b1a", 1);
          drawText(group, x + 24, y + 73, "shared", { "font-size": 11, "font-weight": "700", fill: "#8a6d15" });
        }
        const refY = y + nodeHeight + 18;
        node.refs.forEach((ref, refIndex) => {
          const badgeWidth = Math.max(54, 10 + ref.length * 7);
          const badgeX = x + refIndex * (badgeWidth + 8);
          roundedRect(group, badgeX, refY, badgeWidth, 22, 11, "rgba(255,255,255,0.92)", stroke, 1);
          drawText(group, badgeX + 10, refY + 15, ref, { "font-size": 11, fill: stroke });
        });
        positions.push({ x, y, width, height: nodeHeight, node, chainKind: chain.kind });
      });
      group.appendChild(mk("path", {
        d: "M " + arrowStartX + " " + arrowY + " C " + (arrowStartX + 24) + " " + arrowY + ", " + (startX - 24) + " " + arrowY + ", " + startX + " " + arrowY,
        fill: "none",
        stroke: "#64748b",
        "stroke-width": 2.2,
        "marker-end": "url(#arrow-solid)"
      }));
      positions.forEach((pos, index) => {
        const start = pos.x + pos.width;
        const end = index === positions.length - 1 ? pos.x + pos.width + 106 : positions[index + 1].x;
        group.appendChild(mk("path", {
          d: "M " + start + " " + (pos.y + 46) + " C " + (start + 24) + " " + (pos.y + 46) + ", " + (end - 24) + " " + (pos.y + 46) + ", " + end + " " + (pos.y + 46),
          fill: "none",
          stroke: pos.chainKind === "reachable" ? "#0d6a72" : "#c96839",
          "stroke-width": 2.4,
          "marker-end": "url(#arrow-solid)"
        }));
      });
      const nilX = positions[positions.length - 1].x + positions[positions.length - 1].width + 118;
      roundedRect(group, nilX, y + 24, 74, 42, 16, "rgba(100,116,139,0.08)", "#64748b", 1.2);
      drawText(group, nilX + 22, y + 51, "nil", { "font-size": 18, "font-weight": "700", fill: "#475569" });
      root.appendChild(group);
      return { positions, width: nilX + 74 - labelX };
    }

    function drawThreadRefs(root, threadPositions, chainLayouts) {
      const refsGroup = mk("g");
      chainLayouts.forEach(layout => {
        layout.positions.forEach((pos, nodeIndex) => {
          pos.node.refs.forEach((ref, refIndex) => {
            const [threadID] = ref.split(":");
            const thread = threadPositions.get(threadID);
            if (!thread) return;
            const targetX = pos.x + 18 + refIndex * 18;
            const targetY = pos.y - 10;
            const controlX = (thread.x + targetX) / 2;
            refsGroup.appendChild(mk("path", {
              d: "M " + thread.x + " " + thread.y + " C " + controlX + " " + thread.y + ", " + controlX + " " + targetY + ", " + targetX + " " + targetY,
              fill: "none",
              stroke: thread.color,
              "stroke-width": 2,
              "stroke-dasharray": "7 6",
              opacity: 0.92,
              "marker-end": "url(#arrow-thread)"
            }));
          });
        });
      });
      root.appendChild(refsGroup);
    }

    function renderFrame(index) {
      if (!frames.length) return;
      frameIndex = Math.max(0, Math.min(index, frames.length - 1));
      const frame = frames[frameIndex];
      slider.value = frameIndex;

      chipStep.textContent = "Step " + frame.step;
      chipOp.textContent = frame.opLabel + " / " + frame.displayOp;
      chipThread.textContent = frame.threadId;
      chipLock.textContent = frame.lockOwner ? "lock " + frame.lockOwner : "lock free";
      frameTitle.textContent = frame.opLabel + " on " + frame.threadId;
      frameSummary.textContent = frame.summary;
      frameSource.textContent = frame.source || "source";
      frameDisplayOp.textContent = frame.displayOp;
      frameSnippet.textContent = frame.snippet;
      clearChildren(impactList);
      const impacts = frame.impacts && frame.impacts.length ? frame.impacts : ["No cross-thread visibility change on this step."];
      impacts.forEach(impact => {
        const item = document.createElement("li");
        item.textContent = impact;
        impactList.appendChild(item);
      });

      clearChildren(svg);
      svg.appendChild(buildDefs());
      const stageHeight = computeStageHeight(frame);
      svg.setAttribute("viewBox", "0 0 1600 " + stageHeight);

      const background = mk("g");
      roundedRect(background, 302, 24, 1272, stageHeight - 48, 28, "rgba(255,255,255,0.48)", "rgba(56,73,87,0.08)", 1);
      drawText(background, 330, 68, "Structure", { "font-size": 26, "font-weight": "700", fill: "#1f2b37" });
      svg.appendChild(background);

      const threadPositions = drawThreadCards(svg, frame);
      const chainLayouts = [];
      chainLayouts.push(drawChain(svg, frame.reachable, 120, 336, 500));
      frame.detached.forEach((chain, index) => {
        chainLayouts.push(drawChain(svg, chain, 320 + index * 182, 336, 500));
      });
      drawThreadRefs(svg, threadPositions, chainLayouts);
    }

    function stopPlayback() {
      if (timer) {
        clearInterval(timer);
        timer = null;
      }
      playBtn.textContent = "Play";
    }

    function startPlayback() {
      stopPlayback();
      playBtn.textContent = "Pause";
      timer = setInterval(() => {
        if (frameIndex >= frames.length - 1) {
          stopPlayback();
          return;
        }
        renderFrame(frameIndex + 1);
      }, Number(speedSelect.value));
    }

    prevBtn.addEventListener("click", () => {
      stopPlayback();
      renderFrame(frameIndex - 1);
    });
    nextBtn.addEventListener("click", () => {
      stopPlayback();
      renderFrame(frameIndex + 1);
    });
    playBtn.addEventListener("click", () => {
      if (timer) {
        stopPlayback();
      } else {
        startPlayback();
      }
    });
    slider.addEventListener("input", () => {
      stopPlayback();
      renderFrame(Number(slider.value));
    });
    speedSelect.addEventListener("change", () => {
      if (timer) startPlayback();
    });

    renderFrame(0);
  </script>
</body>
</html>
`))
