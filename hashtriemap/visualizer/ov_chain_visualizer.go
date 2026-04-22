package visualizer

import (
	"bytes"
	"fmt"
	"html/template"
	"strings"
)

// RenderOvChainTraceHTML simulates a trace and renders a self-contained HTML page.
func RenderOvChainTraceHTML(trace OvChainTrace) ([]byte, error) {
	result, err := SimulateOvChainTrace(trace)
	if err != nil {
		return nil, err
	}
	return RenderOvChainTraceResultHTML(result)
}

// RenderOvChainTraceResultHTML renders a previously simulated trace.
func RenderOvChainTraceResultHTML(result *OvChainTraceResult) ([]byte, error) {
	model := buildOvChainHTMLModel(result)
	var out bytes.Buffer
	if err := ovChainTraceTemplate.Execute(&out, model); err != nil {
		return nil, err
	}
	return out.Bytes(), nil
}

type ovChainHTMLModel struct {
	Title          string
	ThreadPlans    []OvChainThreadPlan
	ThreadOrder    []string
	Events         []ovChainHTMLEvent
	FinalReachable string
	FinalDetached  []string
}

type ovChainHTMLEvent struct {
	Step       int
	Source     string
	Snippet    string
	Summary    string
	Impacts    []string
	LockOwner  string
	Reachable  string
	Detached   []string
	ThreadCell []ovChainHTMLCell
}

type ovChainHTMLCell struct {
	Active     bool
	ThreadID   string
	Label      string
	Status     string
	Current    string
	Locals     string
	LastResult string
	Summary    string
}

func buildOvChainHTMLModel(result *OvChainTraceResult) ovChainHTMLModel {
	model := ovChainHTMLModel{
		Title:          result.Title,
		ThreadPlans:    result.ThreadPlans,
		ThreadOrder:    result.ThreadOrder,
		FinalReachable: result.FinalReachable,
		FinalDetached:  result.FinalDetached,
	}
	if strings.TrimSpace(model.Title) == "" {
		model.Title = "OvChain Trace"
	}
	for _, event := range result.Events {
		row := ovChainHTMLEvent{
			Step:      event.Step,
			Source:    formatOvSource(event.Source),
			Snippet:   event.Source.Snippet,
			Summary:   event.Summary,
			Impacts:   event.Impacts,
			LockOwner: event.LockOwner,
			Reachable: event.Reachable,
			Detached:  event.Detached,
		}
		snapshots := make(map[string]OvChainThreadSnapshot, len(event.Threads))
		for _, snapshot := range event.Threads {
			snapshots[snapshot.ID] = snapshot
		}
		for _, threadID := range result.ThreadOrder {
			snapshot := snapshots[threadID]
			cell := ovChainHTMLCell{
				ThreadID:   threadID,
				Active:     threadID == event.ThreadID,
				Label:      event.OpLabel,
				Status:     snapshot.Status,
				Current:    snapshot.Current,
				Locals:     strings.Join(snapshot.Locals, ", "),
				LastResult: snapshot.LastResult,
			}
			if cell.Active {
				cell.Summary = event.Summary
			}
			row.ThreadCell = append(row.ThreadCell, cell)
		}
		model.Events = append(model.Events, row)
	}
	return model
}

func formatOvSource(source OvChainSourceRef) string {
	if source.Start == 0 {
		return ""
	}
	if source.Start == source.End {
		return fmt.Sprintf("ov_chain.go:%d", source.Start)
	}
	return fmt.Sprintf("ov_chain.go:%d-%d", source.Start, source.End)
}

var ovChainTraceTemplate = template.Must(template.New("ovchain-trace").Parse(`<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>{{.Title}}</title>
  <style>
    :root {
      color-scheme: light;
      --bg: #f5f1e8;
      --panel: #fffdf8;
      --line: #d9cdb7;
      --ink: #1d2329;
      --muted: #5f6b73;
      --accent: #0b6b5f;
      --accent-soft: #d8efe9;
      --active: #fff0c7;
      --blocked: #f9d7d2;
      --done: #dfe8f5;
      --mono: "Iosevka", "SFMono-Regular", "Menlo", monospace;
      --sans: "IBM Plex Sans", "Segoe UI", sans-serif;
    }
    * { box-sizing: border-box; }
    body {
      margin: 0;
      background:
        radial-gradient(circle at top left, rgba(11, 107, 95, 0.12), transparent 30%),
        linear-gradient(180deg, #fbf7f0 0%, var(--bg) 100%);
      color: var(--ink);
      font-family: var(--sans);
    }
    main {
      width: min(1600px, calc(100vw - 32px));
      margin: 24px auto 48px;
    }
    h1, h2 {
      margin: 0 0 12px;
      font-weight: 700;
      letter-spacing: -0.02em;
    }
    p, li { line-height: 1.45; }
    code {
      font-family: var(--mono);
      font-size: 0.95em;
    }
    .panel {
      background: color-mix(in srgb, var(--panel) 92%, white);
      border: 1px solid var(--line);
      border-radius: 18px;
      box-shadow: 0 12px 30px rgba(24, 32, 38, 0.06);
      padding: 20px 22px;
      margin-bottom: 20px;
      overflow: hidden;
    }
    .meta {
      display: grid;
      gap: 12px;
      grid-template-columns: repeat(auto-fit, minmax(240px, 1fr));
    }
    .thread-plan {
      padding: 14px 16px;
      border: 1px solid var(--line);
      border-radius: 14px;
      background: rgba(255, 255, 255, 0.76);
    }
    .thread-plan h3 {
      margin: 0 0 10px;
      font-size: 1rem;
    }
    .thread-plan ul {
      margin: 0;
      padding-left: 18px;
    }
    table {
      width: 100%;
      border-collapse: collapse;
      table-layout: fixed;
    }
    thead th {
      position: sticky;
      top: 0;
      z-index: 2;
      background: rgba(255, 253, 248, 0.96);
      backdrop-filter: blur(8px);
    }
    th, td {
      border: 1px solid var(--line);
      padding: 10px 12px;
      vertical-align: top;
      text-align: left;
    }
    th {
      font-size: 0.82rem;
      text-transform: uppercase;
      letter-spacing: 0.08em;
      color: var(--muted);
    }
    td.step,
    td.source,
    td.lock,
    td.chain,
    td.impact {
      font-size: 0.92rem;
    }
    .lane {
      min-width: 220px;
      background: rgba(255, 255, 255, 0.74);
    }
    .lane.active {
      background: var(--active);
    }
    .lane.blocked {
      background: var(--blocked);
    }
    .lane.done {
      background: var(--done);
    }
    .lane .label {
      display: inline-block;
      margin-bottom: 6px;
      padding: 2px 7px;
      border-radius: 999px;
      background: rgba(11, 107, 95, 0.12);
      color: var(--accent);
      font-size: 0.78rem;
      font-weight: 700;
    }
    .lane .status {
      display: block;
      color: var(--muted);
      font-size: 0.82rem;
      margin-bottom: 6px;
    }
    .lane .locals,
    .lane .result,
    .snippet,
    .chain-code {
      font-family: var(--mono);
      white-space: pre-wrap;
      word-break: break-word;
    }
    .result {
      color: var(--accent);
      margin-top: 8px;
      font-size: 0.84rem;
    }
    .summary {
      margin-top: 6px;
      font-weight: 600;
    }
    .snippet {
      margin-top: 4px;
      color: var(--muted);
      font-size: 0.84rem;
    }
    .impact ul {
      margin: 0;
      padding-left: 18px;
    }
    .impact .none {
      color: var(--muted);
    }
    .detached {
      margin-top: 8px;
      color: var(--muted);
      font-size: 0.84rem;
    }
    .small {
      color: var(--muted);
      font-size: 0.84rem;
      margin-top: 6px;
    }
    @media (max-width: 960px) {
      main { width: calc(100vw - 16px); margin: 16px auto 28px; }
      .panel { padding: 16px; border-radius: 14px; }
      th, td { padding: 8px 9px; }
    }
  </style>
</head>
<body>
  <main>
    <section class="panel">
      <h1>{{.Title}}</h1>
      <p>Each row is one scheduled semantic step taken directly from <code>ov_chain.go</code>. The selected thread advances by one source-faithful action, while the other lanes show the state they currently hold.</p>
      <div class="meta">
        {{range .ThreadPlans}}
        <div class="thread-plan">
          <h3><code>{{.ID}}</code></h3>
          <ul>
            {{range .Ops}}<li><code>{{.}}</code></li>{{end}}
          </ul>
        </div>
        {{end}}
      </div>
      <div class="small">
        <div><strong>Final reachable chain:</strong> <code>{{.FinalReachable}}</code></div>
        {{if .FinalDetached}}
        <div><strong>Final detached chains:</strong></div>
        <ul>
          {{range .FinalDetached}}<li><code>{{.}}</code></li>{{end}}
        </ul>
        {{else}}
        <div><strong>Final detached chains:</strong> none</div>
        {{end}}
      </div>
    </section>

    <section class="panel">
      <h2>Timeline</h2>
      <table>
        <thead>
          <tr>
            <th style="width:72px;">Step</th>
            <th style="width:160px;">Source</th>
            <th style="width:120px;">Lock</th>
            {{range .ThreadOrder}}<th>{{.}}</th>{{end}}
            <th style="width:360px;">Chain</th>
            <th style="width:280px;">Impact</th>
          </tr>
        </thead>
        <tbody>
          {{range .Events}}
          <tr>
            <td class="step"><strong>{{.Step}}</strong></td>
            <td class="source">
              <div><code>{{.Source}}</code></div>
              <div class="snippet">{{.Snippet}}</div>
            </td>
            <td class="lock">{{if .LockOwner}}<code>{{.LockOwner}}</code>{{else}}free{{end}}</td>
            {{range .ThreadCell}}
            <td class="lane {{if .Active}}active{{else if eq .Status "blocked"}}blocked{{else if eq .Status "done"}}done{{end}}">
              {{if .Active}}
              <span class="label">{{.Label}}</span>
              <span class="status">{{.ThreadID}} ran</span>
              <div class="summary">{{.Summary}}</div>
              {{else}}
              <span class="status">{{.ThreadID}}: {{.Status}}</span>
              {{if .Current}}<div><strong>{{.Current}}</strong></div>{{end}}
              {{end}}
              {{if .Locals}}<div class="locals">{{.Locals}}</div>{{end}}
              {{if .LastResult}}<div class="result">{{.LastResult}}</div>{{end}}
            </td>
            {{end}}
            <td class="chain">
              <div class="chain-code">{{.Reachable}}</div>
              {{if .Detached}}
              <div class="detached">
                {{range .Detached}}<div><code>{{.}}</code></div>{{end}}
              </div>
              {{end}}
            </td>
            <td class="impact">
              {{if .Impacts}}
              <ul>
                {{range .Impacts}}<li>{{.}}</li>{{end}}
              </ul>
              {{else}}
              <div class="none">No cross-thread visibility change on this step.</div>
              {{end}}
            </td>
          </tr>
          {{end}}
        </tbody>
      </table>
    </section>
  </main>
</body>
</html>
`))
