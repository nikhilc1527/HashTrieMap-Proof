package visualizer

import (
	"strings"
	"testing"
)

func TestRenderOvChainTraceGraphHTML(t *testing.T) {
	trace := OvChainTrace{
		Title: "graph smoke test",
		Threads: []OvChainTraceThread{
			{
				ID: "t1",
				Ops: []OvChainTraceOp{
					{Op: "LoadOrStore", Key: ovInt(1), Value: ovInt(10)},
					{Op: "Swap", Key: ovInt(1), New: ovInt(20)},
				},
			},
			{
				ID: "t2",
				Ops: []OvChainTraceOp{
					{Op: "Load", Key: ovInt(1)},
				},
			},
		},
		Schedule: []OvChainScheduleEntry{
			{Thread: "t1", Count: 7},
			{Thread: "t2", Count: 2},
			{Thread: "t1", Count: 9},
			{Thread: "t2", Count: 2},
		},
	}

	html, err := RenderOvChainTraceGraphHTML(trace)
	if err != nil {
		t.Fatalf("RenderOvChainTraceGraphHTML returned error: %v", err)
	}
	out := string(html)
	if !strings.Contains(out, `id="ovchain-stage"`) ||
		!strings.Contains(out, `const frames =`) ||
		!strings.Contains(out, `Play`) ||
		!strings.Contains(out, `detached 1`) ||
		!strings.Contains(out, `"nodes":[]`) {
		t.Fatalf("graph html output missing expected content:\n%s", out)
	}
}
