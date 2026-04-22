package visualizer

import (
	"strings"
	"testing"
)

func TestSimulateOvChainTraceStaleReaderAfterHeadSwap(t *testing.T) {
	trace := OvChainTrace{
		Title: "stale reader after head swap",
		Threads: []OvChainTraceThread{
			{
				ID: "writer",
				Ops: []OvChainTraceOp{
					{Op: "LoadOrStore", Key: ovInt(1), Value: ovInt(10)},
					{Op: "Swap", Key: ovInt(1), New: ovInt(20)},
				},
			},
			{
				ID: "reader",
				Ops: []OvChainTraceOp{
					{Op: "Load", Key: ovInt(1)},
				},
			},
		},
		Schedule: []OvChainScheduleEntry{
			{Thread: "writer", Count: 7},
			{Thread: "reader", Count: 2},
			{Thread: "writer", Count: 9},
			{Thread: "reader", Count: 2},
		},
	}

	result, err := SimulateOvChainTrace(trace)
	if err != nil {
		t.Fatalf("SimulateOvChainTrace returned error: %v", err)
	}
	if got := result.FinalReachable; !strings.Contains(got, "head -> n2(k=1,v=20)") {
		t.Fatalf("final reachable chain = %q, want head to contain swapped value", got)
	}

	var sawImpact bool
	for _, event := range result.Events {
		if strings.Contains(event.Summary, "replaced head n1 with n2") && containsLine(event.Impacts, "reader:e still holds detached n1") {
			sawImpact = true
			break
		}
	}
	if !sawImpact {
		t.Fatalf("expected a swap event showing reader:e holding detached n1; got %#v", result.Events)
	}

	last := result.Events[len(result.Events)-1]
	var readerResult string
	for _, snapshot := range last.Threads {
		if snapshot.ID == "reader" {
			readerResult = snapshot.LastResult
		}
	}
	if readerResult != "(value=10, ok=true)" {
		t.Fatalf("reader saw %q, want stale value from detached head", readerResult)
	}
}

func TestSimulateOvChainTraceStaleReaderAfterInteriorDelete(t *testing.T) {
	trace := OvChainTrace{
		Title: "stale reader after delete splice",
		Threads: []OvChainTraceThread{
			{
				ID: "writer",
				Ops: []OvChainTraceOp{
					{Op: "LoadOrStore", Key: ovInt(1), Value: ovInt(10)},
					{Op: "LoadOrStore", Key: ovInt(2), Value: ovInt(20)},
					{Op: "LoadAndDelete", Key: ovInt(1)},
				},
			},
			{
				ID: "reader",
				Ops: []OvChainTraceOp{
					{Op: "Load", Key: ovInt(1)},
				},
			},
		},
		Schedule: []OvChainScheduleEntry{
			{Thread: "writer", Count: 17},
			{Thread: "reader", Count: 5},
			{Thread: "writer", Count: 10},
			{Thread: "reader", Count: 2},
		},
	}

	result, err := SimulateOvChainTrace(trace)
	if err != nil {
		t.Fatalf("SimulateOvChainTrace returned error: %v", err)
	}
	if got := result.FinalReachable; !strings.Contains(got, "head -> n2(k=2,v=20)") || strings.Contains(got, "k=1,v=10") {
		t.Fatalf("final reachable chain = %q, want only key 2 to remain", got)
	}

	var sawImpact bool
	for _, event := range result.Events {
		if strings.Contains(event.Summary, "rewired n2.overflow from n1 to nil") && containsLine(event.Impacts, "reader:e still holds detached n1") {
			sawImpact = true
			break
		}
	}
	if !sawImpact {
		t.Fatalf("expected delete splice event showing reader:e holding detached n1; got %#v", result.Events)
	}

	last := result.Events[len(result.Events)-1]
	var readerResult string
	for _, snapshot := range last.Threads {
		if snapshot.ID == "reader" {
			readerResult = snapshot.LastResult
		}
	}
	if readerResult != "(value=10, ok=true)" {
		t.Fatalf("reader saw %q, want stale value from detached interior node", readerResult)
	}
}

func TestSimulateOvChainTraceRangeStopsOnFalse(t *testing.T) {
	trace := OvChainTrace{
		Title: "range stop",
		Threads: []OvChainTraceThread{
			{
				ID: "t1",
				Ops: []OvChainTraceOp{
					{Op: "LoadOrStore", Key: ovInt(1), Value: ovInt(10)},
					{Op: "LoadOrStore", Key: ovInt(2), Value: ovInt(20)},
					{Op: "Range", Yield: []bool{true, false}},
				},
			},
		},
		Schedule: []OvChainScheduleEntry{
			{Thread: "t1", Count: 24},
		},
	}

	result, err := SimulateOvChainTrace(trace)
	if err != nil {
		t.Fatalf("SimulateOvChainTrace returned error: %v", err)
	}
	last := result.Events[len(result.Events)-1]
	var got string
	for _, snapshot := range last.Threads {
		if snapshot.ID == "t1" {
			got = snapshot.LastResult
		}
	}
	want := "visited=[2:20=>true, 1:10=>false]"
	if got != want {
		t.Fatalf("Range result = %q, want %q", got, want)
	}
}

func TestRenderOvChainTraceHTML(t *testing.T) {
	trace := OvChainTrace{
		Title: "html smoke test",
		Threads: []OvChainTraceThread{
			{
				ID: "t1",
				Ops: []OvChainTraceOp{
					{Op: "LoadOrStore", Key: ovInt(1), Value: ovInt(10)},
				},
			},
		},
		Schedule: []OvChainScheduleEntry{
			{Thread: "t1", Count: 7},
		},
	}

	html, err := RenderOvChainTraceHTML(trace)
	if err != nil {
		t.Fatalf("RenderOvChainTraceHTML returned error: %v", err)
	}
	out := string(html)
	if !strings.Contains(out, "<table>") || !strings.Contains(out, "ov_chain.go:68-69") || !strings.Contains(out, "head -&gt; n1(k=1,v=10)") {
		t.Fatalf("html output missing expected content:\n%s", out)
	}
}

func ovInt(v int) *int {
	return &v
}

func containsLine(lines []string, want string) bool {
	for _, line := range lines {
		if line == want {
			return true
		}
	}
	return false
}
