package visualizer

import (
	"reflect"
	"strings"
	"testing"
)

func TestGenerateRandomOvChainTraceDeterministic(t *testing.T) {
	opts := OvChainRandomTraceOptions{
		Seed:              12345,
		Threads:           4,
		OpsPerThread:      5,
		KeySpace:          5,
		ValueSpace:        20,
		MaxBurst:          3,
		MaxYieldDecisions: 3,
		BlockedStepChance: 0.25,
	}

	first, err := GenerateRandomOvChainTrace(opts)
	if err != nil {
		t.Fatalf("GenerateRandomOvChainTrace returned error: %v", err)
	}
	second, err := GenerateRandomOvChainTrace(opts)
	if err != nil {
		t.Fatalf("GenerateRandomOvChainTrace returned error: %v", err)
	}
	if !reflect.DeepEqual(first, second) {
		t.Fatalf("generator is not deterministic for a fixed seed:\nfirst=%#v\nsecond=%#v", first, second)
	}
}

func TestGenerateRandomOvChainTraceProducesValidTrace(t *testing.T) {
	trace, err := GenerateRandomOvChainTrace(OvChainRandomTraceOptions{
		Seed:              777,
		Threads:           3,
		OpsPerThread:      6,
		KeySpace:          4,
		ValueSpace:        25,
		MaxBurst:          5,
		MaxYieldDecisions: 4,
		BlockedStepChance: 0.30,
	})
	if err != nil {
		t.Fatalf("GenerateRandomOvChainTrace returned error: %v", err)
	}
	if len(trace.Threads) != 3 {
		t.Fatalf("generated %d threads, want 3", len(trace.Threads))
	}
	for _, thread := range trace.Threads {
		if len(thread.Ops) != 6 {
			t.Fatalf("thread %q has %d ops, want 6", thread.ID, len(thread.Ops))
		}
	}
	if len(trace.Schedule) == 0 {
		t.Fatal("generated schedule is empty")
	}

	result, err := SimulateOvChainTrace(trace)
	if err != nil {
		t.Fatalf("generated trace does not simulate: %v", err)
	}
	if len(result.Events) == 0 {
		t.Fatal("generated simulation produced no events")
	}

	html, err := RenderOvChainTraceHTML(trace)
	if err != nil {
		t.Fatalf("generated trace does not render: %v", err)
	}
	if !strings.Contains(string(html), "<table>") {
		t.Fatalf("rendered HTML is missing the timeline table:\n%s", string(html))
	}
}
