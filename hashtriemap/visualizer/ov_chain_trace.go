package visualizer

import (
	"fmt"
	"slices"
	"strings"
)

// OvChainTrace describes one visualization run.
//
// The visualizer consumes per-thread operation streams plus a global schedule.
// Each schedule tick advances the selected thread by exactly one semantic step
// from ov_chain.go, which makes interleavings explicit and easy to generate
// programmatically.
type OvChainTrace struct {
	Title    string                  `json:"title,omitempty"`
	Threads  []OvChainTraceThread    `json:"threads"`
	Schedule []OvChainScheduleEntry  `json:"schedule"`
}

// OvChainTraceThread is a single goroutine lane in the visualization.
type OvChainTraceThread struct {
	ID  string           `json:"id"`
	Ops []OvChainTraceOp `json:"ops"`
}

// OvChainTraceOp is one public API operation against OvChain.
//
// Supported op values:
//   - "Load"
//   - "LoadOrStore"
//   - "Store"
//   - "Swap"
//   - "CompareAndSwap"
//   - "LoadAndDelete"
//   - "Delete"
//   - "CompareAndDelete"
//   - "Clear"
//   - "Range"
//   - "AllOpen"
//   - "AllIterate"
//
// AllOpen models calling oc.All() and binding the returned closure to Iter.
// AllIterate models invoking that previously returned closure.
type OvChainTraceOp struct {
	Label string `json:"label,omitempty"`
	Op    string `json:"op"`

	Key   *int `json:"key,omitempty"`
	Value *int `json:"value,omitempty"`
	Old   *int `json:"old,omitempty"`
	New   *int `json:"new,omitempty"`

	Iter  string `json:"iter,omitempty"`
	Yield []bool `json:"yield,omitempty"`
}

// OvChainScheduleEntry expands into Count individual ticks for Thread.
type OvChainScheduleEntry struct {
	Thread string `json:"thread"`
	Count  int    `json:"count,omitempty"`
}

// OvChainTraceResult is the fully simulated run.
type OvChainTraceResult struct {
	Title          string
	ThreadOrder    []string
	ThreadPlans    []OvChainThreadPlan
	Events         []OvChainTraceEvent
	FinalReachable string
	FinalDetached  []string
}

// OvChainThreadPlan is the planned operation list for a thread.
type OvChainThreadPlan struct {
	ID  string
	Ops []string
}

// OvChainTraceEvent is one scheduled semantic step.
type OvChainTraceEvent struct {
	Step       int
	ThreadID   string
	OpLabel    string
	DisplayOp  string
	Source     OvChainSourceRef
	Summary    string
	Impacts    []string
	LockOwner  string
	Reachable  string
	Detached   []string
	Threads    []OvChainThreadSnapshot
}

// OvChainSourceRef identifies the corresponding source lines in ov_chain.go.
type OvChainSourceRef struct {
	Start   int
	End     int
	Snippet string
}

// OvChainThreadSnapshot describes one lane after a scheduled step.
type OvChainThreadSnapshot struct {
	ID         string
	Status     string
	Current    string
	Locals     []string
	LastResult string
}

// SimulateOvChainTrace runs a schedule-driven OvChain execution trace.
func SimulateOvChainTrace(trace OvChainTrace) (*OvChainTraceResult, error) {
	compiled, err := compileOvChainTrace(trace)
	if err != nil {
		return nil, err
	}
	sim := newOvChainSimulator(compiled)
	return sim.run()
}

type ovCompiledTrace struct {
	title       string
	threads     []*ovThreadPlan
	threadOrder []string
	schedule    []string
}

type ovThreadPlan struct {
	id  string
	ops []ovCompiledOp
}

type ovCompiledOp struct {
	label       string
	displayKind string
	execKind    string
	key         K
	value       V
	old         V
	newValue    V
	iter        string
	yield       []bool
}

func compileOvChainTrace(trace OvChainTrace) (*ovCompiledTrace, error) {
	out, seenThreads, err := compileOvChainThreads(trace.Title, trace.Threads)
	if err != nil {
		return nil, err
	}
	out.schedule, err = expandOvChainSchedule(trace.Schedule, seenThreads)
	if err != nil {
		return nil, err
	}
	return out, nil
}

func compileOvChainThreads(title string, threads []OvChainTraceThread) (*ovCompiledTrace, map[string]struct{}, error) {
	if len(threads) == 0 {
		return nil, nil, fmt.Errorf("trace must contain at least one thread")
	}
	out := &ovCompiledTrace{
		title:       title,
		threads:     make([]*ovThreadPlan, 0, len(threads)),
		threadOrder: make([]string, 0, len(threads)),
	}
	seenThreads := make(map[string]struct{}, len(threads))
	for _, thread := range threads {
		if strings.TrimSpace(thread.ID) == "" {
			return nil, nil, fmt.Errorf("thread id must not be empty")
		}
		if _, ok := seenThreads[thread.ID]; ok {
			return nil, nil, fmt.Errorf("duplicate thread id %q", thread.ID)
		}
		seenThreads[thread.ID] = struct{}{}
		out.threadOrder = append(out.threadOrder, thread.ID)
		plan := &ovThreadPlan{id: thread.ID, ops: make([]ovCompiledOp, 0, len(thread.Ops))}
		for idx, op := range thread.Ops {
			compiledOp, err := compileOvChainTraceOp(thread.ID, idx, op)
			if err != nil {
				return nil, nil, err
			}
			plan.ops = append(plan.ops, compiledOp)
		}
		out.threads = append(out.threads, plan)
	}
	return out, seenThreads, nil
}

func expandOvChainSchedule(schedule []OvChainScheduleEntry, seenThreads map[string]struct{}) ([]string, error) {
	if len(schedule) == 0 {
		return nil, fmt.Errorf("trace schedule must not be empty")
	}
	out := make([]string, 0, len(schedule))
	for _, step := range schedule {
		if _, ok := seenThreads[step.Thread]; !ok {
			return nil, fmt.Errorf("schedule references unknown thread %q", step.Thread)
		}
		count := step.Count
		if count == 0 {
			count = 1
		}
		if count < 0 {
			return nil, fmt.Errorf("schedule count for %q must be positive", step.Thread)
		}
		for range count {
			out = append(out, step.Thread)
		}
	}
	return out, nil
}

func compileOvChainTraceOp(threadID string, index int, op OvChainTraceOp) (ovCompiledOp, error) {
	kind, ok := canonicalOvOp(op.Op)
	if !ok {
		return ovCompiledOp{}, fmt.Errorf("thread %q op %d uses unsupported op %q", threadID, index, op.Op)
	}
	label := strings.TrimSpace(op.Label)
	if label == "" {
		label = fmt.Sprintf("%s[%d]", kind, index+1)
	}
	out := ovCompiledOp{
		label:       label,
		displayKind: kind,
		execKind:    kind,
		iter:        op.Iter,
		yield:       slices.Clone(op.Yield),
	}
	switch kind {
	case "Load":
		key, err := requiredOvInt(op.Key, "key", threadID, index)
		if err != nil {
			return ovCompiledOp{}, err
		}
		out.key = K(key)
	case "LoadOrStore":
		key, err := requiredOvInt(op.Key, "key", threadID, index)
		if err != nil {
			return ovCompiledOp{}, err
		}
		value, err := requiredOvInt(op.Value, "value", threadID, index)
		if err != nil {
			return ovCompiledOp{}, err
		}
		out.key = K(key)
		out.value = V(value)
	case "Store":
		key, err := requiredOvInt(op.Key, "key", threadID, index)
		if err != nil {
			return ovCompiledOp{}, err
		}
		value, err := requiredOvInt(op.Value, "value", threadID, index)
		if err != nil {
			return ovCompiledOp{}, err
		}
		out.key = K(key)
		out.value = V(value)
		out.newValue = V(value)
		out.execKind = "StoreWrapper"
	case "Swap":
		key, err := requiredOvInt(op.Key, "key", threadID, index)
		if err != nil {
			return ovCompiledOp{}, err
		}
		newValue, err := requiredOvInt(op.New, "new", threadID, index)
		if err != nil {
			return ovCompiledOp{}, err
		}
		out.key = K(key)
		out.newValue = V(newValue)
	case "CompareAndSwap":
		key, err := requiredOvInt(op.Key, "key", threadID, index)
		if err != nil {
			return ovCompiledOp{}, err
		}
		oldValue, err := requiredOvInt(op.Old, "old", threadID, index)
		if err != nil {
			return ovCompiledOp{}, err
		}
		newValue, err := requiredOvInt(op.New, "new", threadID, index)
		if err != nil {
			return ovCompiledOp{}, err
		}
		out.key = K(key)
		out.old = V(oldValue)
		out.newValue = V(newValue)
	case "LoadAndDelete":
		key, err := requiredOvInt(op.Key, "key", threadID, index)
		if err != nil {
			return ovCompiledOp{}, err
		}
		out.key = K(key)
	case "Delete":
		key, err := requiredOvInt(op.Key, "key", threadID, index)
		if err != nil {
			return ovCompiledOp{}, err
		}
		out.key = K(key)
		out.execKind = "DeleteWrapper"
	case "CompareAndDelete":
		key, err := requiredOvInt(op.Key, "key", threadID, index)
		if err != nil {
			return ovCompiledOp{}, err
		}
		oldValue, err := requiredOvInt(op.Old, "old", threadID, index)
		if err != nil {
			return ovCompiledOp{}, err
		}
		out.key = K(key)
		out.old = V(oldValue)
	case "Clear":
	case "Range":
	case "AllOpen":
		if strings.TrimSpace(op.Iter) == "" {
			return ovCompiledOp{}, fmt.Errorf("thread %q op %d (%s) requires iter", threadID, index, kind)
		}
	case "AllIterate":
		if strings.TrimSpace(op.Iter) == "" {
			return ovCompiledOp{}, fmt.Errorf("thread %q op %d (%s) requires iter", threadID, index, kind)
		}
	default:
		return ovCompiledOp{}, fmt.Errorf("thread %q op %d has unreachable op kind %q", threadID, index, kind)
	}
	return out, nil
}

func requiredOvInt(value *int, field, threadID string, index int) (int, error) {
	if value == nil {
		return 0, fmt.Errorf("thread %q op %d is missing %s", threadID, index, field)
	}
	return *value, nil
}

func canonicalOvOp(op string) (string, bool) {
	switch strings.ToLower(strings.ReplaceAll(op, "_", "")) {
	case "load":
		return "Load", true
	case "loadorstore":
		return "LoadOrStore", true
	case "store":
		return "Store", true
	case "swap":
		return "Swap", true
	case "compareandswap":
		return "CompareAndSwap", true
	case "loadanddelete":
		return "LoadAndDelete", true
	case "delete":
		return "Delete", true
	case "compareanddelete":
		return "CompareAndDelete", true
	case "clear":
		return "Clear", true
	case "range":
		return "Range", true
	case "allopen":
		return "AllOpen", true
	case "alliterate":
		return "AllIterate", true
	default:
		return "", false
	}
}

type ovChainSimulator struct {
	trace       *ovCompiledTrace
	nextNodeID  int
	initialized bool
	lockOwner   string
	head        *ovVisNode
	threads     map[string]*ovThreadState
	threadOrder []string
	iterators   map[string]struct{}
}

type ovThreadState struct {
	plan       *ovThreadPlan
	opIndex    int
	current    *ovOpState
	lastResult string
	blocked    bool
}

type ovOpState struct {
	spec ovCompiledOp

	opIndex     int
	displayKind string
	execKind    string

	pc int

	hasHead bool
	head    *ovVisNode

	hasE bool
	e    *ovVisNode

	hasI bool
	i    ovSlotRef

	hasNewE bool
	newE    *ovVisNode

	iter      string
	yieldPos  int
	visitLog  []string
	lastYield string
	result    string

	path string
}

type ovVisNode struct {
	ID       string
	Key      K
	Value    V
	Overflow *ovVisNode
}

type ovSlotRef struct {
	head  bool
	owner *ovVisNode
}

type ovStepResult struct {
	source  OvChainSourceRef
	summary string
	impacts []string
	done    bool
	blocked bool
}

func newOvChainSimulator(trace *ovCompiledTrace) *ovChainSimulator {
	sim := &ovChainSimulator{
		trace:       trace,
		threads:     make(map[string]*ovThreadState, len(trace.threads)),
		threadOrder: slices.Clone(trace.threadOrder),
		iterators:   make(map[string]struct{}),
	}
	for _, plan := range trace.threads {
		sim.threads[plan.id] = &ovThreadState{plan: plan}
	}
	return sim
}

func (sim *ovChainSimulator) run() (*OvChainTraceResult, error) {
	result := &OvChainTraceResult{
		Title:       sim.trace.title,
		ThreadOrder: slices.Clone(sim.threadOrder),
		ThreadPlans: make([]OvChainThreadPlan, 0, len(sim.trace.threads)),
	}
	for _, plan := range sim.trace.threads {
		view := OvChainThreadPlan{ID: plan.id, Ops: make([]string, 0, len(plan.ops))}
		for _, op := range plan.ops {
			view.Ops = append(view.Ops, fmt.Sprintf("%s: %s", op.label, ovOpSummary(op)))
		}
		result.ThreadPlans = append(result.ThreadPlans, view)
	}
	for idx, threadID := range sim.trace.schedule {
		thread := sim.threads[threadID]
		if thread == nil {
			return nil, fmt.Errorf("internal error: unknown thread %q", threadID)
		}
		if err := thread.ensureCurrent(); err != nil {
			return nil, err
		}
		opLabel := thread.currentLabel()
		displayOp := thread.currentDisplayKind()
		step, err := sim.stepThread(threadID, thread)
		if err != nil {
			return nil, err
		}
		sim.applyThreadStep(thread, step)
		refs := sim.threadNodeRefs()
		event := OvChainTraceEvent{
			Step:      idx + 1,
			ThreadID:  threadID,
			OpLabel:   opLabel,
			DisplayOp: displayOp,
			Source:    step.source,
			Summary:   step.summary,
			LockOwner: sim.lockOwner,
			Reachable: sim.renderReachableChain(refs),
			Detached:  sim.renderDetachedChains(refs),
			Threads:   sim.snapshots(),
		}
		event.Impacts = append(event.Impacts, step.impacts...)
		if len(step.impacts) > 0 {
			event.Impacts = append(event.Impacts, sim.detachedThreadImpacts(threadID, refs)...)
		}
		result.Events = append(result.Events, event)
	}
	refs := sim.threadNodeRefs()
	result.FinalReachable = sim.renderReachableChain(refs)
	result.FinalDetached = sim.renderDetachedChains(refs)
	return result, nil
}

func (thread *ovThreadState) ensureCurrent() error {
	if thread.current != nil {
		return nil
	}
	if thread.opIndex >= len(thread.plan.ops) {
		return fmt.Errorf("thread %q has no remaining operations for this schedule tick", thread.plan.id)
	}
	thread.current = newOvOpState(thread.plan.ops[thread.opIndex], thread.opIndex)
	thread.blocked = false
	return nil
}

func newOvOpState(spec ovCompiledOp, opIndex int) *ovOpState {
	return &ovOpState{
		spec:        spec,
		opIndex:     opIndex,
		displayKind: spec.displayKind,
		execKind:    spec.execKind,
		iter:        spec.iter,
	}
}

func (sim *ovChainSimulator) applyThreadStep(thread *ovThreadState, step ovStepResult) {
	thread.blocked = step.blocked
	if step.done {
		thread.lastResult = thread.current.result
		thread.current = nil
		thread.opIndex++
		thread.blocked = false
	}
}

func (sim *ovChainSimulator) stepThread(threadID string, thread *ovThreadState) (ovStepResult, error) {
	op := thread.current
	switch op.execKind {
	case "Load":
		return sim.stepLoad(threadID, op), nil
	case "LoadOrStore":
		return sim.stepLoadOrStore(threadID, op), nil
	case "StoreWrapper":
		return sim.stepStoreWrapper(op), nil
	case "Swap":
		return sim.stepSwap(threadID, op), nil
	case "CompareAndSwap":
		return sim.stepCompareAndSwap(threadID, op), nil
	case "LoadAndDelete":
		return sim.stepLoadAndDelete(threadID, op), nil
	case "DeleteWrapper":
		return sim.stepDeleteWrapper(op), nil
	case "CompareAndDelete":
		return sim.stepCompareAndDelete(threadID, op), nil
	case "Clear":
		return sim.stepClear(threadID, op), nil
	case "Range":
		return sim.stepRange(op, false), nil
	case "AllOpen":
		return sim.stepAllOpen(threadID, op)
	case "AllIterate":
		return sim.stepRange(op, true), nil
	default:
		return ovStepResult{}, fmt.Errorf("internal error: unsupported exec kind %q", op.execKind)
	}
}

func (sim *ovChainSimulator) stepLoad(threadID string, op *ovOpState) ovStepResult {
	switch op.pc {
	case 0:
		op.pc++
		return sim.initStep()
	case 1:
		op.e = sim.head
		op.hasE = true
		op.pc++
		return ovStepResult{
			source:  ovSrc(42, 42, "e := oc.head.Load().(*ovEntry)"),
			summary: fmt.Sprintf("loaded head into e: %s", ovNodeID(op.e)),
		}
	case 2:
		if op.e == nil {
			op.result = "(value=0, ok=false)"
			return ovStepResult{
				source:  ovSrc(43, 49, "for e != nil { ... } return *new(V), false"),
				summary: "e is nil; load returns the zero value and ok=false",
				done:    true,
			}
		}
		op.pc++
		return ovStepResult{
			source:  ovSrc(43, 43, "for e != nil {"),
			summary: fmt.Sprintf("loop sees e=%s; continue scanning", ovNodeID(op.e)),
		}
	case 3:
		if op.e.Key == op.spec.key {
			op.result = fmt.Sprintf("(value=%d, ok=true)", op.e.Value)
			return ovStepResult{
				source:  ovSrc(44, 45, "if e.key == key { return e.value, true }"),
				summary: fmt.Sprintf("matched key %d in %s; load returns %d", op.spec.key, op.e.ID, op.e.Value),
				done:    true,
			}
		}
		op.pc++
		return ovStepResult{
			source:  ovSrc(44, 45, "if e.key == key { return e.value, true }"),
			summary: fmt.Sprintf("key %d does not match %s(key=%d); keep scanning", op.spec.key, op.e.ID, op.e.Key),
		}
	default:
		op.e = op.e.Overflow
		op.pc = 2
		return ovStepResult{
			source:  ovSrc(47, 47, "e = e.overflow.Load().(*ovEntry)"),
			summary: fmt.Sprintf("advanced e to %s", ovNodeID(op.e)),
		}
	}
}

func (sim *ovChainSimulator) stepLoadOrStore(threadID string, op *ovOpState) ovStepResult {
	switch op.pc {
	case 0:
		op.pc++
		return sim.initStep()
	case 1:
		if !sim.tryLock(threadID) {
			return ovStepResult{
				source:  ovSrc(57, 58, "oc.mu.Lock(); defer oc.mu.Unlock()"),
				summary: fmt.Sprintf("blocked on mu; %s currently holds it", sim.lockOwner),
				blocked: true,
			}
		}
		op.pc++
		return ovStepResult{
			source:  ovSrc(57, 58, "oc.mu.Lock(); defer oc.mu.Unlock()"),
			summary: "acquired mu for LoadOrStore",
		}
	case 2:
		op.head = sim.head
		op.hasHead = true
		op.e = op.head
		op.hasE = true
		op.pc++
		return ovStepResult{
			source:  ovSrc(60, 61, "head := oc.head.Load(); for e := head; ..."),
			summary: fmt.Sprintf("captured head=%s and initialized e=head", ovNodeID(op.head)),
		}
	case 3:
		if op.e == nil {
			op.path = "insert"
			op.pc = 6
			return ovStepResult{
				source:  ovSrc(61, 65, "for e := head; e != nil; ..."),
				summary: "scan reached nil; the key is absent and a new head entry will be inserted",
			}
		}
		op.pc++
		return ovStepResult{
			source:  ovSrc(61, 61, "for e := head; e != nil; ..."),
			summary: fmt.Sprintf("scan is visiting %s", ovNodeID(op.e)),
		}
	case 4:
		if op.e.Key == op.spec.key {
			op.result = fmt.Sprintf("(result=%d, loaded=true)", op.e.Value)
			sim.unlock(threadID)
			return ovStepResult{
				source:  ovSrc(62, 63, "if e.key == key { return e.value, true }"),
				summary: fmt.Sprintf("found existing key %d in %s; returning loaded value %d and unlocking", op.spec.key, op.e.ID, op.e.Value),
				done:    true,
			}
		}
		op.pc++
		return ovStepResult{
			source:  ovSrc(62, 64, "if e.key == key { ... }"),
			summary: fmt.Sprintf("%s holds key %d, not target %d", op.e.ID, op.e.Key, op.spec.key),
		}
	case 5:
		op.e = op.e.Overflow
		op.pc = 3
		return ovStepResult{
			source:  ovSrc(61, 61, "e = e.overflow.Load().(*ovEntry)"),
			summary: fmt.Sprintf("advanced e to %s", ovNodeID(op.e)),
		}
	case 6:
		op.newE = sim.newNode(op.spec.key, op.spec.value)
		op.hasNewE = true
		op.pc++
		return ovStepResult{
			source:  ovSrc(66, 66, "newE := newOvEntry(key, value)"),
			summary: fmt.Sprintf("allocated %s for key=%d value=%d with overflow=nil", op.newE.ID, op.newE.Key, op.newE.Value),
		}
	case 7:
		op.newE.Overflow = op.head
		op.pc++
		return ovStepResult{
			source:  ovSrc(67, 67, "newE.overflow.Store(head)"),
			summary: fmt.Sprintf("set %s.overflow = %s", op.newE.ID, ovNodeID(op.head)),
		}
	default:
		before := sim.head
		sim.head = op.newE
		sim.unlock(threadID)
		op.result = fmt.Sprintf("(result=%d, loaded=false)", op.spec.value)
		return ovStepResult{
			source:  ovSrc(68, 69, "oc.head.Store(newE); return value, false"),
			summary: fmt.Sprintf("published %s as the new head and unlocked", op.newE.ID),
			impacts: sim.mutationImpacts(ovHeadSlot(), before, sim.head),
			done:    true,
		}
	}
}

func (sim *ovChainSimulator) stepStoreWrapper(op *ovOpState) ovStepResult {
	op.execKind = "Swap"
	op.pc = 0
	return ovStepResult{
		source:  ovSrc(73, 75, "func (oc *OvChain) Store(key K, value V) { _, _ = oc.Swap(key, value) }"),
		summary: "Store delegates to Swap and discards the returned previous value",
	}
}

func (sim *ovChainSimulator) stepSwap(threadID string, op *ovOpState) ovStepResult {
	switch op.pc {
	case 0:
		op.pc++
		return sim.initStep()
	case 1:
		if !sim.tryLock(threadID) {
			return ovStepResult{
				source:  ovSrc(81, 82, "oc.mu.Lock(); defer oc.mu.Unlock()"),
				summary: fmt.Sprintf("blocked on mu; %s currently holds it", sim.lockOwner),
				blocked: true,
			}
		}
		op.pc++
		return ovStepResult{
			source:  ovSrc(81, 82, "oc.mu.Lock(); defer oc.mu.Unlock()"),
			summary: "acquired mu for Swap",
		}
	case 2:
		op.head = sim.head
		op.hasHead = true
		op.pc++
		return ovStepResult{
			source:  ovSrc(84, 84, "head := oc.head.Load().(*ovEntry)"),
			summary: fmt.Sprintf("captured head=%s", ovNodeID(op.head)),
		}
	case 3:
		if op.head == nil {
			op.path = "insert"
			op.pc = 19
			return ovStepResult{
				source:  ovSrc(85, 102, "if head != nil { ... }"),
				summary: "head is nil; Swap will insert a brand new head node",
			}
		}
		op.pc++
		return ovStepResult{
			source:  ovSrc(85, 85, "if head != nil {"),
			summary: fmt.Sprintf("head=%s is non-nil; check whether it matches key %d", op.head.ID, op.spec.key),
		}
	case 4:
		if op.head.Key == op.spec.key {
			op.path = "head-replace"
			op.pc = 11
			return ovStepResult{
				source:  ovSrc(86, 90, "if head.key == key { ... }"),
				summary: fmt.Sprintf("head %s already holds key %d; Swap will replace the head entry", op.head.ID, op.spec.key),
			}
		}
		op.hasI = true
		op.i = ovOverflowSlot(op.head)
		op.pc = 6
		return ovStepResult{
			source:  ovSrc(86, 92, "if head.key == key { ... }; i := &head.overflow"),
			summary: fmt.Sprintf("head key %d does not match %d; start scanning from %s", op.head.Key, op.spec.key, op.i.String()),
		}
	case 6:
		op.e = op.i.load(sim)
		op.hasE = true
		op.pc++
		return ovStepResult{
			source:  ovSrc(93, 93, "for e := i.Load().(*ovEntry); e != nil; ..."),
			summary: fmt.Sprintf("loaded e from %s: %s", op.i.String(), ovNodeID(op.e)),
		}
	case 7:
		if op.e == nil {
			op.path = "insert"
			op.pc = 19
			return ovStepResult{
				source:  ovSrc(93, 101, "for e := i.Load(); e != nil; ..."),
				summary: "scan reached nil without finding the key; Swap will insert at head",
			}
		}
		op.pc++
		return ovStepResult{
			source:  ovSrc(93, 93, "e != nil"),
			summary: fmt.Sprintf("scan is visiting %s", ovNodeID(op.e)),
		}
	case 8:
		if op.e.Key == op.spec.key {
			op.path = "interior-replace"
			op.pc = 15
			return ovStepResult{
				source:  ovSrc(94, 99, "if e.key == key { ... }"),
				summary: fmt.Sprintf("found key %d in %s; Swap will replace it through %s", op.spec.key, op.e.ID, op.i.String()),
			}
		}
		op.pc++
		return ovStepResult{
			source:  ovSrc(94, 100, "if e.key == key { ... }; i = &e.overflow"),
			summary: fmt.Sprintf("%s holds key %d, not %d", op.e.ID, op.e.Key, op.spec.key),
		}
	case 9:
		op.i = ovOverflowSlot(op.e)
		op.pc = 6
		return ovStepResult{
			source:  ovSrc(100, 100, "i = &e.overflow"),
			summary: fmt.Sprintf("advanced predecessor slot to %s", op.i.String()),
		}
	case 11:
		op.newE = sim.newNode(op.spec.key, op.spec.newValue)
		op.hasNewE = true
		op.pc++
		return ovStepResult{
			source:  ovSrc(87, 87, "newE := newOvEntry(key, new)"),
			summary: fmt.Sprintf("allocated replacement head %s with value=%d", op.newE.ID, op.newE.Value),
		}
	case 12:
		op.newE.Overflow = op.head.Overflow
		op.pc++
		return ovStepResult{
			source:  ovSrc(88, 88, "newE.overflow.Store(head.overflow.Load().(*ovEntry))"),
			summary: fmt.Sprintf("copied head tail into %s.overflow = %s", op.newE.ID, ovNodeID(op.newE.Overflow)),
		}
	case 13:
		before := sim.head
		sim.head = op.newE
		op.pc++
		return ovStepResult{
			source:  ovSrc(89, 89, "oc.head.Store(newE)"),
			summary: fmt.Sprintf("replaced head %s with %s", ovNodeID(before), op.newE.ID),
			impacts: sim.mutationImpacts(ovHeadSlot(), before, sim.head),
		}
	case 14:
		sim.unlock(threadID)
		op.result = fmt.Sprintf("(previous=%d, loaded=true)", op.head.Value)
		return ovStepResult{
			source:  ovSrc(90, 90, "return head.value, true"),
			summary: fmt.Sprintf("Swap returns previous=%d, loaded=true and unlocks", op.head.Value),
			done:    true,
		}
	case 15:
		op.newE = sim.newNode(op.spec.key, op.spec.newValue)
		op.hasNewE = true
		op.pc++
		return ovStepResult{
			source:  ovSrc(95, 95, "newE := newOvEntry(key, new)"),
			summary: fmt.Sprintf("allocated replacement node %s with value=%d", op.newE.ID, op.newE.Value),
		}
	case 16:
		op.newE.Overflow = op.e.Overflow
		op.pc++
		return ovStepResult{
			source:  ovSrc(96, 96, "newE.overflow.Store(e.overflow.Load().(*ovEntry))"),
			summary: fmt.Sprintf("copied %s tail into %s.overflow = %s", op.e.ID, op.newE.ID, ovNodeID(op.newE.Overflow)),
		}
	case 17:
		before := op.i.load(sim)
		op.i.store(sim, op.newE)
		op.pc++
		return ovStepResult{
			source:  ovSrc(97, 97, "i.Store(newE)"),
			summary: fmt.Sprintf("rewired %s from %s to %s", op.i.String(), ovNodeID(before), op.newE.ID),
			impacts: sim.mutationImpacts(op.i, before, op.newE),
		}
	case 18:
		sim.unlock(threadID)
		op.result = fmt.Sprintf("(previous=%d, loaded=true)", op.e.Value)
		return ovStepResult{
			source:  ovSrc(98, 98, "return e.value, true"),
			summary: fmt.Sprintf("Swap returns previous=%d, loaded=true and unlocks", op.e.Value),
			done:    true,
		}
	case 19:
		op.newE = sim.newNode(op.spec.key, op.spec.newValue)
		op.hasNewE = true
		op.pc++
		return ovStepResult{
			source:  ovSrc(103, 103, "newE := newOvEntry(key, new)"),
			summary: fmt.Sprintf("allocated inserted head %s with value=%d", op.newE.ID, op.newE.Value),
		}
	case 20:
		op.newE.Overflow = op.head
		op.pc++
		return ovStepResult{
			source:  ovSrc(104, 104, "newE.overflow.Store(head)"),
			summary: fmt.Sprintf("set %s.overflow = %s", op.newE.ID, ovNodeID(op.head)),
		}
	default:
		before := sim.head
		sim.head = op.newE
		sim.unlock(threadID)
		op.result = "(previous=0, loaded=false)"
		return ovStepResult{
			source:  ovSrc(105, 107, "oc.head.Store(newE); var zero V; return zero, false"),
			summary: fmt.Sprintf("published inserted head %s, returning loaded=false and unlocking", op.newE.ID),
			impacts: sim.mutationImpacts(ovHeadSlot(), before, sim.head),
			done:    true,
		}
	}
}

func (sim *ovChainSimulator) stepCompareAndSwap(threadID string, op *ovOpState) ovStepResult {
	switch op.pc {
	case 0:
		op.pc++
		return sim.initStep()
	case 1:
		if !sim.tryLock(threadID) {
			return ovStepResult{
				source:  ovSrc(114, 115, "oc.mu.Lock(); defer oc.mu.Unlock()"),
				summary: fmt.Sprintf("blocked on mu; %s currently holds it", sim.lockOwner),
				blocked: true,
			}
		}
		op.pc++
		return ovStepResult{
			source:  ovSrc(114, 115, "oc.mu.Lock(); defer oc.mu.Unlock()"),
			summary: "acquired mu for CompareAndSwap",
		}
	case 2:
		op.head = sim.head
		op.hasHead = true
		op.pc++
		return ovStepResult{
			source:  ovSrc(117, 117, "head := oc.head.Load().(*ovEntry)"),
			summary: fmt.Sprintf("captured head=%s", ovNodeID(op.head)),
		}
	case 3:
		if op.head == nil {
			sim.unlock(threadID)
			op.result = "false"
			return ovStepResult{
				source:  ovSrc(118, 120, "if head == nil { return false }"),
				summary: "head is nil; CompareAndSwap fails and unlocks",
				done:    true,
			}
		}
		op.pc++
		return ovStepResult{
			source:  ovSrc(118, 120, "if head == nil { return false }"),
			summary: "head is present; check the head entry first",
		}
	case 4:
		if op.head.Key == op.spec.key && op.head.Value == op.spec.old {
			op.pc = 11
			return ovStepResult{
				source:  ovSrc(121, 125, "if head.key == key && head.value == old { ... }"),
				summary: fmt.Sprintf("head %s matches key=%d old=%d; replacing head", op.head.ID, op.spec.key, op.spec.old),
			}
		}
		op.hasI = true
		op.i = ovOverflowSlot(op.head)
		op.pc = 6
		return ovStepResult{
			source:  ovSrc(121, 127, "if head.key == key && head.value == old { ... }; i := &head.overflow"),
			summary: fmt.Sprintf("head does not match key=%d old=%d; scan from %s", op.spec.key, op.spec.old, op.i.String()),
		}
	case 6:
		op.e = op.i.load(sim)
		op.hasE = true
		op.pc++
		return ovStepResult{
			source:  ovSrc(128, 128, "for e := i.Load().(*ovEntry); e != nil; ..."),
			summary: fmt.Sprintf("loaded e from %s: %s", op.i.String(), ovNodeID(op.e)),
		}
	case 7:
		if op.e == nil {
			sim.unlock(threadID)
			op.result = "false"
			return ovStepResult{
				source:  ovSrc(128, 137, "for e := i.Load(); e != nil; ...; return false"),
				summary: "scan reached nil without a matching key/value pair; CompareAndSwap fails and unlocks",
				done:    true,
			}
		}
		op.pc++
		return ovStepResult{
			source:  ovSrc(128, 128, "e != nil"),
			summary: fmt.Sprintf("scan is visiting %s", ovNodeID(op.e)),
		}
	case 8:
		if op.e.Key == op.spec.key && op.e.Value == op.spec.old {
			op.pc = 15
			return ovStepResult{
				source:  ovSrc(129, 133, "if e.key == key && e.value == old { ... }"),
				summary: fmt.Sprintf("found matching key/value pair in %s; replacing through %s", op.e.ID, op.i.String()),
			}
		}
		op.pc++
		return ovStepResult{
			source:  ovSrc(129, 135, "if e.key == key && e.value == old { ... }; i = &e.overflow"),
			summary: fmt.Sprintf("%s does not match key=%d old=%d", ovNodeID(op.e), op.spec.key, op.spec.old),
		}
	case 9:
		op.i = ovOverflowSlot(op.e)
		op.pc = 6
		return ovStepResult{
			source:  ovSrc(135, 135, "i = &e.overflow"),
			summary: fmt.Sprintf("advanced predecessor slot to %s", op.i.String()),
		}
	case 11:
		op.newE = sim.newNode(op.spec.key, op.spec.newValue)
		op.hasNewE = true
		op.pc++
		return ovStepResult{
			source:  ovSrc(122, 122, "newE := newOvEntry(key, new)"),
			summary: fmt.Sprintf("allocated replacement head %s with value=%d", op.newE.ID, op.newE.Value),
		}
	case 12:
		op.newE.Overflow = op.head.Overflow
		op.pc++
		return ovStepResult{
			source:  ovSrc(123, 123, "newE.overflow.Store(head.overflow.Load().(*ovEntry))"),
			summary: fmt.Sprintf("copied head tail into %s.overflow = %s", op.newE.ID, ovNodeID(op.newE.Overflow)),
		}
	case 13:
		before := sim.head
		sim.head = op.newE
		op.pc++
		return ovStepResult{
			source:  ovSrc(124, 124, "oc.head.Store(newE)"),
			summary: fmt.Sprintf("replaced head %s with %s", ovNodeID(before), op.newE.ID),
			impacts: sim.mutationImpacts(ovHeadSlot(), before, sim.head),
		}
	case 14:
		sim.unlock(threadID)
		op.result = "true"
		return ovStepResult{
			source:  ovSrc(125, 125, "return true"),
			summary: "CompareAndSwap succeeded and unlocked",
			done:    true,
		}
	case 15:
		op.newE = sim.newNode(op.spec.key, op.spec.newValue)
		op.hasNewE = true
		op.pc++
		return ovStepResult{
			source:  ovSrc(130, 130, "newE := newOvEntry(key, new)"),
			summary: fmt.Sprintf("allocated replacement node %s with value=%d", op.newE.ID, op.newE.Value),
		}
	case 16:
		op.newE.Overflow = op.e.Overflow
		op.pc++
		return ovStepResult{
			source:  ovSrc(131, 131, "newE.overflow.Store(e.overflow.Load().(*ovEntry))"),
			summary: fmt.Sprintf("copied %s tail into %s.overflow = %s", ovNodeID(op.e), op.newE.ID, ovNodeID(op.newE.Overflow)),
		}
	case 17:
		before := op.i.load(sim)
		op.i.store(sim, op.newE)
		op.pc++
		return ovStepResult{
			source:  ovSrc(132, 132, "i.Store(newE)"),
			summary: fmt.Sprintf("rewired %s from %s to %s", op.i.String(), ovNodeID(before), op.newE.ID),
			impacts: sim.mutationImpacts(op.i, before, op.newE),
		}
	default:
		sim.unlock(threadID)
		op.result = "true"
		return ovStepResult{
			source:  ovSrc(133, 133, "return true"),
			summary: "CompareAndSwap succeeded and unlocked",
			done:    true,
		}
	}
}

func (sim *ovChainSimulator) stepLoadAndDelete(threadID string, op *ovOpState) ovStepResult {
	switch op.pc {
	case 0:
		op.pc++
		return sim.initStep()
	case 1:
		if !sim.tryLock(threadID) {
			return ovStepResult{
				source:  ovSrc(144, 145, "oc.mu.Lock(); defer oc.mu.Unlock()"),
				summary: fmt.Sprintf("blocked on mu; %s currently holds it", sim.lockOwner),
				blocked: true,
			}
		}
		op.pc++
		return ovStepResult{
			source:  ovSrc(144, 145, "oc.mu.Lock(); defer oc.mu.Unlock()"),
			summary: "acquired mu for LoadAndDelete",
		}
	case 2:
		op.head = sim.head
		op.hasHead = true
		op.pc++
		return ovStepResult{
			source:  ovSrc(147, 147, "head := oc.head.Load().(*ovEntry)"),
			summary: fmt.Sprintf("captured head=%s", ovNodeID(op.head)),
		}
	case 3:
		if op.head == nil {
			sim.unlock(threadID)
			op.result = "(value=0, loaded=false)"
			return ovStepResult{
				source:  ovSrc(148, 150, "if head == nil { return *new(V), false }"),
				summary: "head is nil; LoadAndDelete returns the zero value and unlocks",
				done:    true,
			}
		}
		op.pc++
		return ovStepResult{
			source:  ovSrc(148, 150, "if head == nil { ... }"),
			summary: "head is present; check whether the head entry matches",
		}
	case 4:
		if op.head.Key == op.spec.key {
			op.pc = 11
			return ovStepResult{
				source:  ovSrc(151, 153, "if head.key == key { oc.head.Store(...); return head.value, true }"),
				summary: fmt.Sprintf("head %s matches key %d; delete it by advancing head", op.head.ID, op.spec.key),
			}
		}
		op.hasI = true
		op.i = ovOverflowSlot(op.head)
		op.pc = 6
		return ovStepResult{
			source:  ovSrc(151, 155, "if head.key == key { ... }; i := &head.overflow"),
			summary: fmt.Sprintf("head key %d does not match %d; scan from %s", op.head.Key, op.spec.key, op.i.String()),
		}
	case 6:
		op.e = op.i.load(sim)
		op.hasE = true
		op.pc++
		return ovStepResult{
			source:  ovSrc(156, 156, "for e := i.Load().(*ovEntry); e != nil; ..."),
			summary: fmt.Sprintf("loaded e from %s: %s", op.i.String(), ovNodeID(op.e)),
		}
	case 7:
		if op.e == nil {
			sim.unlock(threadID)
			op.result = "(value=0, loaded=false)"
			return ovStepResult{
				source:  ovSrc(156, 163, "for e := i.Load(); e != nil; ...; return *new(V), false"),
				summary: "scan reached nil without the key; LoadAndDelete returns loaded=false and unlocks",
				done:    true,
			}
		}
		op.pc++
		return ovStepResult{
			source:  ovSrc(156, 156, "e != nil"),
			summary: fmt.Sprintf("scan is visiting %s", ovNodeID(op.e)),
		}
	case 8:
		if op.e.Key == op.spec.key {
			op.pc = 13
			return ovStepResult{
				source:  ovSrc(157, 160, "if e.key == key { i.Store(e.overflow.Load()); return e.value, true }"),
				summary: fmt.Sprintf("found key %d in %s; delete it by rewiring %s", op.spec.key, op.e.ID, op.i.String()),
			}
		}
		op.pc++
		return ovStepResult{
			source:  ovSrc(157, 161, "if e.key == key { ... }; i = &e.overflow"),
			summary: fmt.Sprintf("%s holds key %d, not %d", ovNodeID(op.e), op.e.Key, op.spec.key),
		}
	case 9:
		op.i = ovOverflowSlot(op.e)
		op.pc = 6
		return ovStepResult{
			source:  ovSrc(161, 161, "i = &e.overflow"),
			summary: fmt.Sprintf("advanced predecessor slot to %s", op.i.String()),
		}
	case 11:
		before := sim.head
		sim.head = op.head.Overflow
		op.pc++
		return ovStepResult{
			source:  ovSrc(152, 152, "oc.head.Store(head.overflow.Load().(*ovEntry))"),
			summary: fmt.Sprintf("advanced head from %s to %s", ovNodeID(before), ovNodeID(sim.head)),
			impacts: sim.mutationImpacts(ovHeadSlot(), before, sim.head),
		}
	case 12:
		sim.unlock(threadID)
		op.result = fmt.Sprintf("(value=%d, loaded=true)", op.head.Value)
		return ovStepResult{
			source:  ovSrc(153, 153, "return head.value, true"),
			summary: fmt.Sprintf("LoadAndDelete returns value=%d, loaded=true and unlocks", op.head.Value),
			done:    true,
		}
	case 13:
		before := op.i.load(sim)
		after := op.e.Overflow
		op.i.store(sim, after)
		op.pc++
		return ovStepResult{
			source:  ovSrc(158, 158, "i.Store(e.overflow.Load().(*ovEntry))"),
			summary: fmt.Sprintf("rewired %s from %s to %s", op.i.String(), ovNodeID(before), ovNodeID(after)),
			impacts: sim.mutationImpacts(op.i, before, after),
		}
	default:
		sim.unlock(threadID)
		op.result = fmt.Sprintf("(value=%d, loaded=true)", op.e.Value)
		return ovStepResult{
			source:  ovSrc(159, 159, "return e.value, true"),
			summary: fmt.Sprintf("LoadAndDelete returns value=%d, loaded=true and unlocks", op.e.Value),
			done:    true,
		}
	}
}

func (sim *ovChainSimulator) stepDeleteWrapper(op *ovOpState) ovStepResult {
	op.execKind = "LoadAndDelete"
	op.pc = 0
	return ovStepResult{
		source:  ovSrc(167, 169, "func (oc *OvChain) Delete(key K) { _, _ = oc.LoadAndDelete(key) }"),
		summary: "Delete delegates to LoadAndDelete and discards the returned value",
	}
}

func (sim *ovChainSimulator) stepCompareAndDelete(threadID string, op *ovOpState) ovStepResult {
	switch op.pc {
	case 0:
		op.pc++
		return sim.initStep()
	case 1:
		if !sim.tryLock(threadID) {
			return ovStepResult{
				source:  ovSrc(174, 175, "oc.mu.Lock(); defer oc.mu.Unlock()"),
				summary: fmt.Sprintf("blocked on mu; %s currently holds it", sim.lockOwner),
				blocked: true,
			}
		}
		op.pc++
		return ovStepResult{
			source:  ovSrc(174, 175, "oc.mu.Lock(); defer oc.mu.Unlock()"),
			summary: "acquired mu for CompareAndDelete",
		}
	case 2:
		op.head = sim.head
		op.hasHead = true
		op.pc++
		return ovStepResult{
			source:  ovSrc(177, 177, "head := oc.head.Load().(*ovEntry)"),
			summary: fmt.Sprintf("captured head=%s", ovNodeID(op.head)),
		}
	case 3:
		if op.head == nil {
			sim.unlock(threadID)
			op.result = "false"
			return ovStepResult{
				source:  ovSrc(178, 180, "if head == nil { return false }"),
				summary: "head is nil; CompareAndDelete fails and unlocks",
				done:    true,
			}
		}
		op.pc++
		return ovStepResult{
			source:  ovSrc(178, 180, "if head == nil { ... }"),
			summary: "head is present; check whether the head entry matches",
		}
	case 4:
		if op.head.Key == op.spec.key && op.head.Value == op.spec.old {
			op.pc = 11
			return ovStepResult{
				source:  ovSrc(181, 183, "if head.key == key && head.value == old { ... }"),
				summary: fmt.Sprintf("head %s matches key=%d old=%d; delete it by advancing head", op.head.ID, op.spec.key, op.spec.old),
			}
		}
		op.hasI = true
		op.i = ovOverflowSlot(op.head)
		op.pc = 6
		return ovStepResult{
			source:  ovSrc(181, 185, "if head.key == key && head.value == old { ... }; i := &head.overflow"),
			summary: fmt.Sprintf("head does not match key=%d old=%d; scan from %s", op.spec.key, op.spec.old, op.i.String()),
		}
	case 6:
		op.e = op.i.load(sim)
		op.hasE = true
		op.pc++
		return ovStepResult{
			source:  ovSrc(186, 186, "for e := i.Load().(*ovEntry); e != nil; ..."),
			summary: fmt.Sprintf("loaded e from %s: %s", op.i.String(), ovNodeID(op.e)),
		}
	case 7:
		if op.e == nil {
			sim.unlock(threadID)
			op.result = "false"
			return ovStepResult{
				source:  ovSrc(186, 193, "for e := i.Load(); e != nil; ...; return false"),
				summary: "scan reached nil without a matching key/value pair; CompareAndDelete fails and unlocks",
				done:    true,
			}
		}
		op.pc++
		return ovStepResult{
			source:  ovSrc(186, 186, "e != nil"),
			summary: fmt.Sprintf("scan is visiting %s", ovNodeID(op.e)),
		}
	case 8:
		if op.e.Key == op.spec.key && op.e.Value == op.spec.old {
			op.pc = 13
			return ovStepResult{
				source:  ovSrc(187, 189, "if e.key == key && e.value == old { i.Store(...); return true }"),
				summary: fmt.Sprintf("found matching key/value pair in %s; delete it through %s", op.e.ID, op.i.String()),
			}
		}
		op.pc++
		return ovStepResult{
			source:  ovSrc(187, 191, "if e.key == key && e.value == old { ... }; i = &e.overflow"),
			summary: fmt.Sprintf("%s does not match key=%d old=%d", ovNodeID(op.e), op.spec.key, op.spec.old),
		}
	case 9:
		op.i = ovOverflowSlot(op.e)
		op.pc = 6
		return ovStepResult{
			source:  ovSrc(191, 191, "i = &e.overflow"),
			summary: fmt.Sprintf("advanced predecessor slot to %s", op.i.String()),
		}
	case 11:
		before := sim.head
		sim.head = op.head.Overflow
		op.pc++
		return ovStepResult{
			source:  ovSrc(182, 182, "oc.head.Store(head.overflow.Load().(*ovEntry))"),
			summary: fmt.Sprintf("advanced head from %s to %s", ovNodeID(before), ovNodeID(sim.head)),
			impacts: sim.mutationImpacts(ovHeadSlot(), before, sim.head),
		}
	case 12:
		sim.unlock(threadID)
		op.result = "true"
		return ovStepResult{
			source:  ovSrc(183, 183, "return true"),
			summary: "CompareAndDelete succeeded and unlocked",
			done:    true,
		}
	case 13:
		before := op.i.load(sim)
		after := op.e.Overflow
		op.i.store(sim, after)
		op.pc++
		return ovStepResult{
			source:  ovSrc(188, 188, "i.Store(e.overflow.Load().(*ovEntry))"),
			summary: fmt.Sprintf("rewired %s from %s to %s", op.i.String(), ovNodeID(before), ovNodeID(after)),
			impacts: sim.mutationImpacts(op.i, before, after),
		}
	default:
		sim.unlock(threadID)
		op.result = "true"
		return ovStepResult{
			source:  ovSrc(189, 189, "return true"),
			summary: "CompareAndDelete succeeded and unlocked",
			done:    true,
		}
	}
}

func (sim *ovChainSimulator) stepClear(threadID string, op *ovOpState) ovStepResult {
	switch op.pc {
	case 0:
		op.pc++
		return sim.initStep()
	case 1:
		if !sim.tryLock(threadID) {
			return ovStepResult{
				source:  ovSrc(226, 227, "oc.mu.Lock(); defer oc.mu.Unlock()"),
				summary: fmt.Sprintf("blocked on mu; %s currently holds it", sim.lockOwner),
				blocked: true,
			}
		}
		op.pc++
		return ovStepResult{
			source:  ovSrc(226, 227, "oc.mu.Lock(); defer oc.mu.Unlock()"),
			summary: "acquired mu for Clear",
		}
	default:
		before := sim.head
		sim.head = nil
		sim.unlock(threadID)
		op.result = "cleared"
		return ovStepResult{
			source:  ovSrc(228, 228, "oc.head.Store((*ovEntry)(nil))"),
			summary: "stored nil into head and unlocked",
			impacts: append(sim.mutationImpacts(ovHeadSlot(), before, sim.head), "the reachable chain is now empty"),
			done:    true,
		}
	}
}

func (sim *ovChainSimulator) stepAllOpen(threadID string, op *ovOpState) (ovStepResult, error) {
	switch op.pc {
	case 0:
		op.pc++
		return sim.initStep(), nil
	default:
		if _, exists := sim.iterators[op.iter]; exists {
			return ovStepResult{}, fmt.Errorf("thread %q reopened iterator name %q", threadID, op.iter)
		}
		sim.iterators[op.iter] = struct{}{}
		op.result = fmt.Sprintf("iterator=%s", op.iter)
		return ovStepResult{
			source:  ovSrc(197, 199, "func (oc *OvChain) All() func(yield func(K, V) bool) { return func(...) { ... } }"),
			summary: fmt.Sprintf("created iterator handle %q from All()", op.iter),
			done:    true,
		}, nil
	}
}

func (sim *ovChainSimulator) stepRange(op *ovOpState, allIterate bool) ovStepResult {
	if allIterate {
		if _, ok := sim.iterators[op.iter]; !ok {
			op.result = "invalid-iterator"
			return ovStepResult{
				source:  ovSrc(199, 206, "return func(yield func(K, V) bool) { ... }"),
				summary: fmt.Sprintf("iterator %q does not exist; AllIterate cannot proceed", op.iter),
				done:    true,
			}
		}
	}
	switch op.pc {
	case 0:
		if !allIterate {
			op.pc = 2
			return sim.initStep()
		}
		op.pc = 2
		return ovStepResult{
			source:  ovSrc(199, 199, "return func(yield func(K, V) bool) {"),
			summary: fmt.Sprintf("invoking iterator %q returned by All()", op.iter),
		}
	case 2:
		op.e = sim.head
		op.hasE = true
		op.pc++
		if allIterate {
			return ovStepResult{
				source:  ovSrc(200, 200, "e := oc.head.Load().(*ovEntry)"),
				summary: fmt.Sprintf("iterator %q loaded head into e: %s", op.iter, ovNodeID(op.e)),
			}
		}
		return ovStepResult{
			source:  ovSrc(214, 214, "e := oc.head.Load().(*ovEntry)"),
			summary: fmt.Sprintf("Range loaded head into e: %s", ovNodeID(op.e)),
		}
	case 3:
		if op.e == nil {
			if len(op.visitLog) == 0 {
				op.result = "visited=[]"
			} else {
				op.result = fmt.Sprintf("visited=[%s]", strings.Join(op.visitLog, ", "))
			}
			if allIterate {
				return ovStepResult{
					source:  ovSrc(201, 206, "for e != nil { ... }"),
					summary: fmt.Sprintf("iterator %q reached nil and returns", op.iter),
					done:    true,
				}
			}
			return ovStepResult{
				source:  ovSrc(215, 220, "for e != nil { ... }"),
				summary: "Range reached nil and returns",
				done:    true,
			}
		}
		op.pc++
		if allIterate {
			return ovStepResult{
				source:  ovSrc(201, 201, "for e != nil {"),
				summary: fmt.Sprintf("iterator %q is visiting %s", op.iter, ovNodeID(op.e)),
			}
		}
		return ovStepResult{
			source:  ovSrc(215, 215, "for e != nil {"),
			summary: fmt.Sprintf("Range is visiting %s", ovNodeID(op.e)),
		}
	case 4:
		keepGoing := true
		if op.yieldPos < len(op.spec.yield) {
			keepGoing = op.spec.yield[op.yieldPos]
		}
		op.lastYield = fmt.Sprintf("%t", keepGoing)
		op.visitLog = append(op.visitLog, fmt.Sprintf("%d:%d=>%t", op.e.Key, op.e.Value, keepGoing))
		op.yieldPos++
		if !keepGoing {
			op.result = fmt.Sprintf("visited=[%s]", strings.Join(op.visitLog, ", "))
			if allIterate {
				return ovStepResult{
					source:  ovSrc(202, 204, "if !yield(e.key, e.value) { return }"),
					summary: fmt.Sprintf("iterator %q callback returned false at %s; iteration stops", op.iter, ovNodeID(op.e)),
					done:    true,
				}
			}
			return ovStepResult{
				source:  ovSrc(216, 218, "if !yield(e.key, e.value) { return }"),
				summary: fmt.Sprintf("Range callback returned false at %s; iteration stops", ovNodeID(op.e)),
				done:    true,
			}
		}
		op.pc++
		if allIterate {
			return ovStepResult{
				source:  ovSrc(202, 204, "if !yield(e.key, e.value) { return }"),
				summary: fmt.Sprintf("iterator %q yielded (%d,%d) and the callback returned true", op.iter, op.e.Key, op.e.Value),
			}
		}
		return ovStepResult{
			source:  ovSrc(216, 218, "if !yield(e.key, e.value) { return }"),
			summary: fmt.Sprintf("Range yielded (%d,%d) and the callback returned true", op.e.Key, op.e.Value),
		}
	default:
		op.e = op.e.Overflow
		op.pc = 3
		if allIterate {
			return ovStepResult{
				source:  ovSrc(205, 205, "e = e.overflow.Load().(*ovEntry)"),
				summary: fmt.Sprintf("iterator %q advanced e to %s", op.iter, ovNodeID(op.e)),
			}
		}
		return ovStepResult{
			source:  ovSrc(219, 219, "e = e.overflow.Load().(*ovEntry)"),
			summary: fmt.Sprintf("Range advanced e to %s", ovNodeID(op.e)),
		}
	}
}

func (sim *ovChainSimulator) initStep() ovStepResult {
	if sim.initialized {
		return ovStepResult{
			source:  ovSrc(32, 36, "func (oc *OvChain) initOC() { oc.once.Do(func() { oc.head.Store(nil) }) }"),
			summary: "initOC is a no-op because the chain was already initialized",
		}
	}
	sim.initialized = true
	sim.head = nil
	return ovStepResult{
		source:  ovSrc(32, 36, "func (oc *OvChain) initOC() { oc.once.Do(func() { oc.head.Store(nil) }) }"),
		summary: "initOC ran once and stored nil into head",
	}
}

func (sim *ovChainSimulator) tryLock(threadID string) bool {
	if sim.lockOwner != "" {
		return false
	}
	sim.lockOwner = threadID
	return true
}

func (sim *ovChainSimulator) unlock(threadID string) {
	if sim.lockOwner == threadID {
		sim.lockOwner = ""
	}
}

func (sim *ovChainSimulator) newNode(key K, value V) *ovVisNode {
	sim.nextNodeID++
	return &ovVisNode{
		ID:    fmt.Sprintf("n%d", sim.nextNodeID),
		Key:   key,
		Value: value,
	}
}

func ovHeadSlot() ovSlotRef {
	return ovSlotRef{head: true}
}

func ovOverflowSlot(owner *ovVisNode) ovSlotRef {
	return ovSlotRef{owner: owner}
}

func (slot ovSlotRef) load(sim *ovChainSimulator) *ovVisNode {
	if slot.head {
		return sim.head
	}
	if slot.owner == nil {
		return nil
	}
	return slot.owner.Overflow
}

func (slot ovSlotRef) store(sim *ovChainSimulator, node *ovVisNode) {
	if slot.head {
		sim.head = node
		return
	}
	if slot.owner != nil {
		slot.owner.Overflow = node
	}
}

func (slot ovSlotRef) String() string {
	if slot.head {
		return "head"
	}
	if slot.owner == nil {
		return "<nil slot>"
	}
	return slot.owner.ID + ".overflow"
}

func (sim *ovChainSimulator) mutationImpacts(slot ovSlotRef, before, after *ovVisNode) []string {
	return []string{fmt.Sprintf("%s now points to %s instead of %s", slot.String(), ovNodeID(after), ovNodeID(before))}
}

func (sim *ovChainSimulator) detachedThreadImpacts(activeThread string, refs map[*ovVisNode][]string) []string {
	reachable := sim.reachableSet()
	var impacts []string
	seen := make(map[string]struct{})
	for node, labels := range refs {
		if node == nil || reachable[node] {
			continue
		}
		for _, label := range labels {
			if strings.HasPrefix(label, activeThread+":") {
				continue
			}
			msg := fmt.Sprintf("%s still holds detached %s", label, node.ID)
			if _, ok := seen[msg]; ok {
				continue
			}
			seen[msg] = struct{}{}
			impacts = append(impacts, msg)
		}
	}
	slices.Sort(impacts)
	return impacts
}

func (sim *ovChainSimulator) snapshots() []OvChainThreadSnapshot {
	out := make([]OvChainThreadSnapshot, 0, len(sim.threadOrder))
	for _, id := range sim.threadOrder {
		thread := sim.threads[id]
		snap := OvChainThreadSnapshot{
			ID:         id,
			LastResult: thread.lastResult,
		}
		switch {
		case thread.current == nil && thread.opIndex >= len(thread.plan.ops):
			snap.Status = "done"
		case thread.current == nil:
			snap.Status = "ready"
			next := thread.plan.ops[thread.opIndex]
			snap.Current = next.label
		case thread.blocked:
			snap.Status = "blocked"
			snap.Current = thread.current.spec.label
			snap.Locals = thread.current.locals()
		default:
			snap.Status = "running"
			snap.Current = thread.current.spec.label
			snap.Locals = thread.current.locals()
		}
		out = append(out, snap)
	}
	return out
}

func (thread *ovThreadState) currentLabel() string {
	if thread.current == nil {
		if thread.opIndex < len(thread.plan.ops) {
			return thread.plan.ops[thread.opIndex].label
		}
		return ""
	}
	return thread.current.spec.label
}

func (thread *ovThreadState) currentDisplayKind() string {
	if thread.current == nil {
		if thread.opIndex < len(thread.plan.ops) {
			return thread.plan.ops[thread.opIndex].displayKind
		}
		return ""
	}
	return thread.current.displayKind
}

func (op *ovOpState) locals() []string {
	var out []string
	if op.hasHead {
		out = append(out, fmt.Sprintf("head=%s", ovNodeID(op.head)))
	}
	if op.hasI {
		out = append(out, "i="+op.i.String())
	}
	if op.hasE {
		out = append(out, fmt.Sprintf("e=%s", ovNodeID(op.e)))
	}
	if op.hasNewE {
		out = append(out, fmt.Sprintf("newE=%s", ovNodeID(op.newE)))
	}
	if op.iter != "" {
		out = append(out, fmt.Sprintf("iter=%s", op.iter))
	}
	if op.yieldPos > 0 || op.lastYield != "" {
		out = append(out, fmt.Sprintf("yieldPos=%d", op.yieldPos))
	}
	if op.lastYield != "" {
		out = append(out, "lastYield="+op.lastYield)
	}
	if len(op.visitLog) > 0 {
		out = append(out, fmt.Sprintf("visited=%d", len(op.visitLog)))
	}
	return out
}

func (sim *ovChainSimulator) threadNodeRefs() map[*ovVisNode][]string {
	out := make(map[*ovVisNode][]string)
	for _, id := range sim.threadOrder {
		thread := sim.threads[id]
		if thread.current == nil {
			continue
		}
		for _, ref := range thread.current.nodeRefs(id) {
			out[ref.node] = append(out[ref.node], ref.label)
		}
	}
	for _, labels := range out {
		slices.Sort(labels)
	}
	return out
}

type ovNodeRef struct {
	node  *ovVisNode
	label string
}

func (op *ovOpState) nodeRefs(threadID string) []ovNodeRef {
	var refs []ovNodeRef
	if op.hasHead && op.head != nil {
		refs = append(refs, ovNodeRef{node: op.head, label: threadID + ":head"})
	}
	if op.hasE && op.e != nil {
		refs = append(refs, ovNodeRef{node: op.e, label: threadID + ":e"})
	}
	if op.hasNewE && op.newE != nil {
		refs = append(refs, ovNodeRef{node: op.newE, label: threadID + ":newE"})
	}
	return refs
}

func (sim *ovChainSimulator) reachableSet() map[*ovVisNode]bool {
	out := make(map[*ovVisNode]bool)
	for node := sim.head; node != nil && !out[node]; node = node.Overflow {
		out[node] = true
	}
	return out
}

func (sim *ovChainSimulator) renderReachableChain(refs map[*ovVisNode][]string) string {
	var parts []string
	seen := make(map[*ovVisNode]bool)
	for node := sim.head; node != nil && !seen[node]; node = node.Overflow {
		parts = append(parts, sim.renderNode(node, refs[node]))
		seen[node] = true
	}
	if len(parts) == 0 {
		return "head -> nil"
	}
	return "head -> " + strings.Join(parts, " -> ") + " -> nil"
}

func (sim *ovChainSimulator) renderDetachedChains(refs map[*ovVisNode][]string) []string {
	reachable := sim.reachableSet()
	roots := make(map[*ovVisNode]struct{})
	for node := range refs {
		if node == nil || reachable[node] {
			continue
		}
		parentDetached := false
		for other := range refs {
			if other == nil || other == node || reachable[other] {
				continue
			}
			for cur := other.Overflow; cur != nil && !reachable[cur]; cur = cur.Overflow {
				if cur == node {
					parentDetached = true
					break
				}
			}
			if parentDetached {
				break
			}
		}
		if !parentDetached {
			roots[node] = struct{}{}
		}
	}
	if len(roots) == 0 {
		return nil
	}
	var chains []string
	for root := range roots {
		var parts []string
		seen := make(map[*ovVisNode]bool)
		for node := root; node != nil && !seen[node]; node = node.Overflow {
			parts = append(parts, sim.renderNode(node, refs[node]))
			seen[node] = true
		}
		chains = append(chains, strings.Join(parts, " -> ")+" -> nil")
	}
	slices.Sort(chains)
	return chains
}

func (sim *ovChainSimulator) renderNode(node *ovVisNode, refs []string) string {
	if node == nil {
		return "nil"
	}
	if len(refs) == 0 {
		return fmt.Sprintf("%s(k=%d,v=%d)", node.ID, node.Key, node.Value)
	}
	return fmt.Sprintf("%s(k=%d,v=%d [%s])", node.ID, node.Key, node.Value, strings.Join(refs, ", "))
}

func ovNodeID(node *ovVisNode) string {
	if node == nil {
		return "nil"
	}
	return node.ID
}

func ovOpSummary(op ovCompiledOp) string {
	switch op.displayKind {
	case "Load":
		return fmt.Sprintf("Load(key=%d)", op.key)
	case "LoadOrStore":
		return fmt.Sprintf("LoadOrStore(key=%d, value=%d)", op.key, op.value)
	case "Store":
		return fmt.Sprintf("Store(key=%d, value=%d)", op.key, op.value)
	case "Swap":
		return fmt.Sprintf("Swap(key=%d, new=%d)", op.key, op.newValue)
	case "CompareAndSwap":
		return fmt.Sprintf("CompareAndSwap(key=%d, old=%d, new=%d)", op.key, op.old, op.newValue)
	case "LoadAndDelete":
		return fmt.Sprintf("LoadAndDelete(key=%d)", op.key)
	case "Delete":
		return fmt.Sprintf("Delete(key=%d)", op.key)
	case "CompareAndDelete":
		return fmt.Sprintf("CompareAndDelete(key=%d, old=%d)", op.key, op.old)
	case "Clear":
		return "Clear()"
	case "Range":
		return fmt.Sprintf("Range(yield=%v)", op.yield)
	case "AllOpen":
		return fmt.Sprintf("AllOpen(iter=%q)", op.iter)
	case "AllIterate":
		return fmt.Sprintf("AllIterate(iter=%q, yield=%v)", op.iter, op.yield)
	default:
		return op.displayKind
	}
}

func ovSrc(start, end int, snippet string) OvChainSourceRef {
	return OvChainSourceRef{Start: start, End: end, Snippet: snippet}
}
