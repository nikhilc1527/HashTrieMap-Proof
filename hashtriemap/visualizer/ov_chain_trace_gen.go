package visualizer

import (
	"fmt"
	"math/rand"
	"slices"
	"strings"
	"time"
)

// OvChainRandomTraceOptions controls random trace generation.
type OvChainRandomTraceOptions struct {
	Seed              int64
	Title             string
	Threads           int
	OpsPerThread      int
	KeySpace          int
	ValueSpace        int
	MaxBurst          int
	MaxYieldDecisions int
	BlockedStepChance float64
}

// GenerateRandomOvChainTrace produces a valid OvChainTrace plus a compatible
// per-step schedule for a random interleaving.
func GenerateRandomOvChainTrace(opts OvChainRandomTraceOptions) (OvChainTrace, error) {
	opts = normalizeOvChainRandomTraceOptions(opts)
	if opts.Seed == 0 {
		opts.Seed = time.Now().UnixNano()
	}
	rng := rand.New(rand.NewSource(opts.Seed))

	threads, err := generateRandomOvChainThreads(rng, opts)
	if err != nil {
		return OvChainTrace{}, err
	}
	title := strings.TrimSpace(opts.Title)
	if title == "" {
		title = fmt.Sprintf("Random OvChain trace (seed=%d)", opts.Seed)
	}
	schedule, err := generateRandomOvChainSchedule(title, threads, rng, opts)
	if err != nil {
		return OvChainTrace{}, err
	}
	return OvChainTrace{
		Title:    title,
		Threads:  threads,
		Schedule: schedule,
	}, nil
}

func normalizeOvChainRandomTraceOptions(opts OvChainRandomTraceOptions) OvChainRandomTraceOptions {
	if opts.Threads <= 0 {
		opts.Threads = 3
	}
	if opts.OpsPerThread <= 0 {
		opts.OpsPerThread = 6
	}
	if opts.KeySpace <= 0 {
		opts.KeySpace = 6
	}
	if opts.ValueSpace <= 0 {
		opts.ValueSpace = 100
	}
	if opts.MaxBurst <= 0 {
		opts.MaxBurst = 4
	}
	if opts.MaxYieldDecisions <= 0 {
		opts.MaxYieldDecisions = 4
	}
	if opts.BlockedStepChance < 0 {
		opts.BlockedStepChance = 0
	}
	if opts.BlockedStepChance > 1 {
		opts.BlockedStepChance = 1
	}
	if opts.BlockedStepChance == 0 {
		opts.BlockedStepChance = 0.18
	}
	return opts
}

type ovRandomThreadBuilder struct {
	id       string
	ops      []OvChainTraceOp
	iterIDs  []string
	nextIter int
}

func generateRandomOvChainThreads(rng *rand.Rand, opts OvChainRandomTraceOptions) ([]OvChainTraceThread, error) {
	builders := make([]*ovRandomThreadBuilder, 0, opts.Threads)
	threads := make([]OvChainTraceThread, 0, opts.Threads)
	for i := 0; i < opts.Threads; i++ {
		id := fmt.Sprintf("t%d", i+1)
		builders = append(builders, &ovRandomThreadBuilder{id: id})
		threads = append(threads, OvChainTraceThread{ID: id})
	}

	shadow := make(map[int]int)
	total := opts.Threads * opts.OpsPerThread
	for generated := 0; generated < total; generated++ {
		builder := builders[randomBuilderWithCapacity(rng, builders, opts.OpsPerThread)]
		op := generateRandomOvChainOp(rng, builder, shadow, opts)
		builder.ops = append(builder.ops, op)
	}
	for i, builder := range builders {
		threads[i].Ops = builder.ops
	}
	return threads, nil
}

func randomBuilderWithCapacity(rng *rand.Rand, builders []*ovRandomThreadBuilder, maxOps int) int {
	available := make([]int, 0, len(builders))
	for i, builder := range builders {
		if len(builder.ops) < maxOps {
			available = append(available, i)
		}
	}
	return available[rng.Intn(len(available))]
}

func generateRandomOvChainOp(rng *rand.Rand, builder *ovRandomThreadBuilder, shadow map[int]int, opts OvChainRandomTraceOptions) OvChainTraceOp {
	kind := pickRandomOvChainOpKind(rng, builder, shadow)
	label := fmt.Sprintf("%s-%02d", ovRandomOpLabel(kind), len(builder.ops)+1)

	switch kind {
	case "Load":
		key := ovTraceRandomKey(rng, shadow, opts.KeySpace, 0.65)
		return OvChainTraceOp{Label: label, Op: kind, Key: ovIntPtr(key)}
	case "LoadOrStore":
		key := ovTraceRandomKey(rng, shadow, opts.KeySpace, 0.40)
		value := ovTraceRandomValue(rng, opts.ValueSpace)
		if _, ok := shadow[key]; !ok {
			shadow[key] = value
		}
		return OvChainTraceOp{Label: label, Op: kind, Key: ovIntPtr(key), Value: ovIntPtr(value)}
	case "Store":
		key := ovTraceRandomKey(rng, shadow, opts.KeySpace, 0.55)
		value := ovTraceRandomValue(rng, opts.ValueSpace)
		shadow[key] = value
		return OvChainTraceOp{Label: label, Op: kind, Key: ovIntPtr(key), Value: ovIntPtr(value)}
	case "Swap":
		key := ovTraceRandomKey(rng, shadow, opts.KeySpace, 0.60)
		newValue := ovTraceRandomValue(rng, opts.ValueSpace)
		shadow[key] = newValue
		return OvChainTraceOp{Label: label, Op: kind, Key: ovIntPtr(key), New: ovIntPtr(newValue)}
	case "CompareAndSwap":
		key := ovTraceRandomKey(rng, shadow, opts.KeySpace, 0.75)
		newValue := ovTraceRandomValue(rng, opts.ValueSpace)
		oldValue := ovTraceRandomCASValue(rng, shadow, key, opts.ValueSpace)
		if current, ok := shadow[key]; ok && current == oldValue {
			shadow[key] = newValue
		}
		return OvChainTraceOp{Label: label, Op: kind, Key: ovIntPtr(key), Old: ovIntPtr(oldValue), New: ovIntPtr(newValue)}
	case "LoadAndDelete":
		key := ovTraceRandomKey(rng, shadow, opts.KeySpace, 0.70)
		delete(shadow, key)
		return OvChainTraceOp{Label: label, Op: kind, Key: ovIntPtr(key)}
	case "Delete":
		key := ovTraceRandomKey(rng, shadow, opts.KeySpace, 0.70)
		delete(shadow, key)
		return OvChainTraceOp{Label: label, Op: kind, Key: ovIntPtr(key)}
	case "CompareAndDelete":
		key := ovTraceRandomKey(rng, shadow, opts.KeySpace, 0.75)
		oldValue := ovTraceRandomCASValue(rng, shadow, key, opts.ValueSpace)
		if current, ok := shadow[key]; ok && current == oldValue {
			delete(shadow, key)
		}
		return OvChainTraceOp{Label: label, Op: kind, Key: ovIntPtr(key), Old: ovIntPtr(oldValue)}
	case "Clear":
		for key := range shadow {
			delete(shadow, key)
		}
		return OvChainTraceOp{Label: label, Op: kind}
	case "Range":
		return OvChainTraceOp{Label: label, Op: kind, Yield: randomOvYieldPlan(rng, opts.MaxYieldDecisions)}
	case "AllOpen":
		builder.nextIter++
		iter := fmt.Sprintf("%s_it_%d", builder.id, builder.nextIter)
		builder.iterIDs = append(builder.iterIDs, iter)
		return OvChainTraceOp{Label: label, Op: kind, Iter: iter}
	case "AllIterate":
		iter := builder.iterIDs[rng.Intn(len(builder.iterIDs))]
		return OvChainTraceOp{Label: label, Op: kind, Iter: iter, Yield: randomOvYieldPlan(rng, opts.MaxYieldDecisions)}
	default:
		panic("unreachable random op kind")
	}
}

func pickRandomOvChainOpKind(rng *rand.Rand, builder *ovRandomThreadBuilder, shadow map[int]int) string {
	weighted := []string{
		"Load", "Load",
		"LoadOrStore", "LoadOrStore",
		"Store", "Store",
		"Swap", "Swap",
		"Range",
		"AllOpen",
	}
	if len(shadow) == 0 {
		weighted = append(weighted, "LoadOrStore", "Store", "Swap")
	} else {
		weighted = append(weighted,
			"CompareAndSwap", "CompareAndSwap",
			"LoadAndDelete", "Delete",
			"CompareAndDelete", "CompareAndDelete",
			"Clear",
		)
	}
	if len(builder.iterIDs) > 0 {
		weighted = append(weighted, "AllIterate", "AllIterate")
	}
	return weighted[rng.Intn(len(weighted))]
}

func ovTraceRandomKey(rng *rand.Rand, shadow map[int]int, keySpace int, preferExisting float64) int {
	if len(shadow) > 0 && rng.Float64() < preferExisting {
		keys := make([]int, 0, len(shadow))
		for key := range shadow {
			keys = append(keys, key)
		}
		slices.Sort(keys)
		return keys[rng.Intn(len(keys))]
	}
	return rng.Intn(keySpace)
}

func ovTraceRandomValue(rng *rand.Rand, valueSpace int) int {
	return rng.Intn(valueSpace)
}

func ovTraceRandomCASValue(rng *rand.Rand, shadow map[int]int, key int, valueSpace int) int {
	if current, ok := shadow[key]; ok && rng.Float64() < 0.72 {
		return current
	}
	value := ovTraceRandomValue(rng, valueSpace)
	if current, ok := shadow[key]; ok {
		for value == current && valueSpace > 1 {
			value = ovTraceRandomValue(rng, valueSpace)
		}
	}
	return value
}

func randomOvYieldPlan(rng *rand.Rand, max int) []bool {
	n := 1 + rng.Intn(max)
	yield := make([]bool, n)
	for i := range yield {
		yield[i] = true
	}
	if rng.Float64() < 0.45 {
		yield[n-1] = false
	}
	return yield
}

func ovRandomOpLabel(kind string) string {
	switch kind {
	case "Load":
		return "load"
	case "LoadOrStore":
		return "los"
	case "Store":
		return "store"
	case "Swap":
		return "swap"
	case "CompareAndSwap":
		return "cas"
	case "LoadAndDelete":
		return "lad"
	case "Delete":
		return "del"
	case "CompareAndDelete":
		return "cad"
	case "Clear":
		return "clear"
	case "Range":
		return "range"
	case "AllOpen":
		return "allopen"
	case "AllIterate":
		return "allcall"
	default:
		return "op"
	}
}

func generateRandomOvChainSchedule(title string, threads []OvChainTraceThread, rng *rand.Rand, opts OvChainRandomTraceOptions) ([]OvChainScheduleEntry, error) {
	compiled, _, err := compileOvChainThreads(title, threads)
	if err != nil {
		return nil, err
	}
	sim := newOvChainSimulator(compiled)

	raw := make([]string, 0, opts.Threads*opts.OpsPerThread*8)
	lastThread := ""
	burst := 0
	for !sim.allThreadsDone() {
		runnable, blocked, err := sim.scheduleChoices()
		if err != nil {
			return nil, err
		}
		var choices []string
		switch {
		case len(runnable) == 0:
			choices = blocked
		case len(blocked) > 0 && rng.Float64() < opts.BlockedStepChance:
			choices = blocked
		default:
			choices = runnable
		}
		threadID := pickRandomScheduledThread(rng, choices, lastThread, burst, opts.MaxBurst)
		raw = append(raw, threadID)

		thread := sim.threads[threadID]
		step, err := sim.stepThread(threadID, thread)
		if err != nil {
			return nil, err
		}
		sim.applyThreadStep(thread, step)

		if threadID == lastThread {
			burst++
		} else {
			lastThread = threadID
			burst = 1
		}
	}
	return compressOvChainSchedule(raw), nil
}

func (sim *ovChainSimulator) allThreadsDone() bool {
	for _, thread := range sim.threads {
		if thread.current != nil || thread.opIndex < len(thread.plan.ops) {
			return false
		}
	}
	return true
}

func (sim *ovChainSimulator) scheduleChoices() ([]string, []string, error) {
	var runnable []string
	var blocked []string
	for _, threadID := range sim.threadOrder {
		thread := sim.threads[threadID]
		if thread == nil {
			continue
		}
		if thread.current == nil && thread.opIndex >= len(thread.plan.ops) {
			continue
		}
		if err := thread.ensureCurrent(); err != nil {
			return nil, nil, err
		}
		if sim.nextStepWouldBlock(threadID, thread) {
			blocked = append(blocked, threadID)
		} else {
			runnable = append(runnable, threadID)
		}
	}
	return runnable, blocked, nil
}

func (sim *ovChainSimulator) nextStepWouldBlock(threadID string, thread *ovThreadState) bool {
	if thread.current == nil {
		return false
	}
	if !ovExecKindUsesLock(thread.current.execKind) {
		return false
	}
	return thread.current.pc == 1 && sim.lockOwner != "" && sim.lockOwner != threadID
}

func ovExecKindUsesLock(execKind string) bool {
	switch execKind {
	case "LoadOrStore", "Swap", "CompareAndSwap", "LoadAndDelete", "CompareAndDelete", "Clear":
		return true
	default:
		return false
	}
}

func pickRandomScheduledThread(rng *rand.Rand, choices []string, last string, burst, maxBurst int) string {
	if len(choices) == 1 {
		return choices[0]
	}
	if last != "" && burst < maxBurst {
		for _, choice := range choices {
			if choice == last && rng.Float64() < 0.55 {
				return choice
			}
		}
	}
	return choices[rng.Intn(len(choices))]
}

func compressOvChainSchedule(raw []string) []OvChainScheduleEntry {
	if len(raw) == 0 {
		return nil
	}
	out := make([]OvChainScheduleEntry, 0, len(raw))
	current := raw[0]
	count := 1
	for i := 1; i < len(raw); i++ {
		if raw[i] == current {
			count++
			continue
		}
		entry := OvChainScheduleEntry{Thread: current}
		if count > 1 {
			entry.Count = count
		}
		out = append(out, entry)
		current = raw[i]
		count = 1
	}
	entry := OvChainScheduleEntry{Thread: current}
	if count > 1 {
		entry.Count = count
	}
	out = append(out, entry)
	return out
}

func ovIntPtr(v int) *int {
	return &v
}
