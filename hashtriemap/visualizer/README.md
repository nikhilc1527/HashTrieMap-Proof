# OvChain Visualizer

**all visualization code is written by ChatGPT**

This package is the visualization and trace-generation layer for `hashtriemap.OvChain`.
It is intentionally separate from the core data-structure package in `hashtriemap/`.

The visualizer does not instrument the live data structure at runtime.
Instead, it simulates `OvChain` using the exact control flow in `hashtriemap/ov_chain.go` and records one semantic step per scheduled tick.

That gives you:

- deterministic replay
- explicit interleavings
- stale-reader visibility
- detached-chain visualization
- source-line attribution for every step

## Package Layout

- `ov_chain_trace.go`
  Source-faithful simulator and trace model.
- `ov_chain_trace_gen.go`
  Random trace generator plus schedule synthesis.
- `ov_chain_visualizer.go`
  Existing table/timeline HTML renderer.
- `ov_chain_visualizer_graph.go`
  Animated graph renderer with nodes, arrows, and thread-reference overlays.
- `cmd/ovchaingen`
  CLI for generating random traces.
- `cmd/ovchainviz`
  CLI for rendering traces as HTML or dumping the expanded simulated run as JSON.
- `testdata/ovchainviz/stale_reader_swap.json`
  Small hand-authored example trace.

## What Is Being Simulated

The simulator follows the semantics of `hashtriemap/ov_chain.go` exactly:

- `Load` is lock-free and walks the current chain through `head` and `overflow`.
- mutators take the single `mu` lock
- `LoadOrStore` inserts at the head
- `Swap` and `CompareAndSwap` replace nodes rather than mutating them in place
- `LoadAndDelete` and `CompareAndDelete` splice nodes out of the chain
- `Range` and `All` read through the chain visible to the caller when each step occurs

The point is not to approximate concurrency.
The point is to let you describe an interleaving precisely and then see what each thread still holds or observes.

## Trace Model

A trace has three parts:

1. `title`
2. `threads`
3. `schedule`

Each thread has an ordered list of public `OvChain` operations.
The schedule chooses which thread advances on each semantic tick.

### Supported Operations

- `Load`
- `LoadOrStore`
- `Store`
- `Swap`
- `CompareAndSwap`
- `LoadAndDelete`
- `Delete`
- `CompareAndDelete`
- `Clear`
- `Range`
- `AllOpen`
- `AllIterate`

`AllOpen` represents calling `All()` and storing the returned closure name in `iter`.
`AllIterate` represents invoking that stored iterator.

### Example Trace

```json
{
  "title": "Reader holds the old head across Swap",
  "threads": [
    {
      "id": "writer",
      "ops": [
        { "label": "seed", "op": "LoadOrStore", "key": 1, "value": 10 },
        { "label": "replace-head", "op": "Swap", "key": 1, "new": 20 }
      ]
    },
    {
      "id": "reader",
      "ops": [
        { "label": "stale-load", "op": "Load", "key": 1 }
      ]
    }
  ],
  "schedule": [
    { "thread": "writer", "count": 7 },
    { "thread": "reader", "count": 2 },
    { "thread": "writer", "count": 9 },
    { "thread": "reader", "count": 2 }
  ]
}
```

### Important Detail About `schedule`

`count` is the number of semantic simulator steps, not the number of API calls.

For example, one `Swap` may expand into:

- `initOC`
- lock acquisition
- head load
- branch on head
- allocate replacement node
- copy overflow pointer
- publish replacement
- unlock
- return

So if you want the writer to reach the publish step before the reader resumes, the schedule has to reflect that exact step count.

If you do not want to hand-author those counts, use the generator CLI or library API and let it synthesize a valid schedule for you.

## Renderers

### 1. Table Renderer

`RenderOvChainTraceHTML` emits the original timeline/table view.

It is good for:

- reading source-line references
- scanning lane state
- inspecting locals like `head`, `e`, `i`, and `newE`
- auditing exact step order

### 2. Animated Graph Renderer

`RenderOvChainTraceGraphHTML` emits the newer diagram-based view.

It shows:

- thread cards on the left
- reachable chain across the top
- detached chains below
- node cards with key/value payloads
- overflow arrows
- dashed arrows from thread state to referenced nodes
- play/pause/step controls

This renderer is self-contained HTML plus inline JS and SVG.
It does not require any network access or external JS libraries.

## CLI Usage

Run these from the module root:

`/home/haddr/go_sync_proof/hashtriemap`

### Generate a Random Trace

```bash
env GOCACHE=/tmp/go-build-hashtriemap \
go run ./visualizer/cmd/ovchaingen \
  -seed 123 \
  -threads 4 \
  -ops 6 \
  -keys 6 \
  -values 100 \
  -out /tmp/ovchain_trace.json
```

Generator flags:

- `-seed`
  Fixed seed for reproducibility. `0` uses current time.
- `-threads`
  Number of concurrent thread lanes.
- `-ops`
  Operations per thread.
- `-keys`
  Key-space size used by the generator.
- `-values`
  Generated value range `[0, values)`.
- `-max-burst`
  Preferred maximum run length for one thread before switching.
- `-max-yield`
  Maximum explicit yield decisions for `Range` and `AllIterate`.
- `-blocked-chance`
  Probability that the synthesized schedule emits a blocked lock-attempt step when one is available.
- `-title`
  Optional trace title override.

### Render the Table View

```bash
env GOCACHE=/tmp/go-build-hashtriemap \
go run ./visualizer/cmd/ovchainviz \
  -in ./visualizer/testdata/ovchainviz/stale_reader_swap.json \
  -format html \
  -out /tmp/ovchain_table.html
```

### Render the Animated Graph View

```bash
env GOCACHE=/tmp/go-build-hashtriemap \
go run ./visualizer/cmd/ovchainviz \
  -in ./visualizer/testdata/ovchainviz/stale_reader_swap.json \
  -format graph-html \
  -out /tmp/ovchain_graph.html
```

`animated-html` is accepted as an alias for `graph-html`.

### Dump the Expanded Simulated Run

```bash
env GOCACHE=/tmp/go-build-hashtriemap \
go run ./visualizer/cmd/ovchainviz \
  -in ./visualizer/testdata/ovchainviz/stale_reader_swap.json \
  -format json \
  > /tmp/ovchain_expanded.json
```

This is useful if you want to post-process the event stream yourself.

### Pipe Generator Directly Into Renderer

```bash
env GOCACHE=/tmp/go-build-hashtriemap \
go run ./visualizer/cmd/ovchaingen -seed 42 -threads 3 -ops 5 \
| env GOCACHE=/tmp/go-build-hashtriemap \
  go run ./visualizer/cmd/ovchainviz -format graph-html \
  -out /tmp/ovchain_random.html
```

## Library Usage

### Simulate Only

```go
import "hashtriemap/visualizer"

result, err := visualizer.SimulateOvChainTrace(trace)
```

### Render the Table View

```go
html, err := visualizer.RenderOvChainTraceHTML(trace)
```

### Render the Animated Graph View

```go
html, err := visualizer.RenderOvChainTraceGraphHTML(trace)
```

### Generate a Random Trace

```go
trace, err := visualizer.GenerateRandomOvChainTrace(visualizer.OvChainRandomTraceOptions{
    Seed:         123,
    Threads:      4,
    OpsPerThread: 6,
    KeySpace:     6,
    ValueSpace:   100,
})
```

## What the Generator Actually Does

The random generator is not just making up a thread list.

It works in two phases:

1. Build random per-thread operation streams.
2. Dry-run the same simulator used by the renderers and randomly choose the next runnable thread on each semantic step.

That means the emitted `schedule` is already valid for the exact internal step expansion used by the simulator.

It also means:

- lock-blocked steps can appear explicitly
- schedules are deterministic for a fixed seed
- you do not have to compute semantic step counts by hand

## Reading the Outputs

### Reachable Chain

This is the chain currently reachable from `head`.

### Detached Chains

These are chains or nodes no longer reachable from `head` but still referenced by one or more thread-local variables such as `head`, `e`, or `newE`.

Detached chains are the key to understanding stale-reader behavior.

### Thread Locals

The simulator tracks locals that matter to `ov_chain.go` semantics:

- `head`
- `e`
- `i`
- `newE`
- iterator handles and yield state when relevant

### Impact Notes

Impact notes summarize what just changed in a way that matters to another thread.
Examples:

- `head now points to n2 instead of n1`
- `reader:e still holds detached n1`

## Limitations

- The visualizer is specialized to `OvChain`, not the full `HashTrieMap`.
- The trace model currently assumes `K` and `V` are integer-valued, matching the current package aliases.
- This is a semantic simulator, not a recorder for arbitrary live goroutine execution.
- The graph renderer is intentionally 2D SVG rather than a 3D engine so it stays local, deterministic, and dependency-free.

## Testing

From the module root:

```bash
env GOCACHE=/tmp/go-build-hashtriemap go test ./...
```

The tests cover:

- stale readers after head replacement
- stale readers after delete splicing
- `Range` stopping early
- deterministic random generation
- renderer smoke tests for both HTML views

## Other Ideas

- Add a trace importer that consumes logs from a custom instrumented `OvChain` wrapper.
- Emit GIF or MP4 snapshots from the animated renderer.
- Add a “diff mode” that highlights only the nodes and pointers changed between adjacent frames.
- Add a per-thread filter so one viewer can focus on a subset of lanes.
- Add a “proof mode” that shows preconditions and postconditions for each semantic step.
- Extend the same simulator/rendering framework to the full `HashTrieMap`.
- Add a compact textual DSL for traces in addition to JSON.
- Add a timeline scrubber that jumps directly to steps touching a specific key.
