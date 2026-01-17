# go HashTrieMap proof

This repository is a proof-oriented adaptation of Go's internal `sync` HashTrieMap
implementation. The code is adjusted to fit Goose and Rocq (Coq) tooling constraints
so that the map can be translated and verified.

## Goals
- Provide a mechanically verifiable version of Go's HashTrieMap.
- Keep the implementation as close as possible to upstream semantics.
- Track and document all deviations from the upstream source.
- Generate Goose and Rocq artifacts for proof development.

## Source of Truth
- Upstream: `https://github.com/golang/go/blob/master/src/internal/sync/hashtriemap.go`
- Adapted: `hashtriemap/hashtriemap/hashtriemap.go`

## Current Changes from Upstream
- Package and imports: `package sync` → `package hashtriemap`; removed `internal/abi`, `internal/goarch`; added `sync`.
- Generics removed: `HashTrieMap[K,V]`, `indirect[K,V]`, `entry[K,V]`, `node[K,V]` are monomorphic; `type K = int`, `type V = int`.
- Hashing/equality + map plumbing: replaced runtime/ABI map hasher and element equality with a local `hashInt` and direct `==` comparisons.
  - Removed `valEqual`, `hashFunc`/`equalFunc` types, `abi.NoEscape`/`unsafe.Pointer` helpers, `abi.TypeOf(map).MapType()` derivation, and `runtime_rand`.
  - `seed` is `uint64` and set to `0`.
- Pointer arithmetic: `hashShift` uses `uint(hashBits)` (`hashBits = 64`) instead of `8*goarch.PtrSize`.
- Comparison APIs: `CompareAndSwap`/`CompareAndDelete` no longer check for comparability; they rely on direct equality.
- HashTrieMap fields changed: removed `keyHash` and `valEqual`.
  - `seed` is `uint64`; `root` is `atomic.Value`.
  - `init` renamed to `initHT` and all call sites updated (no `//go:noinline`).
- Atomic pointers and layout: `atomic.Pointer[...]` replaced with `atomic.Value` for root, children, and overflow.
  - Children array became a slice with explicit initialization.
  - `atomic.Value` loads now require explicit type assertions throughout.
- Node header changed: `unsafe` header casts removed; node representation changed from embedded headers to explicit `node` pointers with `ent`/`ind` fields.
- find/compare path: `find` uses `checkValue bool` instead of an `equalFunc`; `lookupWithValue` uses direct `==` gated by that flag.
- Panic text: `expand` panic message shortened (removed the "incorrect use of unsafe or cgo..." suffix).
- Minor name-only diff: `Store` parameter renamed (`new` → `old`).

## Goose/Rocq Constraints
- No generics.
  - Includes `atomic.Pointer[T]`.
- `range` only supported over slices and maps.
- Method name `init` can be treated specially and may need renaming
- No use of `internal/*` packages (`internal/abi`, `internal/goarch`) in translated code.
- No `unsafe`/`abi.NoEscape` helpers for hashing/equality.
- No `//go:linkname` (e.g., to `runtime.rand`).
These limitations are the reason for the differences between the implementation of HashTrieMap in this repository and the original HashTrieMap from the go stdlib source code.

## Generated Artifacts
- Goose output: `src/code`
- Generated proofs: `src/generatedproof`
- Proof setup: `src/proof`

## Workflow
Build proofs:
   ```sh
   make
   ```
relies on having perennial-cli installed

## Tests
A small Go test exists at `hashtriemap/hashtriemap/hashtriemap_test.go` to sanity-check
basic behavior and concurrent usage, to make sure that the adapted implementation
of HashTrieMap matches with the source material.
```sh
cd hashtriemap
go test ./hashtriemap
```

## References

+ [https://link.springer.com/chapter/10.1007/978-3-662-44202-9_9](https://link.springer.com/chapter/10.1007/978-3-662-44202-9_9)
