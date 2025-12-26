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
- Adapted: `sync/hashtriemap/hashtriemap.go`

## Current Changes from Upstream
- Package and imports: `package sync` → `package stdsync`; removed `internal/abi`, `internal/goarch`; added `sync`.
- Generics removed: `HashTrieMap[K,V]`, `indirect[K,V]`, `entry[K,V]`, `node[K,V]` are monomorphic; `type K = int`, `type V = int`.
- Hashing/equality: replaced runtime/ABI map hasher and element equality with a local `hashInt` and direct `==` comparisons; removed `valEqual` and `runtime_rand`; seed is `uint64` and set to `0`.
- Pointer arithmetic: `hashShift` uses `uint(hashBits)` (`hashBits = 64`) instead of `8*goarch.PtrSize`.
- Comparison APIs: `CompareAndSwap`/`CompareAndDelete` no longer check for comparability; they rely on direct equality.
- Range over children: `for j := range i.children` → `for j := range i.children[:]` (Goose only supports ranges over slices/maps).
- Atomic pointers removed: `atomic.Pointer[...]` replaced with `atomic.Value` for root, children, and overflow; typed nils are stored to initialize values.
- Node header changed: `unsafe` header casts removed; header uses explicit entry/indirect pointers.

## Goose/Rocq Constraints
- No generics (including `atomic.Pointer[T]`).
- `range` only supported over slices and maps.
- Method name `init` can be treated specially and may need renaming if Goose skips it.  
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
A small Go test exists at `sync/stdsync/hashtriemap_test.go` to sanity-check
basic behavior and concurrent usage, to make sure that the adapted implementation
of HashTrieMap matches with the source material.
```sh
cd sync
go test hashtriemap/hashtriemap
```
