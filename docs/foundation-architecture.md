# Finite compiler material and Lean queries

The producer exports a finite document from one pinned rustc invocation: generic MIR bodies, raw definition identities, type and trait declarations, target facts, source metadata, startup data and allocation identities. It does not enumerate every substitution or compiler-query answer. Unsupported producer data aborts export.

The normal runner parses this document once into typed material. One evaluation-local `SourceCompilerWorld` owns canonical type, definition, instance, body and ABI identities. The fixed interpreter asks its compiler hooks for a fact when execution reaches that demand. Supported hooks derive the fact as a pure Lean function of the typed material and the current World; memoized results live only in that evaluation. Execution does not contact rustc or read a query-answer file.

## Concrete constants

For a syntactically observed constant with fully concrete generic arguments, the producing rustc evaluates the constant and exports an exact keyed result. Lean substitutes the caller's key and looks up that typed result only when the interpreter demands it. The implemented result domain is integer, bool, char, float and unit scalar values. Unobserved concrete substitutions, promoted constants and aggregate or pointer results remain Unsupported. There is no Lean CTFE implementation or enumeration of possible generic substitutions.

The result and rustc CTFE are trusted inputs. Before and after the producer evaluates concrete constants, it compares the complete allocation identity frontier, global map and dedup map. Any change rejects the whole document; a failed evaluation cannot leave a usable snapshot. This guards the current scalar domain, but does not establish an allocation or provenance transfer protocol for pointer results.

## Evidence and limits

A genuine no_std program using `<u64 as SizedTypeProperties>::SIZE` passes the normal runner through typed decode, demand-time lookup and the fixed interpreter to `finalized_exit` code 1. Removing the one compiler result stops at the actual demand with Unsupported. These are concrete execution checks, not proofs of all permitted executions.

Ordinary std main still lacks complete source coverage and execution. Bound function-pointer and outlives material, general enum layout, further ABI and physical types, and the examples proof closure are active work. The old schema-12 snapshot route remains available while migration continues; its precomputed answers do not fill missing finite-material queries. A Lean proof will need to pin the exact exported program and library revision, relate the typed input to that program, state initial and external assumptions, and cover every reachable permitted finite prefix of the fixed interpreter. Successful export or one run alone does not prove UB freedom.

Six alternating fixed-CPU trials of the same Rust program produced identical exits and complete choice tapes on frozen old-main/schema-12 and a foundation runner. Median wall time was 237.93 ms versus 267.55 ms; the ranges overlapped. Typed decode took 26.25 ms versus 62.07 ms at the median; lower, prepare and guest execution times were close. That measured foundation binary first tried the old decoder before dispatching to its own parser, adding a redundant document pass. The dispatch has since been corrected but not remeasured. The exact cost of the redundant pass has not been isolated. These are different payloads and binaries, and the measured foundation binary includes uncommitted work; artifact hashes and raw measurements are in ignored `scratch/constant-route-comparison/`. This does not establish a general runtime speedup or a same-input algorithm comparison.
