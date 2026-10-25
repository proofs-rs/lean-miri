The comparison extracts the complete pinned `helpers.rs::gen_random` body,
checks its source-lock SHA256 before compilation, and changes only its Rust
signature/context adapter. RNG, host fill and memory writes are explicit
fixture leaves whose call/error traces are compared with the actual Lean
`RandomMemory.generate` driver. Six cases cover zero length (including null
pointer), isolated/host fill, host failure, and write failure after filling.

This validates outer driver ordering and preservation of leaf failures. It does
not compare physical memory/borrow checking, host randomness distributions,
compiler ABI dispatch, OS wrapper branches, or unrestricted Rust UB freedom.
