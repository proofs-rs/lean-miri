# Aggregate and repeat checks

Run from the repository root after the [README setup](../../README.md#prerequisites-and-setup):

```bash
ELAN_HOME=$PWD/.elan flock /tmp/lean-miri-lake-build.lock .elan/bin/lake build Miri.Interpreter.Aggregate
ELAN_HOME=$PWD/.elan .elan/bin/lake env lean --run MiriTests/Aggregate/Order.lean
ELAN_HOME=$PWD/.elan .elan/bin/lake env lean --run MiriTests/Aggregate/Memory.lean
```

`Order.lean` checks callback order against the pinned rustc
`compiler/rustc_const_eval/src/interpret/step.rs` methods `write_aggregate` and
`write_repeat`. Cases include aggregate variants, pointer metadata, failures,
and zero/one/multiple repeat lengths. `Memory.lean` checks copied bytes,
machine-hook order and failure-state retention through the concrete memory adapter.

Compiler queries, validation and machine policies are supplied through explicit
hooks. These focused component checks do not compare Rust program executions
or prove whole-program semantic equivalence.
