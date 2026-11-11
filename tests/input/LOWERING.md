# MIR lowering checks

Run from the repository root after the [README setup](../../README.md#build):

```bash
bash tests/input/run.sh
```

The script builds the pinned exporter and input modules, generates compiler
fixtures and runs the lowering checks alongside decoder and compiler-query tests.
It requires the pinned Miri sysroot; generated exports use temporary files.

| Test | Input and coverage |
| --- | --- |
| `LowerMIRTests.lean` | Compiler `add_one` export: arithmetic/assertions, source metadata and rejection of malformed fields or references |
| `CompactAllocationTests.lean` | Document-local byte sharing with distinct runtime identities, cyclic provenance, noncontiguous source salt results, TLS image bounds and malformed allocation-world evidence |
| `LowerMIRConstructorsTests.lean` | Wire fixtures decoded directly to all top-level MIR constructors and assembly operand forms; identity, generic constants and recursive call references |
| `LowerProgramTests.lean` | `mir_features.rs` and `mir_lowering.rs` exports: roots, instances, promoted bodies, shared tables and compiler metadata |
| `DefinitionLookup2026.lean` | Kernel theorem equating indexed lookup with list lookup, including duplicate and missing identities |

These are syntax-construction and metadata-preservation checks. Constructing a
MIR node does not establish execution readiness or operational equivalence;
synthetic constructor fixtures are not Rust programs.

Missing graph nodes, scalar widths and definition lookups are errors. Failed
compiler queries stop export. The decoder constructs interpreter MIR while
reading each body, retaining typed compiler facts for runtime queries. Program
bundles share definition and constant identities across bodies. Compiler pool
indices must not serve as runtime frame IDs.

Target-layout checks use compiler numeric queries and the official LLVM layout
string. Unsupported pointer widths produce errors. Typed constants retain their types, allocation
identities and pointer flags. Assertions in the tests define the exact finite
coverage and expected metadata.
