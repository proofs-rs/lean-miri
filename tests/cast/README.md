# Typed cast component checks

Run from the repository root after building the library:

```bash
ELAN_HOME=$PWD/.elan .elan/bin/lake env lean MiriTests/Cast/Typed.lean
```

Kernel-checked examples exercise the actual `Cast.cast` dispatcher with fixture
type/layout queries and fallible callbacks. They check integer/float results,
layout and validity ordering, uninitialized scalar reads, capturing-closure
rejection, skipped transmute source validity and transmute size mismatch UB.

The types are component fixtures, not compiler-exported metadata. Unused dynamic
operations fail explicitly. These examples do not establish whole-program
safety or complete source equivalence. See [STATUS.md](../../STATUS.md) for
remaining work.
