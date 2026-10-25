import NativeRunner

/-! Run the precompiled harness without elaborating its implementation
on every invocation. Build `+NativeRunner:olean` before `lean --run` on this
file. The imported `main` retains all readiness, execution and finalization checks.
-/
