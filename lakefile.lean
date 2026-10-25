import Lake
open Lake DSL

package «lean-miri» where
  version := v!"0.1.0"

extern_lib nativeMathLgamma pkg := do
  let source := pkg.dir / "native" / "math_lgamma.c"
  let object := pkg.staticLibDir / "math_lgamma.o"
  let archive := pkg.staticLibDir / "liblean_miri_math_lgamma.a"
  let sourceJob ← inputTextFile source
  let lean ← getLeanInstall
  let objectJob ← buildO object sourceJob #["-I", lean.includeDir.toString]
    #["-fPIC"] (extraDepTrace := getLeanTrace)
  buildStaticLib archive #[objectJob]

@[default_target]
lean_lib Miri where
  roots := #[`Miri]

@[default_target]
lean_lib MiriTests where
  roots := #[`MiriTests]
  -- Runtime modules have independent mains; build them without importing them together.
  globs := #[.one `MiriTests, .submodules `MiriTests]

lean_exe miri_tests where
  root := `MiriTests.Run

lean_exe check_input where
  srcDir := "tools"
  root := `CheckInput

lean_exe native_runner where
  srcDir := "tools"
  root := `NativeRunner

-- QA-only native ABI check for actual libc math and the lgamma C shim.
lean_exe native_math_boundary_qa where
  srcDir := "tools"
  root := `NativeMathBoundaryQA

lean_exe native_windows_final where
  srcDir := "tools"
  root := `NativeWindowsFinal

lean_exe native_varying_choice125 where
  srcDir := "tools"
  root := `VaryingChoiceNative

-- Diagnostic only: structural hashing cost on a compact shared JSON DAG.
lean_exe profile_json_sharing where
  srcDir := "tools"
  root := `ProfileJsonSharing

-- Decode only, with the same native compiler as the full runner.
lean_exe profile_runtime_decoder where
  srcDir := "tools"
  root := `ProfileRuntimeDecoder

-- Finite cached/reference decoder parity against the native runtime.
lean_exe decoder_traversal_cache_tests where
  srcDir := "tests/input"
  root := `DecoderTraversalCache2026
