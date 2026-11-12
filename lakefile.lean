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

-- Standard-stream host adapter, built by the same pinned compiler as the exporter.
extern_lib nativeStdioHost pkg := do
  let source := pkg.dir / "native" / "stdio_host.rs"
  let shim := pkg.dir / "native" / "stdio_host.c"
  let object := pkg.staticLibDir / "stdio_host.o"
  let archive := pkg.staticLibDir / "liblean_miri_stdio_host.a"
  let sourceJob ← inputTextFile source
  let shimJob ← inputTextFile shim
  let lean ← getLeanInstall
  let objectJob ← buildO object shimJob #["-I", lean.includeDir.toString]
    #["-fPIC"] (extraDepTrace := getLeanTrace)
  let deps := Job.collectArray #[sourceJob,objectJob]
  buildFileAfterDep archive deps fun files => do
    let source := files[0]!
    let object := files[1]!
    let rustc := pkg.dir / ".rustup" / "toolchains" / "miri-exporter-8144389c895d" / "bin" / "rustc"
    let version ← IO.Process.output {cmd := rustc.toString, args := #["-vV"]}
    unless version.exitCode == 0 && (version.stdout.splitOn "commit-hash: 8144389c895da997dbdecaa635e41d6a50be6ffd\n").length == 2 do
      error "native stdio requires the pinned exporter rustc commit"
    proc {cmd := rustc.toString, args := #["--edition=2024", "--crate-type=staticlib",
      "-C", "opt-level=2", "-C", "relocation-model=pic", source.toString, "-o", archive.toString]}
    proc {cmd := "ar", args := #["rcs", archive.toString, object.toString]}

lean_lib NativeRunnerSupport where
  srcDir := "tools"
  roots := #[`NativeStdioHost, `NativeStdioProtocol]

lean_exe native_stdio_host_qa where
  srcDir := "native"
  root := `StdioHostQA

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

-- Decode only, with the same native compiler as the full runner.
lean_exe profile_runtime_decoder where
  srcDir := "tools"
  root := `ProfileRuntimeDecoder

lean_exe typed_function_abi_tests where
  srcDir := "tests/input"
  root := `TypedFunctionAbiTests
