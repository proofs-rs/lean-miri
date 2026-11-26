import Lake
open Lake DSL
open System (FilePath)

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
-- A general target avoids package-global extern_lib dependencies: pure Miri,
-- documentation and proof clients do not require Rust. Only runner support links it.
target nativeStdioHost pkg : System.FilePath := do
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
    let rustc := pkg.dir / ".rustup" / "toolchains" / "miri-exporter-8eb778d04094" / "bin" / "rustc"
    let version ← IO.Process.output {cmd := rustc.toString, args := #["-vV"]}
    unless version.exitCode == 0 && (version.stdout.splitOn "commit-hash: 8eb778d04094d3af4b26580cab327e0413eb1e02\n").length == 2 do
      error "native stdio requires the pinned exporter rustc commit"
    proc {cmd := rustc.toString, args := #["--edition=2024", "--crate-type=staticlib",
      "-C", "opt-level=2", "-C", "relocation-model=pic", source.toString, "-o", archive.toString]}
    proc {cmd := "ar", args := #["rcs", archive.toString, object.toString]}

lean_lib NativeRunnerSupport where
  srcDir := "tools"
  roots := #[`NativeStdioHost, `NativeStdioProtocol]
  moreLinkObjs := #[⟨.packageTarget .anonymous `nativeStdioHost⟩]

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

lean_exe profile_retag_lookup where
  srcDir := "tools"
  root := `ProfileRetagLookup

lean_exe source_abi_boundary_tests where
  srcDir := "tests/input"
  root := `SourceAbiBoundaryTests

lean_exe coroutine_native_queries where
  srcDir := "tests/input"
  root := `CoroutineNativeQueries

lean_exe profile_allocation_storage where
  srcDir := "tools"
  root := `StorageMicro

/-!
Opt-in Rust pipeline. `lake build` does not build these targets.
The shell scripts in `tools/` call the scripts below, which build these targets.
-/
namespace Pipeline

open Lake DSL System IO IO.FS

def pinnedRustcCommit : String := "8eb778d04094d3af4b26580cab327e0413eb1e02"
def exporterToolchain : String := "miri-exporter-8eb778d04094"
def toolchainInstallerVersion : String := "1.12.1"

def lakeDir (root : FilePath) : FilePath :=
  root / "scratch" / "lake"

def stampPath (root : FilePath) (name : String) : FilePath :=
  lakeDir root / "stamps" / name

def miriSysroot (root : FilePath) : FilePath :=
  lakeDir root / "miri-sysroot"

def miriTargetDir (root : FilePath) : FilePath :=
  lakeDir root / "miri-target"

def exporterBin (root : FilePath) : FilePath :=
  root / "exporter" / "target" / "release" / "lean-miri-mir-exporter"

def miriReferenceExporterBin (root : FilePath) : FilePath :=
  lakeDir root / "exporter-miri-reference" / "release" / "lean-miri-mir-exporter"

structure RustTools where
  cargo : FilePath
  rustup : FilePath
  cargoHome : FilePath
  rustupHome : FilePath

def unwords (args : List String) : String :=
  args.foldl (fun acc arg => if acc.isEmpty then arg else s!"{acc} {arg}") ""

def commandLine (args : IO.Process.SpawnArgs) : String :=
  unwords (args.cmd :: args.args.toList)

def textField (text key : String) : Option String :=
  let head := key ++ ": "
  text.splitOn "\n" |>.findSome? fun line =>
    match line.trimAscii.toString.dropPrefix? head with
    | some rest => some rest.trimAscii.toString
    | none => none

def stringTrace (caption value : String) : BuildTrace :=
  .ofHash (pureHash value) s!"{caption}: {value}"

def skipGeneratedDir (dir : FilePath) : IO Bool := do
  let name := dir.fileName.getD ""
  return name != "target" && name != ".git" && name != ".lake"

/-- Hash the files under `root`, skipping generated directories. One trace, not one job per file. -/
def inputTree (root : FilePath) : SpawnM (Job Unit) :=
  Job.async (caption := s!"inputs {root}") do
    if !(← System.FilePath.pathExists root) then
      error s!"input directory does not exist: {root}"
    else
      let paths ← root.walkDir skipGeneratedDir
      let files ← paths.filterM fun path => return !(← System.FilePath.isDir path)
      let files := files.qsort (·.toString < ·.toString)
      let mut hash := Hash.nil
      for file in files do
        hash := Hash.mix hash (Hash.ofString file.toString)
        hash := Hash.mix hash (← computeHash file)
      hash := Hash.mix hash (Hash.ofNat files.size)
      addTrace (BuildTrace.ofHash hash s!"{root} ({files.size} files)")

def inputOne (path : FilePath) : SpawnM (Job Unit) := do
  let file ← inputBinFile path
  file.mapM fun _ => pure ()

def toolEnv (tools : RustTools) (extra : Array (String × Option String) := #[]) :
    Array (String × Option String) :=
  #[("CARGO_HOME", some tools.cargoHome.toString),
    ("RUSTUP_HOME", some tools.rustupHome.toString)] ++ extra

def joinColon (parts : List String) : String :=
  parts.foldl (fun acc part => if acc.isEmpty then part else s!"{acc}:{part}") ""

def prependEnv (var : String) (front : List FilePath) : IO (String × Option String) := do
  let inherited ← IO.getEnv var
  let parts := front.map (·.toString) ++ match inherited with
    | some value => [value]
    | none => []
  return (var, some (joinColon parts))

def prependPath (front : List FilePath) : IO (String × Option String) :=
  prependEnv "PATH" front

def spawnInherit (args : IO.Process.SpawnArgs) : IO UInt32 := do
  IO.Process.spawn {
    args with
    stdin := .null
    stdout := .inherit
    stderr := .inherit
  } >>= (·.wait)

def runStreaming (args : IO.Process.SpawnArgs) : JobM Unit := do
  logInfo s!"{args.cwd.getD "."}> {commandLine args}"
  let code ← spawnInherit args
  if code != 0 then
    error s!"external command '{args.cmd}' exited with code {code}"

def writeStamp (path : FilePath) (contents : String) : IO Unit := do
  if let some parent := path.parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile path contents

def findOnPath (name : String) : IO (Option FilePath) := do
  let some path ← IO.getEnv "PATH" | return none
  for dir in path.splitOn ":" do
    if dir.isEmpty then
      continue
    let candidate := FilePath.mk dir / name
    if (← System.FilePath.pathExists candidate) && !(← System.FilePath.isDir candidate) then
      return some candidate
  return none

def cargoHomeOf (cargo : FilePath) : IO FilePath := do
  match cargo.parent with
  | some bin =>
    if bin.fileName == some "bin" then
      match bin.parent with
      | some home => return home
      | none => throw <| IO.userError s!"cargo has no home directory: {cargo}"
    else
      defaultHome
  | none => defaultHome
where
  defaultHome : IO FilePath := do
    let some home ← IO.getEnv "HOME"
      | throw <| IO.userError "HOME is unset; cannot locate the cargo home"
    return FilePath.mk home / ".cargo"

def rustupHomeOf (rustup cargoHome : FilePath) : IO FilePath := do
  let out ← IO.Process.output {
    cmd := rustup.toString
    args := #["show", "home"]
    env := #[("RUSTUP_HOME", none), ("CARGO_HOME", some cargoHome.toString)]
  }
  if out.exitCode == 0 then
    let home := out.stdout.trimAscii.toString
    if !home.isEmpty then
      return FilePath.mk home
  let some home ← IO.getEnv "HOME"
    | throw <| IO.userError "HOME is unset; cannot locate the rustup home"
  return FilePath.mk home / ".rustup"

/-- Checkout `.cargo` and `.rustup` win, then `LEAN_MIRI_*`, then `PATH`. -/
def selectRustTools (root : FilePath) : IO RustTools := do
  let checkoutCargo := root / ".cargo" / "bin" / "cargo"
  let checkoutRustup := root / ".cargo" / "bin" / "rustup"
  let checkoutRustupHome := root / ".rustup"
  if (← System.FilePath.pathExists checkoutCargo) && (← System.FilePath.pathExists checkoutRustupHome) then
    if !(← System.FilePath.pathExists checkoutRustup) then
      throw <| IO.userError s!"rustup is missing next to {checkoutCargo}"
    return {
      cargo := checkoutCargo
      rustup := checkoutRustup
      cargoHome := root / ".cargo"
      rustupHome := checkoutRustupHome
    }
  match (← IO.getEnv "LEAN_MIRI_CARGO_HOME", ← IO.getEnv "LEAN_MIRI_RUSTUP_HOME") with
  | (some cargoHome, some rustupHome) =>
    let cargo := FilePath.mk cargoHome / "bin" / "cargo"
    let rustup := FilePath.mk cargoHome / "bin" / "rustup"
    if !(← System.FilePath.pathExists cargo) || !(← System.FilePath.pathExists rustup) then
      throw <| IO.userError s!"LEAN_MIRI_CARGO_HOME does not contain bin/cargo and bin/rustup: {cargoHome}"
    return {
      cargo
      rustup
      cargoHome := FilePath.mk cargoHome
      rustupHome := FilePath.mk rustupHome
    }
  | _ =>
    let some cargo ← findOnPath "cargo"
      | throw <| IO.userError s!"rustup and cargo were not found under {root}/.cargo/bin or on PATH"
    let some rustup ← findOnPath "rustup"
      | throw <| IO.userError s!"rustup and cargo were not found under {root}/.cargo/bin or on PATH"
    let cargoHome ← cargoHomeOf cargo
    let rustupHome ← rustupHomeOf rustup cargoHome
    return { cargo, rustup, cargoHome, rustupHome }

def hasMiddleRmeta (dir : FilePath) : IO Bool := do
  if !(← System.FilePath.pathExists dir) then
    return false
  for entry in (← System.FilePath.readDir dir) do
    let name := entry.fileName
    if name.startsWith "librustc_middle-" && name.endsWith ".rmeta" then
      return true
  return false

def componentsPresent (sysroot host : String) : IO Bool := do
  let rustlib := FilePath.mk sysroot / "lib" / "rustlib"
  let library := rustlib / "src" / "rust" / "library" / "Cargo.toml"
  let compiler := rustlib / "rustc-src" / "rust" / "compiler" / "rustc" / "Cargo.toml"
  let profdata := rustlib / host / "bin" / "llvm-profdata"
  if !(← System.FilePath.pathExists library) then return false
  if !(← System.FilePath.pathExists compiler) then return false
  if !(← System.FilePath.pathExists profdata) then return false
  hasMiddleRmeta (rustlib / host / "lib")

def readPin (root : FilePath) : IO String := do
  let text ← IO.FS.readFile (root / "upstream" / "miri-source" / "rust-version")
  return text.trimAscii.toString

def requirePin (root : FilePath) : IO String := do
  let pin ← readPin root
  if pin != pinnedRustcCommit then
    throw <| IO.userError s!"Miri rust-version does not match the exporter-pinned compiler commit: {pin}"
  return pin

def rustcVerbose (tools : RustTools) (root : FilePath) : IO (Option String) := do
  let out ← IO.Process.output {
    cmd := tools.rustup.toString
    args := #["run", exporterToolchain, "rustc", "--version", "--verbose"]
    cwd := some root
    env := toolEnv tools
  }
  if out.exitCode != 0 then
    return none
  return some out.stdout

def toolchainSysroot (tools : RustTools) (root : FilePath) : IO String := do
  let out ← IO.Process.output {
    cmd := tools.rustup.toString
    args := #["run", exporterToolchain, "rustc", "--print", "sysroot"]
    cwd := some root
    env := toolEnv tools
  }
  if out.exitCode != 0 then
    throw <| IO.userError s!"rustc --print sysroot failed:\n{out.stderr}"
  return out.stdout.trimAscii.toString

/-- Environment for the pinned rustc: its `bin` and `lib` precede the inherited paths. -/
def sysrootEnv (tools : RustTools) (root : FilePath)
    (extra : Array (String × Option String) := #[]) :
    IO (String × Array (String × Option String)) := do
  let sysroot ← toolchainSysroot tools root
  let pathEntry ← prependPath [FilePath.mk sysroot / "bin", tools.cargoHome / "bin"]
  let ldEntry ← prependEnv "LD_LIBRARY_PATH" [FilePath.mk sysroot / "lib"]
  return (sysroot, toolEnv tools (#[pathEntry, ldEntry] ++ extra))

def cargoFetchLocked (cargo manifest : FilePath) (root : FilePath)
    (env : Array (String × Option String)) (leadingArgs : Array String := #[]) : JobM Unit := do
  runStreaming {
    cmd := cargo.toString
    args := leadingArgs ++ #["fetch", "--locked", "--manifest-path", manifest.toString]
    cwd := some root
    env
  }

def toolchainHelperVersion (cmd : FilePath) (tools : RustTools) (root : FilePath) : IO (Option String) := do
  let pathEntry ← prependPath [tools.cargoHome / "bin"]
  let out ← IO.Process.output {
    cmd := cmd.toString
    args := #["--version"]
    cwd := some root
    env := toolEnv tools #[pathEntry]
  }
  if out.exitCode != 0 then
    return none
  let line := out.stdout.trimAscii.toString
  let rest := match line.dropPrefix? "rustup-toolchain-install-master " with
    | some rest => rest
    | none => line.toSlice
  return some rest.trimAscii.toString

def ensureToolchainHelper (tools : RustTools) (root : FilePath) : JobM FilePath := do
  let installed := tools.cargoHome / "bin" / "rustup-toolchain-install-master"
  let existing ← if ← System.FilePath.pathExists installed then
    pure (some installed)
  else
    findOnPath "rustup-toolchain-install-master"
  if let some cmd := existing then
    if (← toolchainHelperVersion cmd tools root) == some toolchainInstallerVersion then
      return cmd
  let pathEntry ← prependPath [tools.cargoHome / "bin"]
  logInfo s!"Installing pinned Miri CI toolchain helper {toolchainInstallerVersion} with stable Cargo"
  runStreaming {
    cmd := tools.cargo.toString
    args := #["+stable", "install", "--locked", "--force", "--version",
      toolchainInstallerVersion, "rustup-toolchain-install-master"]
    cwd := some root
    env := toolEnv tools #[pathEntry]
  }
  unless ← System.FilePath.pathExists installed do
    error s!"toolchain helper was not installed at {installed}"
  return installed

def installRustToolchain (root : FilePath) (stamp : FilePath) : JobM Unit := do
  let pin ← requirePin root
  let tools ← selectRustTools root
  if let some verbose ← rustcVerbose tools root then
    let commit := textField verbose "commit-hash"
    let host := textField verbose "host"
    let sysroot ← toolchainSysroot tools root
    let ready := commit == some pin &&
      (← match host with
        | some host => componentsPresent sysroot host
        | none => pure false)
    if ready then
      logInfo s!"{exporterToolchain} already has rustc-dev and rust-src at {pin}"
      writeStamp stamp s!"{pin}\n"
      return
    if commit.isSome then
      logInfo s!"Removing mismatched exporter toolchain {exporterToolchain}"
      runStreaming {
        cmd := tools.rustup.toString
        args := #["toolchain", "uninstall", exporterToolchain]
        cwd := some root
        env := toolEnv tools
      }
  let helper ← ensureToolchainHelper tools root
  let pathEntry ← prependPath [tools.cargoHome / "bin"]
  logInfo s!"Installing {exporterToolchain} at {pinnedRustcCommit}"
  runStreaming {
    cmd := helper.toString
    args := #[
      "--name", exporterToolchain,
      "--component", "cargo",
      "--component", "rust-src",
      "--component", "rustc-dev",
      "--component", "llvm-tools",
      "--component", "clippy",
      "--component", "rustfmt",
      "--", pinnedRustcCommit]
    cwd := some root
    env := toolEnv tools #[pathEntry]
  }
  let some verbose ← rustcVerbose tools root
    | error s!"Installed rustc for {exporterToolchain} did not run"
  if textField verbose "commit-hash" != some pin then
    error s!"Installed rustc commit mismatch: expected {pin}"
  let some host := textField verbose "host"
    | error "Installed rustc did not report a host"
  let sysroot ← toolchainSysroot tools root
  if !(← componentsPresent sysroot host) then
    error "Pinned toolchain is missing rustc-dev, rust-src, or llvm-tools payloads"
  logInfo s!"Installed {exporterToolchain} with rustc-dev and rust-src at {pin}"
  writeStamp stamp s!"{pin}\n"

def requireCachedCrates (root lock cache : FilePath) (tools : RustTools) : JobM Unit := do
  runStreaming {
    cmd := "python3"
    args := #[
      (root / "tools" / "require_cached_crates.py").toString,
      lock.toString, cache.toString]
    cwd := some root
    env := toolEnv tools
  }

def vendorLock (root lock cargo : FilePath) (tools : RustTools)
    (env : Array (String × Option String)) : JobM Unit := do
  -- Populate the cargo cache online, then refuse to vendor anything still missing.
  -- `vendor_pinned_crates.py` can download on its own; this path does not use that.
  let some parent := lock.parent
    | error s!"Cargo.lock has no directory: {lock}"
  cargoFetchLocked cargo (parent / "Cargo.toml") root env
  let cache := tools.cargoHome / "registry" / "cache"
  requireCachedCrates root lock cache tools
  runStreaming {
    cmd := "python3"
    args := #[
      (root / "tools" / "vendor_pinned_crates.py").toString,
      "--lock", lock.toString,
      "--destination", (lakeDir root / "miri-vendor").toString,
      "--cargo-cache", cache.toString]
    cwd := some root
    env := toolEnv tools
  }

def bashSingleQuote (value : String) : String :=
  "'" ++ value.replace "'" "'\\''" ++ "'"

def buildMiriReference (root : FilePath) (stamp : FilePath) : JobM Unit := do
  let pin ← requirePin root
  let tools ← selectRustTools root
  let (sysroot, env) ← sysrootEnv tools root
    #[("CARGO_TARGET_DIR", some (miriTargetDir root).toString)]
  let verbose ← captureProc {
    cmd := s!"{sysroot}/bin/rustc"
    args := #["-vV"]
    cwd := some root
    env
  }
  if textField verbose "commit-hash" != some pin then
    error "The reference Miri build requires the exact pinned rustc-dev toolchain."
  let cargo := FilePath.mk sysroot / "bin" / "cargo"
  let locks := #[
    root / "upstream" / "miri-source" / "Cargo.lock",
    root / "upstream" / "miri-source" / "cargo-miri" / "Cargo.lock",
    FilePath.mk sysroot / "lib" / "rustlib" / "src" / "rust" / "library" / "Cargo.lock"]
  for lock in locks do
    vendorLock root lock cargo tools env
  let config := lakeDir root / "cargo-vendor.toml"
  let cargoOffline (args : Array String) : JobM Unit :=
    runStreaming {
      cmd := cargo.toString
      args := #["--config", config.toString] ++ args
      cwd := some root
      env
    }
  let miriManifest := root / "upstream" / "miri-source" / "Cargo.toml"
  cargoOffline #[
    "build", "--offline", "--locked",
    "--manifest-path", miriManifest.toString,
    "--bin", "miri"]
  cargoOffline #[
    "test", "--offline", "--locked",
    "--manifest-path", miriManifest.toString,
    "--lib"]
  cargoOffline #[
    "build", "--offline", "--locked",
    "--manifest-path", (root / "upstream" / "miri-source" / "cargo-miri" / "Cargo.toml").toString]
  let miriBin := miriTargetDir root / "debug" / "miri"
  let cargoMiri := miriTargetDir root / "debug" / "cargo-miri"
  unless (← System.FilePath.pathExists miriBin) do
    error s!"Miri binary was not produced: {miriBin}"
  unless (← System.FilePath.pathExists cargoMiri) do
    error s!"cargo-miri binary was not produced: {cargoMiri}"
  let wrapper := lakeDir root / "cargo-offline.sh"
  writeStamp wrapper <|
    "#!/usr/bin/env bash\n" ++
    "set -euo pipefail\n" ++
    s!"exec {bashSingleQuote cargo.toString} \\\n" ++
    s!"  --config {bashSingleQuote config.toString} \"$@\"\n"
  runStreaming {
    cmd := "chmod"
    args := #["+x", wrapper.toString]
    cwd := some root
  }
  let sysrootOut := miriSysroot root
  runStreaming {
    cmd := cargoMiri.toString
    args := #["miri", "setup"]
    cwd := some root
    env := env ++ #[
      ("CARGO", some wrapper.toString),
      ("CARGO_NET_OFFLINE", some "true"),
      ("MIRI", some miriBin.toString),
      ("MIRI_SYSROOT", some sysrootOut.toString)]
  }
  let hash ← captureProc { cmd := "sha256sum", args := #[miriBin.toString], cwd := some root }
  let digest := hash.splitOn " " |>.head?
  let some digest := digest
    | error s!"sha256sum returned no hash for {miriBin}"
  writeStamp (lakeDir root / "miri-reference-build.json") <|
    "{\n" ++
    s!"  \"rustc_commit\": \"{pin}\",\n" ++
    "  \"cargo_feature_args\": [],\n" ++
    s!"  \"binary_sha256\": \"{digest}\"\n" ++
    "}\n"
  logInfo s!"Reference Miri sysroot: {sysrootOut}"
  writeStamp stamp s!"{pin} default-features\n"

def buildExporter (root targetDir : FilePath) (featureArgs : Array String) : JobM Unit := do
  let tools ← selectRustTools root
  if let some parent := targetDir.parent then
    IO.FS.createDirAll parent
  runStreaming {
    cmd := tools.cargo.toString
    args := #[s!"+{exporterToolchain}", "build", "--release", "--locked", "--offline",
      "--manifest-path", (root / "exporter" / "Cargo.toml").toString] ++ featureArgs
    cwd := some root
    env := toolEnv tools #[("CARGO_TARGET_DIR", some targetDir.toString)]
  }

def fetchExporterCrates (root : FilePath) : JobM Unit := do
  let tools ← selectRustTools root
  cargoFetchLocked tools.cargo (root / "exporter" / "Cargo.toml") root (toolEnv tools)
    #[s!"+{exporterToolchain}"]

def runSourceAudit (root : FilePath) (stamp : FilePath) : JobM Unit := do
  let tools ← selectRustTools root
  cargoFetchLocked tools.cargo (root / "tools" / "source-analysis" / "Cargo.toml") root
    (toolEnv tools)
  runStreaming {
    cmd := "python3"
    args := #[(root / "tools" / "prepare-source-audit.py").toString]
    cwd := some root
    env := toolEnv tools
  }
  runStreaming {
    cmd := "python3"
    args := #[(root / "tools" / "coverage.py").toString, "check",
      "--root", (root / "scratch" / "source-audit").toString]
    cwd := some root
    env := toolEnv tools
  }
  writeStamp stamp "source-audit\n"

structure InterpretArgs where
  source : String
  output : Option String
  crateName : Option String
  roots : Array String
  seed : Option String
  profile : Bool
  noRun : Bool
  rustcArgs : Array String

def interpretUsage : String :=
  "usage: lake run interpret -- SOURCE.rs [--output FILE] [--crate-name NAME] [--root DEF-PATH]... [--seed U64] [--profile] [--no-run] [-- RUSTC-ARG...]"

inductive Cli where
  | help
  | ok (args : InterpretArgs)
  | error (message : String)

structure PartialArgs where
  source : Option String := none
  output : Option String := none
  crateName : Option String := none
  roots : Array String := #[]
  seed : Option String := none
  profile : Bool := false
  noRun : Bool := false
  rustcArgs : Array String := #[]

def checkSeed (raw : String) : Except String Unit := do
  if raw.isEmpty || !raw.toList.all (·.isDigit) then
    throw "--seed expects an unsigned decimal u64"
  let some value := raw.toNat?
    | throw "--seed expects an unsigned decimal u64"
  if value >= 2 ^ 64 then
    throw "--seed is outside the u64 range"

def parseInterpret (args : List String) : Cli :=
  -- `lake run` forwards a leading `--` into the script. Accept it so
  -- `lake run interpret -- SOURCE.rs` and `lake run interpret SOURCE.rs` both work.
  let args := match args with
    | "--" :: rest => rest
    | other => other
  go args {} false
where
  go (args : List String) (acc : PartialArgs) (rustc : Bool) : Cli :=
    if rustc then
      finish { acc with rustcArgs := acc.rustcArgs ++ args.toArray }
    else
      match args with
      | [] => finish acc
      | "--" :: rest => go rest acc true
      | "--help" :: _ | "-h" :: _ => .help
      | "--profile" :: rest => go rest { acc with profile := true } false
      | "--output" :: path :: rest => go rest { acc with output := some path } false
      | "--output" :: [] => .error s!"--output requires a path\n{interpretUsage}"
      | "--crate-name" :: name :: rest => go rest { acc with crateName := some name } false
      | "--crate-name" :: [] => .error s!"--crate-name requires a name\n{interpretUsage}"
      | "--root" :: path :: rest =>
        go rest { acc with roots := acc.roots.push path } false
      | "--root" :: [] => .error s!"--root requires a def-path\n{interpretUsage}"
      | "--no-run" :: rest => go rest { acc with noRun := true } false
      | "--seed" :: raw :: rest =>
        match checkSeed raw with
        | .ok () => go rest { acc with seed := some raw } false
        | .error message => .error s!"{message}\n{interpretUsage}"
      | "--seed" :: [] => .error s!"--seed requires an unsigned decimal u64\n{interpretUsage}"
      | flag :: rest =>
        if flag.startsWith "--" then
          .error s!"unknown option {flag}\n{interpretUsage}"
        else if acc.source.isSome then
          .error s!"expected one Rust source\n{interpretUsage}"
        else
          go rest { acc with source := some flag } false
  finish (acc : PartialArgs) : Cli :=
    match acc.source with
    | none => .error s!"missing Rust source\n{interpretUsage}"
    | some source => .ok {
        source
        output := acc.output
        crateName := acc.crateName
        roots := acc.roots
        seed := acc.seed
        profile := acc.profile
        noRun := acc.noRun
        rustcArgs := acc.rustcArgs
      }

#guard match parseInterpret ["scratch/example.rs"] with
  | .ok args => args.source == "scratch/example.rs" && args.output.isNone && !args.profile
  | _ => false

#guard match parseInterpret ["--", "scratch/example.rs", "--", "--edition", "2024"] with
  | .ok args => args.source == "scratch/example.rs" && args.rustcArgs == #["--edition", "2024"]
  | _ => false

#guard match parseInterpret ["--", "--help"] with
  | .help => true
  | _ => false

#guard match parseInterpret ["--seed", "3", "a.rs", "--profile", "--output", "out.json",
    "--crate-name", "demo", "--root", "add_one", "--no-run", "--", "--edition", "2024"] with
  | .ok args =>
    args.source == "a.rs" && args.seed == some "3" && args.profile && args.noRun &&
      args.output == some "out.json" && args.crateName == some "demo" &&
      args.roots == #["add_one"] && args.rustcArgs == #["--edition", "2024"]
  | _ => false

#guard match parseInterpret ["--seed", "18446744073709551615", "a.rs"] with
  | .ok args => args.seed == some "18446744073709551615"
  | _ => false

#guard match parseInterpret ["--seed", "18446744073709551616", "a.rs"] with
  | .error _ => true
  | _ => false

#guard match parseInterpret ["--help"] with
  | .help => true
  | _ => false

#guard match parseInterpret [] with
  | .error _ => true
  | _ => false

#guard match parseInterpret ["a.rs", "b.rs"] with
  | .error _ => true
  | _ => false

end Pipeline

open Pipeline

target rustToolchain pkg : FilePath := do
  let pin ← inputBinFile (pkg.dir / "upstream" / "miri-source" / "rust-version")
  let stamp := stampPath pkg.dir "rust-toolchain"
  buildFileAfterDep stamp pin
    (extraDepTrace := pure (stringTrace "commit" pinnedRustcCommit))
    (text := true) fun _ =>
    installRustToolchain pkg.dir stamp

target exporterFetch pkg : FilePath := do
  let toolchain ← rustToolchain.fetch
  let manifest ← inputOne (pkg.dir / "exporter" / "Cargo.toml")
  let lock ← inputOne (pkg.dir / "exporter" / "Cargo.lock")
  let stamp := stampPath pkg.dir "exporter-fetch"
  buildFileAfterDep stamp ((toolchain.mix manifest).mix lock) (text := true) fun _ => do
    fetchExporterCrates pkg.dir
    writeStamp stamp s!"fetched {pinnedRustcCommit}\n"

def exporterJob (root targetDir : FilePath) (featureArgs : Array String) (label : String)
    (bin : FilePath) : FetchM (Job FilePath) := do
  let fetched ← exporterFetch.fetch
  let sources ← inputTree (root / "exporter")
  let dep := fetched.mix sources
  buildFileAfterDep bin dep
    (extraDepTrace := pure (stringTrace "features" label)) fun _ => do
    buildExporter root targetDir featureArgs
    unless ← System.FilePath.pathExists bin do
      error s!"exporter binary was not produced: {bin}"

target exporter pkg : FilePath :=
  exporterJob pkg.dir (pkg.dir / "exporter" / "target") #[] "default" (exporterBin pkg.dir)

target exporterMiriReference pkg : FilePath :=
  exporterJob pkg.dir (lakeDir pkg.dir / "exporter-miri-reference")
    #["--features", "miri-reference"] "miri-reference" (miriReferenceExporterBin pkg.dir)

target miriReference pkg : FilePath := do
  let toolchain ← rustToolchain.fetch
  let sources ← inputTree (pkg.dir / "upstream" / "miri-source")
  let vendor ← inputOne (pkg.dir / "tools" / "vendor_pinned_crates.py")
  let cacheCheck ← inputOne (pkg.dir / "tools" / "require_cached_crates.py")
  let stamp := stampPath pkg.dir "miri-reference"
  buildFileAfterDep stamp ((toolchain.mix sources).mix (vendor.mix cacheCheck))
    (extraDepTrace := pure (stringTrace "features" "default"))
    (text := true) fun _ =>
    buildMiriReference pkg.dir stamp

target sourceAudit pkg : FilePath := do
  let mut jobs : List (Job Unit) := []
  for path in #[
      pkg.dir / "Miri", pkg.dir / "MiriTests", pkg.dir / "tests", pkg.dir / "exporter",
      pkg.dir / "native", pkg.dir / "third_party", pkg.dir / "upstream" / "miri-source",
      pkg.dir / "upstream" / "rustc-source", pkg.dir / "tools" / "source-analysis",
      pkg.dir / "tools" / "audit"] do
    jobs := (← inputTree path) :: jobs
  for path in #[
      pkg.dir / "Miri.lean", pkg.dir / "MiriTests.lean",
      pkg.dir / "tools" / "prepare-source-audit.py", pkg.dir / "tools" / "coverage.py",
      pkg.dir / "tools" / "update_features.py",
      pkg.dir / "tools" / "update_implementation_ledger.py",
      pkg.dir / "tools" / "check_implementation_ledger.py"] do
    jobs := (← inputOne path) :: jobs
  let stamp := stampPath pkg.dir "source-audit"
  buildFileAfterDep stamp (Job.mixList jobs) (text := true) fun _ =>
    runSourceAudit pkg.dir stamp

/-- Export a Rust program and run it on `native_runner`. Builds the pinned toolchain, exporter, and Miri sysroot first. -/
script interpret (args) do
  match parseInterpret args with
  | .help =>
    IO.println interpretUsage
    return 0
  | .error message =>
    IO.eprintln message
    return 64
  | .ok parsed =>
    let ws ← getWorkspace
    let root := ws.root.dir
    let cwd ← IO.currentDir
    let sourceFile := FilePath.mk parsed.source
    let sourcePath := if sourceFile.isRelative then cwd / sourceFile else sourceFile
    if !(← System.FilePath.pathExists sourcePath) then
      IO.eprintln s!"Rust source does not exist: {sourcePath}"
      return 1
    let sourceAbs ← IO.FS.realPath sourcePath
    let stem := sourceAbs.fileStem.getD "input"
    let crateName := parsed.crateName.getD stem
    let output := match parsed.output with
      | some path =>
        let outputFile := FilePath.mk path
        if outputFile.isRelative then cwd / outputFile else outputFile
      | none => root / "scratch" / s!"{stem}.json"
    if let some parent := output.parent then
      IO.FS.createDirAll parent
    let runner? ← runBuild do
      let exporterJob ← exporter.fetch
      let miriJob ← miriReference.fetch
      if parsed.noRun then
        return (exporterJob.mix miriJob).map fun _ => (none : Option FilePath)
      else
        let runnerJob ← native_runner.fetch
        return runnerJob.zipWith (fun runner _ => some runner) (exporterJob.mix miriJob)
    let tools ← selectRustTools root
    let (_, exportEnv) ← sysrootEnv tools root #[
      ("MIRI_SYSROOT", some (miriSysroot root).toString),
      ("LEAN_MIRI_PREPARED_ALLOC_ID_WORLD", some "1")]
    IO.println s!"export {sourceAbs} -> {output}"
    (← IO.getStdout).flush
    let mut exportArgs := #["--output", output.toString]
    for defPath in parsed.roots do
      exportArgs := exportArgs.push "--root" |>.push defPath
    exportArgs := exportArgs ++ #[ "--", sourceAbs.toString, "--crate-name", crateName] ++ parsed.rustcArgs
    let exportCode ← spawnInherit {
      cmd := exporterBin root |>.toString
      args := exportArgs
      cwd := some root
      env := exportEnv
    }
    if exportCode != 0 then
      return exportCode
    let some runner := runner?
      | return 0
    let mut runnerArgs := #[output.toString]
    if let some seed := parsed.seed then
      runnerArgs := runnerArgs.push "--seed" |>.push seed
    if parsed.profile then
      runnerArgs := runnerArgs.push "--profile"
    let threads ← IO.getEnv "LEAN_NUM_THREADS"
    let threadEnv := if threads.isSome then #[] else #[("LEAN_NUM_THREADS", some "1")]
    spawnInherit {
      cmd := runner.toString
      args := runnerArgs
      cwd := some root
      env := threadEnv
    }

/-- Run the source audit, then build the pinned reference Miri and its sysroot. -/
script «setup-miri-reference» (args) do
  let args := match args with
    | "--" :: rest => rest
    | other => other
  unless args.isEmpty do
    IO.eprintln "Usage: tools/setup-miri-reference.sh"
    return 2
  let _ ← runBuild sourceAudit.fetch
  let _ ← runBuild miriReference.fetch
  return 0

/-- Build the release exporter, or the separate `miri-reference` feature target. -/
script «build-exporter» (args) do
  let args := match args with
    | "--" :: rest => rest
    | other => other
  match args with
  | [] =>
    let _ ← runBuild exporter.fetch
    return 0
  | ["--features", "miri-reference"] =>
    let _ ← runBuild exporterMiriReference.fetch
    return 0
  | _ =>
    IO.eprintln "usage: tools/build-exporter.sh [--features miri-reference]"
    return 2

/-- Export MIR with the already built release exporter. `tools/export-mir.sh` builds the `exporter` target first. -/
script «export-mir» (args) do
  let args := match args with
    | "--" :: rest => rest
    | other => other
  let root := (← getWorkspace).root.dir
  let bin := exporterBin root
  unless ← System.FilePath.pathExists bin do
    IO.eprintln s!"Optimized exporter is missing: {bin} (build it with tools/build-exporter.sh)"
    return 1
  let sysroot ← match ← IO.getEnv "MIRI_SYSROOT" with
    | some value => pure (if value.isEmpty then (miriSysroot root).toString else value)
    | none => pure (miriSysroot root).toString
  let targetDir ← match ← IO.getEnv "CARGO_TARGET_DIR" with
    | some value =>
      if value.isEmpty then pure (root / "exporter" / "target").toString else pure value
    | none => pure (root / "exporter" / "target").toString
  let tools ← selectRustTools root
  let (_, exportEnv) ← sysrootEnv tools root #[
    ("MIRI_SYSROOT", some sysroot),
    ("CARGO_TARGET_DIR", some targetDir)]
  spawnInherit { cmd := bin.toString, args := args.toArray, env := exportEnv }

/-- Run an exported JSON input on the already built native runner. -/
script run (args) do
  let args := match args with
    | "--" :: rest => rest
    | other => other
  let some input := args.head?
    | IO.eprintln "usage: lake run run INPUT.json [--seed U64] [--profile]"
      return 64
  let root := (← getWorkspace).root.dir
  let child ← IO.Process.spawn {
    cmd := (root / ".lake" / "build" / "bin" / "native_runner").toString
    args := (input :: args.tail).toArray
    cwd := some root
  }
  child.wait
