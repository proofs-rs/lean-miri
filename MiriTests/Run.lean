import MiriTests.RuntimeChecks

/-! Run self-contained assertions in isolated Lean processes. Source elaboration
also reruns #eval checks even when Lake's module artifacts are already cached.
Run from the repository root. --case accepts an exact source path or module name. -/

private def moduleName (path : String) : String :=
  (path.dropEnd 5).toString.replace "/" "."

def main (args : List String) : IO UInt32 := do
  if args == ["--list"] then
    for (path, _) in MiriTests.runtimeChecks do IO.println (moduleName path)
    return 0
  let selected ← match args with
    | [] => pure MiriTests.runtimeChecks
    | ["--case", name] => do
      let selected := MiriTests.runtimeChecks.filter fun (path, _) =>
        path == name || moduleName path == name
      if selected.isEmpty then
        throw (IO.userError s!"unknown runtime check: {name}; use --list")
      pure selected
    | _ => throw (IO.userError "usage: lake exe miri_tests [--list | --case MODULE_OR_PATH]")
  let lake ← IO.getEnv "LAKE" <&> (·.getD "lake")
  for (path, runMain) in selected do
    IO.println s!"Checking {path}"
    (← IO.getStdout).flush
    let args := #["env", "lean"] ++ (if runMain then #["--run"] else #[]) ++ #[path]
    let child ← IO.Process.spawn {cmd := lake, args, stdout := .inherit, stderr := .inherit}
    let code ← child.wait
    if code != 0 then
      IO.eprintln s!"FAILED: {path} (exit {code})"
      return code
  IO.println s!"Passed {selected.size} self-contained runtime checks"
  return 0
