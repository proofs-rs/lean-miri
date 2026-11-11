import Miri.Input.CompilerForeignSymbols

open Miri.Input Miri.Interpreter

private def check (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)
private def candidate (symbol : String) : CompilerForeignSymbolTables.Candidate := {
  symbol, explicitSymbol := true, fnInstance := none, crateIndex := 0,
  crateName := "actual_guest", weak := false, spanLo := 10, spanHi := 20,
  kind := .function, compilerBuiltins := false }
private def registry (candidates : Array CompilerForeignSymbolTables.Candidate) :
    CompilerForeignSymbolTables.Prepared := ⟨"__rust_no_alloc_shim_is_unstable", candidates, #[]⟩

def main : IO Unit := do
  -- LLVM, ordinary function shims, and extern-static shims share this exact
  -- pinned exported-symbol registry policy, including builtins and duplicates.
  for symbol in #["llvm.x86.sse2.pause", "memcmp", "environ"] do
    check ((CompilerForeignSymbols.checkSymbolClash (registry #[]) symbol).isOk)
      "absent guest symbol unexpectedly clashed"
    let guestExport := candidate symbol
    match CompilerForeignSymbols.checkSymbolClash (registry #[guestExport]) symbol with
    | .error (.machineStop detail) =>
      check (detail.contains "symbol shim clashing") "wrong clash diagnostic"
    | _ => throw (IO.userError "real guest export did not stop the shim")
    check ((CompilerForeignSymbols.checkSymbolClash
      (registry #[{guestExport with compilerBuiltins := true}]) symbol).isOk)
      "compiler-builtins exemption was lost"
    match CompilerForeignSymbols.checkSymbolClash
      (registry #[guestExport, {guestExport with crateIndex := 1, crateName := "other_guest"}]) symbol with
    | .error (.machineStop detail) =>
      check (detail.contains "multiple symbol definitions") "duplicate registry policy changed"
    | _ => throw (IO.userError "duplicate equal-strength exports were accepted")
    let weak := {guestExport with weak := true, compilerBuiltins := true}
    check (!(CompilerForeignSymbols.checkSymbolClash (registry #[weak,guestExport]) symbol).isOk)
      "weak compiler-builtins export displaced the guest's strong definition"
  IO.println "LLVM/ordinary foreign/extern-static symbol-registry controls passed"
