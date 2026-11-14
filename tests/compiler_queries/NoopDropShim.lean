import Miri.Input.NoopDropShim
import Miri.Input.MirTemplateCodec

/-! Fresh pinned `DropGlue(_, None)` constructor differential. Expected type
IDs come from the oracle only here; production integration must intern them. -/
open Lean Miri.Input
private def check (input : Json) : Except String Nat := do
  let rows ← input.getArr?
  for row in rows do
    let signature ← GenericMaterialCodec.readTerm 16384 (← row.getObjVal? "signature")
    let arguments ← (← (← row.getObjVal? "arguments").getArr?).mapM (GenericMaterialCodec.readTerm 16384)
    let expected ← MirTemplateCodec.readTemplate (← row.getObjVal? "expected")
    let resolve (term : GenericSubstitution.Term) : Except String Nat := do
      let term ← MirTemplate.eraseFreeRegions 16384 term
      let some index := expected.types.findIdx? (· == term)
        | throw "no-op drop constructor type absent from actual rustc body"
      pure index
    let actual ← NoopDropShim.instantiate 16384 signature arguments ⟨0⟩ resolve
    let reference ← MirTemplate.instantiate expected 16384 arguments resolve
    unless actual == reference do throw "no-op drop constructor differs from pinned rustc"
    let failed : Except String Miri.MIR.Body := NoopDropShim.instantiate 16384 signature arguments ⟨0⟩
      (fun _ => .error "type construction unavailable")
    match failed with
    | .error "type construction unavailable" => pure ()
    | _ => throw "no-op drop constructor swallowed type construction failure"
    unless (NoopDropShim.instantiate 16384 signature #[] ⟨0⟩ resolve).toOption.isNone do
      throw "no-op drop constructor accepted missing argument"
    let .binder _ source := signature | throw "oracle signature is not bound"
    let unsupported := GenericSubstitution.Term.binder #[.type .anonymous] source
    unless (NoopDropShim.instantiate 16384 unsupported arguments ⟨0⟩ resolve).toOption.isNone do
      throw "no-op drop constructor accepted a bound type variable"
    let nested := GenericSubstitution.Term.binder #[] (.binder #[] source)
    unless (NoopDropShim.instantiate 16384 nested arguments ⟨0⟩ resolve).toOption.isNone do
      throw "no-op drop constructor accepted an unsupported nested signature binder"
  unless rows.size == 5 do throw "no-op drop source oracle omitted required instances"
  pure rows.size

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected pinned no-op drop shim oracle JSON")
  match Json.parse (← IO.FS.readFile path) >>= check with
  | .ok count => IO.println s!"PASS {count} no-op drop shim bodies match actual rustc; missing argument/type failures reject"
  | .error error => throw (IO.userError error)
