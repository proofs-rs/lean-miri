import Miri.Input.MirTemplateCodec

/-! Fresh pinned rustc generic MIR versus its actual instance normalization.
The test resolver is an explicit oracle catalog of expected type trees; it tests
MIR substitution/traversal, not production interning or normalization fidelity. -/
open Lean Miri.Input
private def field (j : Json) (key : String) : Except String Json := j.getObjVal? key
private def check (json : Json) : Except String Nat := do
  let rows ← json.getArr?
  for row in rows do
    let template ← MirTemplateCodec.readTemplate (← field row "source")
    let expected ← MirTemplateCodec.readTemplate (← field row "expected")
    let args ← (← (← field row "arguments").getArr?).mapM (GenericMaterialCodec.readTerm 16384)
    let resolve (term : GenericSubstitution.Term) : Except String Nat := do
      let some index := expected.types.findIdx? (· == term)
        | throw "instantiated generic MIR type absent from actual rustc oracle"
      pure index
    let actual ← MirTemplate.instantiate template 16384 args resolve
    let reference ← MirTemplate.instantiate expected 16384 args resolve
    unless actual == reference do throw "generic MIR instantiation differs from pinned rustc"
    let missingArgs := MirTemplate.instantiate template 16384 args.pop resolve
    unless missingArgs.toOption.isNone do throw "generic MIR accepted absent generic argument"
    let failed := MirTemplate.instantiate template 16384 args (fun _ => .error "normalization unavailable")
    match failed with
    | .error "normalization unavailable" => pure ()
    | _ => throw "MIR normalization failure did not propagate"
    let malformed := { template with skeleton := { template.skeleton with
      locals := template.skeleton.locals.push ⟨template.types.size⟩ } }
    unless (MirTemplate.instantiate malformed 16384 args resolve).toOption.isNone do
      throw "MIR template accepted absent type slot"
  unless rows.size >= 8 do throw "generic MIR oracle omitted required source bodies"
  pure rows.size

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected pinned generic MIR oracle JSON")
  let input ← IO.FS.readFile path
  match Json.parse input >>= check with
  | .error reason => throw (IO.userError reason)
  | .ok count => IO.println s!"Generic MIR templates match {count} rustc instances; missing args/slots and normalization failures reject."
