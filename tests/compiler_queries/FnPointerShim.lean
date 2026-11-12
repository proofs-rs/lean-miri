import Miri.Input.FnPointerShim
import Miri.Input.GenericMaterialCodec

/-! Complete interpreter-visible body comparison against fresh pinned rustc
instance_mir, including the shim pass pipeline. Oracle type IDs are used only
inside this differential adapter; production constructs its own shared World. -/
open Lean Miri.Input

private def check (json : Json) : Except String Nat := do
  let rows ← json.getArr?
  for row in rows do
    let direction ← match ← (← row.getObjVal? "kind").getStr? with
      | "as_pointer" => pure FnPointerShim.Direction.asPointer
      | "from_pointer" => pure .fromPointer
      | _ => throw "unknown shim oracle direction"
    let term (name : String) : Except String GenericSubstitution.Term := do
      GenericMaterialCodec.readTerm 16384 (← row.getObjVal? name)
    let signature ← term "signature"
    let selfType ← term "self_type"
    let nonNullType ← term "non_null_type"
    let expected ← row.getObjVal? "expected"
    let types ← (← (← expected.getObjVal? "locals").getArr?).mapM (GenericMaterialCodec.readTerm 16384)
    let resolve (term : GenericSubstitution.Term) : Except String Nat := do
      let some index := types.findIdx? (· == term) | throw "constructed shim local type is absent from rustc body"
      pure index
    let source : Miri.MIR.SourceInfo := ⟨⟨0⟩,0⟩
    let blocks ← (← (← expected.getObjVal? "blocks").getArr?).mapM fun block => do
      let statements ← (← (← block.getObjVal? "statements").getArr?).mapM fun statement => do
        let destination ← (← statement.getObjVal? "destination").getNat?
        let operand ← (← statement.getObjVal? "operand").getNat?
        let cast ← match ← (← statement.getObjVal? "cast").getStr? with
          | "transmute" => pure Miri.MIR.CastKind.Transmute
          | "fn_ptr_to_ptr" => pure .FnPtrToPtr
          | _ => throw "unknown compiler shim cast"
        let target ← resolve (← GenericMaterialCodec.readTerm 16384 (← statement.getObjVal? "target"))
        pure (⟨source,.Assign ⟨destination,#[]⟩ (.Cast cast (.Move ⟨operand,#[]⟩) target)⟩ : Miri.MIR.Statement)
      unless (← (← block.getObjVal? "terminator").getStr?) == "return" do throw "unknown compiler shim terminator"
      pure (⟨statements,⟨source,.Return⟩,← (← block.getObjVal? "cleanup").getBool?⟩ : Miri.MIR.BasicBlock)
    unless (← (← expected.getObjVal? "phase").getStr?) == "runtime_optimized" do throw "compiler shim phase changed"
    let spread ← expected.getObjVal? "spread_argument"
    let spread ← if spread == .null then pure none else some <$> spread.getNat?
    let reference : Miri.MIR.Body := {
      phase := .Runtime .Optimized
      argumentCount := ← (← expected.getObjVal? "argument_count").getNat?
      spreadArgument := spread
      locals := ← types.mapM resolve
      basicBlocks := blocks }
    let actual ← FnPointerShim.instantiate 16384 direction signature selfType nonNullType ⟨0⟩ resolve
    unless actual == reference do throw "FnPtr conversion shim differs from complete pinned rustc body"
    let unavailable : Except String Miri.MIR.Body := FnPointerShim.instantiate 16384 direction
      signature selfType nonNullType ⟨0⟩ (fun _ => .error "type construction unavailable")
    unless unavailable matches .error "type construction unavailable" do throw "shim constructor swallowed type error"
    let wrongSelf := GenericSubstitution.Term.atom .type "uint" "u8"
    if (FnPointerShim.instantiate 16384 direction signature wrongSelf nonNullType ⟨0⟩ resolve).isOk then
      throw "shim accepted non-function-pointer Self"
    if (FnPointerShim.instantiate 16384 direction signature selfType wrongSelf ⟨0⟩ resolve).isOk then
      throw "shim accepted wrong NonNull<Code> identity"
  unless rows.size == 8 do throw "FnPtr conversion oracle omitted required signatures or directions"
  pure rows.size

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected pinned FnPtr shim oracle JSON")
  match Json.parse (← IO.FS.readFile path) >>= check with
  | .ok count => IO.println s!"PASS {count} complete FnPtr conversion shim bodies match pinned rustc; invalid type/source identities reject"
  | .error error => throw (IO.userError error)
