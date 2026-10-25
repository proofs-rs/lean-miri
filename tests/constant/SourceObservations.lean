import Miri.Input.Decoder
import Miri.Interpreter.Constant
open Miri Input Memory ABI Interpreter
private def must (v : Except String A) : IO A := match v with | .ok a => pure a | .error e => throw (IO.userError e)
private def scalarText (scalar : Scalar CtfeProvenance) : String :=
  match scalar.toBitsOrPtrInternal scalar.size with
  | .ok (.bits bits) => s!"int:{bits.toNat}"
  | .ok (.pointer p) => s!"ptr:{p.provenance.allocId.value}:{p.offset.bytes}:{p.provenance.immutable}:{p.provenance.sharedRef}"
  | .error e => s!"error:{e}"
private def queries : ConstantQueries CtfeProvenance Unit Unit (Array String) := {
  instantiateAndNormalize := fun _ _ => throw (.query "not used by const_val_to_op source comparison")
  evaluate := fun _ _ _ => throw (.query "not used by const_val_to_op source comparison")
  adjustGlobalRootPointer := fun p => do
    let state ← EStateM.get
    EStateM.set { state with hooks := state.hooks.push s!"root:{p.provenance.allocId.value}:{p.offset.bytes}:{p.provenance.immutable}:{p.provenance.sharedRef}" }
    pure p
  externStaticPointer := fun _ => throw (.query "not used by const_val_to_op source comparison")
}
def main (args : List String) : IO Unit := do
  let path ← match args with | p :: _ => pure p | [] => throw (IO.userError "expected compiler fixture")
  let doc ← must (decodeJson (← IO.FS.readFile path))
  let runtime ← must ((RuntimeMetadata.ofDocument doc.document).mapError toString)
  let some ty := doc.document.types.find? (fun t => t.layout.sizeBytes == some 4 && t.shapeKind == .uint)
    | throw (IO.userError "fixture requires u32 layout")
  let program ← must (lowerProgram doc.document)
  let own ← must (program.rootDefinitionId 0)
  let initial : MemoryState CtfeProvenance Unit Unit := { MemoryState.empty with nextAllocId := 100 }
  let registered := MemoryLifecycle.registerImportedGlobal initial () 0 .memory (.ofBytes 32) .ONE
  let _ ← must (registered.outcome.mapError toString)
  let some pointerTy := doc.document.types.find? (fun t => t.layout.sizeBytes == some 8 && (t.shapeKind == .reference || t.shapeKind == .rawPointer))
    | throw (IO.userError "fixture requires pointer layout")
  let some zstTy := doc.document.types.find? (fun t => t.layout.sizeBytes == some 0)
    | throw (IO.userError "fixture requires zero-sized layout")
  let some sliceTy := doc.document.types.find? (fun t => t.layout.sizeBytes == some 16 && t.layout.backendReprKind == some .scalarPair)
    | throw (IO.userError "fixture requires wide-pointer layout")
  let cases : Array (String × MIR.ConstValue × Nat) := #[("integer", .Scalar (.Int 7 4), ty.id),
    ("pointer", .Scalar (.Ptr (.Allocation 0 6 false false)), pointerTy.id), ("zst", .ZeroSized, zstTy.id),
    ("slice", .Slice 0 11, sliceTy.id), ("indirect", .Indirect 0 6, ty.id)]
  for (name,value,tyId) in cases do
    let state : ConstantState CtfeProvenance Unit Unit (Array String) := ⟨registered.memory, #[], ⟨.Item own, #[]⟩⟩
    match constValueToOp runtime queries value tyId state with
    | .error e _ => throw (IO.userError (reprStr e))
    | .ok op after =>
      let result := match op.op with
        | .immediate (.scalar s) => scalarText s
        | .immediate (.scalarPair a b) => s!"pair:{scalarText a}:{scalarText b}"
        | .immediate .uninit => "uninit"
        | .indirect p => match p.ptr.provenance with
          | some provenance => s!"indirect:{provenance.allocId.value}:{p.ptr.offset.bytes}:{provenance.immutable}:{provenance.sharedRef}"
          | none => "missing provenance"
      IO.println s!"{name}={result};{String.intercalate "," after.hooks.toList}"
