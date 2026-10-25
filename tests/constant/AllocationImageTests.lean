import Miri.Input.Decoder
import Miri.Input.AllocationImage
import Miri.Interpreter.Constant

open Miri Input Memory ABI Interpreter

private def must (value : Except String A) : IO A :=
  match value with | .ok value => pure value | .error e => throw (IO.userError e)
private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def queries : AllocationImage.Queries := {
  -- These are explicit facts of mir_features.rs's local static declarations;
  -- the image supplies the successful compiler initializer query result.
  staticInfo := fun source => do
    unless source.definitionPath == "STATIC_DATA" || source.definitionPath == "STATIC_REF" ||
        source.definitionPath == "VTABLE_ROOT" do
      throw "static classification/layout query has no fixture evidence"
    let some initializer := source.initializer | throw "fixture static requires its compiler initializer"
    let size ← (RuntimeMetadata.size initializer.sizeBytes).mapError toString
    let align ← (RuntimeMetadata.alignment initializer.alignBytes).mapError toString
    let mutability ← match initializer.mutability with
      | .immutable => pure Memory.Mutability.Not
      | .mutable => pure .Mut
      | .unknown _ => throw "unknown static mutability"
    pure ⟨size, align, mutability, true, false⟩
}

private def globals (image : AllocationImage.Imported) : GlobalAllocationHooks CtfeProvenance Unit Unit (Array String) := {
  synchronizeMemory := fun _ state => state
  evaluateStaticInitializer := fun memory state definition =>
    let result := image.evaluateStaticInitializer (state.push "eval") definition
    ⟨memory,result.state,result.outcome⟩
  beforeAccessGlobal := fun memory state _ _ _ _ => ⟨memory, state.push "before", .ok ()⟩
  adjustGlobalAllocation := fun memory state _ allocation => ⟨memory, state.push "adjust", .ok (.owned allocation)⟩
}

private def constantQueries : ConstantQueries CtfeProvenance Unit Unit (Array String) := {
  instantiateAndNormalize := fun fnInstance constant => do
    unless fnInstance.args.isEmpty do throw (.query "fixture normalization requires monomorphic empty InstanceArgs")
    pure constant
  evaluate := fun _ _ _ => throw (.query "no compiler type-constant evaluation evidence in this fixture adapter")
  adjustGlobalRootPointer := fun pointer => do
    let state ← EStateM.get
    EStateM.set { state with hooks := state.hooks.push "root" }
    pure pointer
  externStaticPointer := fun _ => throw (.query "no foreign-static pointer evidence")
}

def main (args : List String) : IO Unit := do
  let path ← match args with | path :: _ => pure path | [] => throw (IO.userError "expected mir_features compiler export")
  let decoded ← must (decodeJson (← IO.FS.readFile path))
  let runtime ← must ((RuntimeMetadata.ofDocument decoded.document).mapError toString)
  let program ← must (lowerProgram decoded.document)
  let initial : MemoryState CtfeProvenance Unit Unit := { MemoryState.empty with nextAllocId := 100 }
  let imported := AllocationImage.importGraph runtime.target program.bundle.definitions queries decoded.document.allocations initial
  let image ← must imported.outcome
  check (imported.memory.importedGlobalIds.size == decoded.document.allocations.size) "global graph lost identity"
  for node in decoded.document.allocations do
    let actual ← must (AllocationImage.runtimeId imported.memory node.id)
    check (actual.value.toNat ≥ 100 && actual.value.toNat != node.id + 1) "source export ID was used as runtime AllocId"
    match node.data with
    | some (.memory source) =>
      let rebuilt ← must (AllocationImage.decode runtime.target imported.memory source)
      check (rebuilt.byteSize.bytes.toNat == source.sizeBytes) "allocation size lost"
      check (rebuilt.provenanceMap.ptrs.size == source.relocations.size) "relocation lost"
      for relocation in source.relocations do
        let target ← must (AllocationImage.runtimeId imported.memory relocation.target)
        let some (_, provenance) := rebuilt.provenanceMap.ptrs.find? (fun p => p.1.bytes.toNat == relocation.storageOffsetBytes)
          | throw (IO.userError "pointer offset lost")
        check (provenance.allocId == target && provenance.immutable == relocation.immutable && provenance.sharedRef == relocation.sharedRef) "CTFE relocation flags or runtime mapping changed"
    | _ => pure ()
  let some static := decoded.document.allocations.find? (fun node => match node.data with
    | some (.static value) => value.definitionPath == "STATIC_DATA" | _ => false)
    | throw (IO.userError "missing actual STATIC_REF allocation")
  let id ← must (AllocationImage.runtimeId imported.memory static.id)
  let first := MemoryLifecycle.getAllocRaw imported.memory #[] id (some ()) (globals image)
  let _ ← must (first.outcome.mapError (fun e => reprStr e))
  check (first.hooks == #["eval", "before", "adjust"]) "global initializer/hook source order changed"
  let second := MemoryLifecycle.getAllocRaw first.memory first.hooks id (some ()) (globals image)
  let _ ← must (second.outcome.mapError (fun e => reprStr e))
  check (second.hooks == first.hooks) "cached owned global repeated initializer/hooks"
  let some primitive := decoded.document.types.find? (fun ty => ty.shapeKind == .uint && ty.layout.sizeBytes == some 4)
    | throw (IO.userError "fixture lacks u32 layout")
  let state : ConstantState CtfeProvenance Unit Unit (Array String) :=
    ⟨imported.memory, #[], ⟨.Item (← must (program.rootDefinitionId 0)), #[]⟩⟩
  match constValueToOp runtime constantQueries (.Indirect static.id 0) primitive.id state with
  | .error error _ => throw (IO.userError (reprStr error))
  | .ok operand after =>
    check (after.hooks == #["root"]) "constant construction eagerly accessed global storage"
    match operand.op with
    | .indirect place =>
      let some provenance := place.ptr.provenance | throw (IO.userError "indirect constant lost provenance")
      check (provenance.allocId == id && provenance.immutable && provenance.sharedRef) "indirect constant lost immutable CTFE root"
    | _ => throw (IO.userError "indirect constant became immediate")
  let some staticRefBody := program.bundle.bodies.find? (fun body => body.input.defPath == "STATIC_REF")
    | throw (IO.userError "missing actual STATIC_REF body")
  let actualConstant := staticRefBody.body.basicBlocks.foldl (fun found block =>
    block.statements.foldl (fun found statement => match found, statement.kind with
      | some value, _ => some value
      | none, .Assign _ (.Use (.Constant constant) _) => some constant
      | none, _ => none) found) (none : Option MIR.ConstOperand)
  let some actualConstant := actualConstant | throw (IO.userError "actual compiler constant operand was lost")
  let actualState := { state with currentInstance := ⟨.Item (← must staticRefBody.ownDefinitionId), #[]⟩ }
  match evalConstOperand runtime constantQueries actualConstant actualState with
  | .error error _ => throw (IO.userError (reprStr error))
  | .ok actual after =>
    match actual.op with
    | .immediate (.scalar scalar) =>
      match scalar.toBitsOrPtrInternal scalar.size with
      | .ok (.pointer pointer) =>
        check (pointer.provenance.allocId == id && !pointer.provenance.immutable && !pointer.provenance.sharedRef) "actual compiler operand flags changed"
        match constantGetAllocRaw pointer.provenance.allocId (some ()) (globals image) after with
        | .error error _ => throw (IO.userError (reprStr error))
        | .ok allocation loaded =>
          check (loaded.hooks == #["root", "eval", "before", "adjust"]) "constant-to-global access lost hook order/state"
          let firstWord ← must ((allocation.readScalar runtime.target.base (allocRange pointer.offset (.ofBytes 4)) false).mapError toString)
          match firstWord.toBitsOrPtrInternal (.ofBytes 4) with
          | .ok (.bits bits) => check (bits.toNat == 11) "actual constant pointer reached incorrect STATIC_DATA bytes"
          | _ => throw (IO.userError "actual STATIC_DATA first element was not initialized integer bytes")
      | _ => throw (IO.userError "actual compiler pointer constant became integer")
    | _ => throw (IO.userError "actual compiler pointer constant changed shape")
    check (after.hooks == #["root"]) "actual constant operand initialized static eagerly"
  let unknown := AllocationImage.runtimeId imported.memory 999999
  check (!unknown.isOk) "missing compiler allocation metadata accepted"
  let parameter : MIR.MirConst := .Ty primitive.id (.Param 0 "N" none)
  let result := evalMirConstant runtime constantQueries parameter ⟨0⟩ state
  match result with
  | .error (.query _) _ => pure ()
  | _ => throw (IO.userError "unknown generic constant became a successful default")
  IO.println s!"actual compiler graph imported: {image.source.size} globals; relocation identity/flags, lazy initializer order/cache, indirect constant root and missing-query rejection passed"
