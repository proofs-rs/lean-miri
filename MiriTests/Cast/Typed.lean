import Miri.Interpreter.Cast
open Miri Miri.ABI Miri.Memory Miri.Interpreter
namespace CastQA
abbrev Trace := List String
private def log (name : String) (value : A) : RvalueM Trace A := do
  modify (· ++ [name]); pure value
private def blocked (name : String) : RvalueM Trace A := do
  modify (· ++ [name]); throw (.unsupported name)
-- Explicit fixture type table: u8/u32/f16/f32/raw pointer/capturing closure/fn pointer.
private def layout (id : Nat) : TyAndLayout MIR.TyId :=
  let bytes : UInt64 := if id == 0 then 1 else if id == 1 || id == 3 then 4 else if id == 2 then 2 else 8
  let align : Align := if bytes == 1 then ⟨0⟩ else if bytes == 2 then ⟨1⟩ else if bytes == 4 then ⟨2⟩ else ⟨3⟩
  let primitive := if id == 2 then Primitive.Float .F16 else if id == 3 then .Float .F32 else if id == 1 then .Int .I32 false else .Int .I8 false
  ⟨id, {
    fields := .Primitive, variants := .Single 0, backendRepr := .Scalar (.Union (value := primitive)),
    largestNiche := none, uninhabited := false, align := .new align, size := Size.ofBytes bytes,
    maxReprAlign := none, unadjustedAbiAlign := align, reprC := false, randomizationSeed := 0 }⟩
private def hooks : CastHooks AllocId Trace Unit (TyAndLayout MIR.TyId) where
  target := ⟨.little,.w64⟩
  typeInfo := fun _ ty => do
    let _ ← log s!"type:{ty}" ()
    match ty with
    | 0 => pure (.integer .u8) | 1 => pure (.integer .u32)
    | 2 => pure (.floating .binary16) | 3 => pure (.floating .binary32)
    | 4 => pure (.rawPointer 0) | 5 => pure (.closure 0 #[] 1)
    | 6 => pure .fnPointer | _ => blocked "unknown type"
  layoutOf := fun _ ty => if ty <= 6 then log s!"layout:{ty}" (layout ty) else blocked "layout"
  destLayout := id
  readImmediate := fun _ op => do
    let _ ← log "read" ()
    match op.op with | .immediate value => pure ⟨value,op.layout⟩ | _ => blocked "indirect read"
  writeImmediate := fun _ value dest =>
    let expected : Immediate AllocId := if dest.ty == 1 then .scalar (.fromScalarInt (.ofUInt32 42))
      else .scalar (.fromScalarInt (.ofUInt32 1065353216))
    if value == expected then log "write" () else blocked "wrong write value"
  writePointer := fun _ _ _ => blocked "writePointer"
  enforceValidity := fun _ _ => log "validity" true
  enforceValidityRecursively := fun _ _ => blocked "recursiveValidity"
  validatePlace := fun _ _ _ _ => blocked "validatePlace"
  derefPointer := fun _ _ => blocked "derefPointer"
  checkFunctionPointer := fun _ _ => blocked "checkFunctionPointer"
  exposeProvenance := fun _ _ => blocked "exposeProvenance"
  pointerFromExposedAddress := fun _ _ => blocked "pointerFromExposedAddress"
  usizeLayout := fun _ => blocked "usizeLayout"
  floatOps := {
    integerKindOf := fun _ _ => blocked "integerKind"
    formatOf := fun _ ty => if ty == 2 then log "format" .binary16 else if ty == 3 then log "format" .binary32 else blocked "format"
    boolLayout := fun _ => blocked "boolLayout"
    floatNondeterministic := false
    chooseNaN := fun _ _ => blocked "chooseNaN" }
  ensureMonomorphic := fun _ _ => blocked "ensureMonomorphic"
  requireNoBoundVars := fun _ _ => blocked "requireNoBoundVars"
  resolveFunction := fun _ _ _ => blocked "resolveFunction"
  resolveClosureFnOnce := fun _ _ _ => blocked "resolveClosureFnOnce"
  functionPointer := fun _ _ => blocked "functionPointer"
  builtinDeref := fun _ _ _ => blocked "builtinDeref"
  boxLayout := fun _ _ => blocked "boxLayout"
  validateImmediateABI := fun _ _ => .error (.unsupported "validateImmediateABI")
  copyAllowTransmute := fun _ _ _ => log "copy" ()
  copyNoValidate := fun _ _ _ _ => blocked "copyNoValidate"
  projectRead := fun _ _ _ => blocked "projectRead"
  projectWrite := fun _ _ _ => blocked "projectWrite"
  fieldLayout := fun _ _ _ => blocked "fieldLayout"
  lockstepTails := fun _ _ _ => blocked "lockstepTails"
  vtableType := fun _ _ _ => blocked "vtableType"
  vtablePointer := fun _ _ _ => blocked "vtablePointer"
  principal := fun _ _ => blocked "principal"
  vtableEntries := fun _ _ _ => blocked "vtableEntries"
  supertraitSlot := fun _ _ _ => blocked "supertraitSlot"
  eraseSelfTraitRef := fun _ _ => blocked "eraseSelfTraitRef"
  normalizePrincipal := fun _ _ => blocked "normalizePrincipal"
private def op (ty : Nat) (value : Immediate AllocId) : OpTy AllocId := ⟨.immediate value,layout ty⟩
private def run (value : OpTy AllocId) (kind : MIR.CastKind) (target dest : Nat) :=
  runRvalue (Cast.cast hooks () 8 value kind target (layout dest)) []
example : (run (op 0 (.scalar (.fromScalarInt (.ofUInt8 42)))) .IntToInt 1 1).2 = .ok () := by decide
example : (run (op 0 (.scalar (.fromScalarInt (.ofUInt8 42)))) .IntToInt 1 1).1 =
  ["validity","type:0","read","type:0","type:1","type:0","type:1","write"] := by decide
-- Layout resolution must fail before source validity/read.
example : (run (op 0 .uninit) .IntToInt 99 1).1 = ["layout"] := by decide
-- Scalar extraction fails before target type query on float conversion.
example : (run (op 2 .uninit) .FloatToInt 1 1).1 = ["validity","type:2","read","type:2"] := by decide
example : (run (op 5 .uninit) .IntToInt 1 1).1 = ["validity","type:5"] := by decide
-- Transmute skips source validity and checks sizes before its required copy.
example : (run (op 0 .uninit) .Transmute 0 0).1 = ["copy"] := by decide
example : (run (op 0 .uninit) .Transmute 1 1).2 = .error (.undefinedBehavior "transmute size mismatch") := by decide
example : (run (op 2 (.scalar (.fromScalarInt (.ofUInt16 15360)))) .FloatToFloat 3 3).2 = .ok () := by decide
end CastQA
