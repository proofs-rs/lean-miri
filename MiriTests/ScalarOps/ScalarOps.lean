import Miri.Interpreter.ScalarOps
open Miri Miri.ABI Miri.Memory Miri.Interpreter

private def layout (id : Nat) (bytes : UInt64 := 1) : TyAndLayout MIR.TyId := ⟨id, {
  fields := .Primitive, variants := .Single 0, backendRepr := .Scalar (.Union (value := .Int .I8 false)),
  largestNiche := none, uninhabited := false, align := .new Align.ONE,
  size := Size.ofBytes bytes, maxReprAlign := none, unadjustedAbiAlign := Align.ONE,
  reprC := false, randomizationSeed := 0 }⟩
private abbrev Trace := List String
private def log (name : String) (value : A) : RvalueM Trace A := do
  modify (· ++ [name])
  pure value
private def blocked (name : String) : RvalueM Trace A := do
  modify (· ++ [name])
  throw (.unsupported name)
private def hooks : ScalarOpsHooks AllocId Trace Unit where
  classify := fun _ ty => do
    let _ ← log s!"classify:{ty}" ()
    match ty with
    | 0 | 6 => pure (.integer .u8)
    | 1 => pure (.integer .i8)
    | 2 => pure .boolean
    | 3 => pure .character
    | 4 => pure .pointer
    | 5 => pure .floating
    | _ => throw (.unsupported "type classification")
  boolLayout := fun _ => log "boolLayout" (layout 2)
  orderingLayout := fun _ => log "orderingLayout" (layout 10)
  overflowLayout := fun _ _ => log "overflowLayout" (layout 11 2)
  metadataLayout := fun _ _ => log "metadataLayout" (layout 12 8)
  unitLayout := fun _ => log "unitLayout" (layout 13 0)
  floatBinary := fun _ _ _ _ => blocked "floatBinary"
  pointerBinary := fun _ _ _ _ => blocked "pointerBinary"
  floatUnary := fun _ _ _ => blocked "floatUnary"
  derefValidity := fun _ _ => log "derefValidity" ()
private def u8 (n : UInt8) (ty : Nat := 0) : RvalueImmTy AllocId :=
  ⟨.scalar (.fromScalarInt (.ofUInt8 n)), layout ty⟩
private def boolean (b : Bool) : RvalueImmTy AllocId := ⟨.scalar (.fromBool b), layout 2⟩
private def character (c : Char) : RvalueImmTy AllocId := ⟨.scalar (.fromChar c), layout 3 4⟩
private def result (action : RvalueM Trace A) : Except StepError A := (runRvalue action []).2
private def trace (action : RvalueM Trace A) : Trace := (runRvalue action []).1

example : result (ScalarOps.binary hooks () .Add (u8 255) (u8 2)) = .ok (u8 1) := by decide
example : result (ScalarOps.binary hooks () .AddWithOverflow (u8 255) (u8 2)) =
    .ok ⟨.scalarPair (.fromScalarInt (.ofUInt8 1)) (.fromBool true), layout 11 2⟩ := by decide
example : trace (ScalarOps.binary hooks () .AddWithOverflow (u8 255) (u8 2)) =
    ["classify:0", "classify:0", "overflowLayout"] := by decide
example : result (ScalarOps.binary hooks () .Eq (u8 1) (u8 1)) = .ok (boolean true) := by decide
example : result (ScalarOps.binary hooks () .Lt (character 'a') (character 'z')) =
    .ok (boolean true) := by decide
example : result (ScalarOps.binary hooks () .Cmp (character 'z') (character 'a')) =
    .ok ⟨.scalar (.fromScalarInt (.ofInt8 1)), layout 10⟩ := by decide
example : result (ScalarOps.binary hooks () .BitXor (boolean true) (boolean true)) =
    .ok (boolean false) := by decide
example : result (ScalarOps.unary hooks () .Not (boolean false)) = .ok (boolean true) := by decide
example : result (ScalarOps.unary hooks () .Not (u8 15)) = .ok (u8 240) := by decide
example : result (ScalarOps.unary hooks () .Neg (u8 128 1)) = .ok (u8 128 1) := by decide
-- Different TyIds remain different even with identical IntegerKind and size.
example : result (ScalarOps.binary hooks () .Add (u8 1) (u8 2 6)) =
    .error (.invalidProgram "asymmetric scalar operand types") := by decide
-- Heterogeneous integer shifts remain permitted.
example : result (ScalarOps.binary hooks () .Shl (u8 1) (u8 2 1)) = .ok (u8 4) := by decide
example : (match result (ScalarOps.binary hooks () .Div (u8 1) (u8 0)) with
    | .error (.undefinedBehavior _) => true | _ => false) = true := by decide
example : result (ScalarOps.binary hooks () .Add (u8 1 5) (u8 2 5)) =
    .error (.unsupported "floatBinary") := by decide
example : result (ScalarOps.binary hooks () .Offset (u8 1 4) (u8 2)) =
    .error (.unsupported "pointerBinary") := by decide
-- Thin pointer metadata validates dereference before querying unit layout.
example : trace (ScalarOps.unary hooks () .PtrMetadata (u8 1 4)) =
    ["classify:4", "derefValidity", "unitLayout"] := by decide
example : trace (ScalarOps.unary { hooks with derefValidity := fun _ _ => blocked "invalidPointer" }
    () .PtrMetadata (u8 1 4)) = ["classify:4", "invalidPointer"] := by decide
example : result (ScalarOps.binary hooks () .Eq (u8 2 2) (boolean true)) =
    .error (.undefinedBehavior "2 is not a valid bool representation") := by decide
example : result (ScalarOps.binary hooks () .Add (u8 1 99) (u8 2)) =
    .error (.unsupported "type classification") := by decide
example : ScalarOps.scalarError .readPointerAsInt = .unsupported "read pointer as integer" := by decide

-- The actual Rvalue dispatcher calls the typed scalar implementation and writes
-- its computed immediate. There is no translated per-function operator IR.
private def place : MIR.Place := ⟨0, #[]⟩
private def rvalueHooks : RvalueHooks AllocId Trace Unit Unit where
  placeLayout := fun _ => layout 0
  evalPlace := fun _ _ _ => log "place" ()
  evalOperand := fun _ _ _ => log "operand" ⟨.immediate (.scalar (.fromScalarInt (.ofUInt8 2))), layout 0⟩
  evalPlaceToOp := fun _ _ _ => blocked "placeToOp"
  readImmediate := fun _ op => do
    let _ ← log "read" ()
    match op.op with
    | .immediate value => pure ⟨value, op.layout⟩
    | .indirect _ => blocked "memory read"
  writeImmediate := fun _ value _ =>
    if value == (u8 4).imm then log "write:4" () else blocked "unexpected result"
  writePointer := fun _ _ _ => blocked "writePointer"
  threadLocalPointer := fun _ _ => blocked "threadLocal"
  withRetagMode := fun _ _ action => action
  copyOp := fun _ _ _ => blocked "copy"
  copyOpAllowTransmute := fun _ _ _ => blocked "copyTransmute"
  binaryOp := ScalarOps.binary hooks
  unaryOp := ScalarOps.unary hooks
  writeAggregate := fun _ _ _ _ => blocked "aggregate"
  writeRepeat := fun _ _ _ => blocked "repeat"
  forceAllocation := fun _ _ => blocked "allocate"
  toRef := fun _ _ => blocked "toRef"
  enforceValidity := fun _ _ => blocked "validity"
  retagPtrValue := fun _ _ _ => blocked "retag"
  placeBaseRaw := fun _ _ => blocked "baseRaw"
  normalize := fun _ _ => blocked "normalize"
  cast := fun _ _ _ _ _ => blocked "cast"
  readDiscriminant := fun _ _ => blocked "discriminant"
  discriminantForVariant := fun _ _ _ => blocked "discriminantValue"
example : trace (evalRvalueIntoPlace rvalueHooks ()
    (.BinaryOp .Add (.Copy place) (.Copy place)) place) =
    ["place", "operand", "read", "operand", "read", "classify:0", "classify:0", "write:4"] := by decide
example : result (evalRvalueIntoPlace rvalueHooks ()
    (.BinaryOp .Add (.Copy place) (.Copy place)) place) = .ok () := by decide

-- Missing result metadata fails after arithmetic, preserving query state.
example : trace (ScalarOps.binary { hooks with overflowLayout := fun _ _ => blocked "missing pair layout" }
    () .AddWithOverflow (u8 255) (u8 2)) =
    ["classify:0", "classify:0", "missing pair layout"] := by decide
example : result (ScalarOps.binary hooks () .Shl (u8 1) (u8 255 1)) = .ok (u8 128) := by decide
