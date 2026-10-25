import Miri.Interpreter.FloatOps
open Miri Miri.ABI Miri.Memory Miri.Interpreter
set_option maxRecDepth 25000
set_option maxHeartbeats 4000000
private def layout (id : Nat) (size : UInt64 := 2) : TyAndLayout MIR.TyId := ⟨id, {
  fields := .Primitive, variants := .Single 0,
  backendRepr := .Scalar (.Union (value := .Float .F16)), largestNiche := none,
  uninhabited := false, align := .new .ONE, size := Size.ofBytes size,
  maxReprAlign := none, unadjustedAbiAlign := .ONE, reprC := false, randomizationSeed := 0 }⟩
private def value (bits : UInt16) : RvalueImmTy AllocId :=
  ⟨.scalar (.fromScalarInt (.ofUInt16 bits)), layout 0⟩
private abbrev Trace := List String
private def log (name : String) (value : A) : RvalueM Trace A := do
  modify (· ++ [name]); pure value
private def blocked (name : String) : RvalueM Trace A := do
  modify (· ++ [name]); throw (.unsupported name)
private def hooks : FloatOpsHooks AllocId Trace Nat where
  integerKindOf := fun _ ty => if ty == 5 then pure .i8 else if ty == 6 then pure .u8
    else blocked "unknown integer type"
  formatOf := fun _ ty => if ty == 0 then log "format" .binary16
    else if ty == 1 then log "format" .binary32 else blocked "unknown float type"
  boolLayout := fun _ => log "boolLayout" (layout 4 1)
  floatNondeterministic := true
  chooseNaN := fun index _ => log "chooseNaN" index
private def scalarHooks : ScalarOpsHooks AllocId Trace Nat where
  classify := fun _ ty => if ty == 0 || ty == 1 then pure .floating else blocked "unknown scalar type"
  boolLayout := hooks.boolLayout
  orderingLayout := fun _ => blocked "orderingLayout"
  overflowLayout := fun _ _ => blocked "overflowLayout"
  metadataLayout := fun _ _ => blocked "metadataLayout"
  unitLayout := fun _ => blocked "unitLayout"
  floatBinary := FloatOps.binary hooks
  pointerBinary := fun _ _ _ _ => blocked "pointerBinary"
  floatUnary := FloatOps.unary hooks
  derefValidity := fun _ _ => blocked "derefValidity"
private def run (action : RvalueM Trace A) := runRvalue action []
example : (run (ScalarOps.binary scalarHooks 0 .Add (value 15360) (value 15360))).2 =
    .ok (value 16384) := by decide
example : (run (ScalarOps.binary scalarHooks 99 .Add (value 15360) (value 15360))).1 =
    ["format", "format"] := by decide
example : (run (ScalarOps.binary scalarHooks 0 .Eq (value 0) (value 32768))).2 =
    .ok ⟨.scalar (.fromBool true), layout 4 1⟩ := by decide
-- Arithmetic NaNs use the checked Miri choice relation, including signaling
-- propagation and independent sign choice. Invalid choices cannot succeed.
example : (run (ScalarOps.binary scalarHooks 4 .Add (value 31745) (value 15360))).2 =
    .ok (value 31745) := by decide
example : (run (ScalarOps.binary scalarHooks 5 .Sub (value 31745) (value 15360))).2 =
    .ok (value 64513) := by decide
example : (run (ScalarOps.binary scalarHooks 99 .Mul (value 0) (value 31744))).2 =
    .error (.invalidProgram "invalid floating NaN choice index") := by decide
example : (run (ScalarOps.unary scalarHooks 99 .Neg (value 31745))).2 =
    .ok (value 64513) := by decide
example : (run (ScalarOps.unary scalarHooks 99 .Neg (value 31745))).1 = ["format"] := by decide
example : (run (FloatOps.castFloatToFloat hooks 0 (value 15360) (layout 1 4))).2 =
    .ok ⟨.scalar (.fromScalarInt (.ofUInt32 1065353216)), layout 1 4⟩ := by decide
example : (run (FloatOps.castFloatToInt hooks 0 (value 48640) (layout 5 1))).2 =
    .ok ⟨.scalar (.fromScalarInt (.ofInt8 (-1))), layout 5 1⟩ := by decide
example : (run (FloatOps.castFloatToInt hooks 0 (value 31744) (layout 6 1))).2 =
    .ok ⟨.scalar (.fromScalarInt (.ofUInt8 255)), layout 6 1⟩ := by decide
example : (run (FloatOps.castIntToFloat hooks 0
    ⟨.scalar (.fromScalarInt (.ofInt8 (-1))), layout 5 1⟩ (layout 0))).2 =
    .ok (value 48128) := by decide
example : (run (ScalarOps.binary { scalarHooks with
    floatBinary := FloatOps.binary { hooks with floatNondeterministic := false } }
    99 .Add (value 31745) (value 15360))).2 = .ok (value 32256) := by decide
