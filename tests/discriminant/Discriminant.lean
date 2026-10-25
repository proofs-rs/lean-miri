import Miri.Interpreter.Discriminant
open Miri Miri.ABI Miri.Memory Miri.Interpreter

private def tag : ABI.Scalar := .Initialized (value := .Int .I8 false)
  (validRange := ⟨0, 255⟩)
private def layout (variants : Variants := .Single 0) (id : Nat := 0) : TyAndLayout MIR.TyId := ⟨id, {
  fields := .Arbitrary #[Size.ZERO] #[0], variants := variants,
  backendRepr := .Scalar tag, largestNiche := none, uninhabited := false,
  align := .new .ONE, size := Size.ofBytes 1, maxReprAlign := none,
  unadjustedAbiAlign := .ONE, reprC := false, randomizationSeed := 0 }⟩
private def variant (uninhabited := false) : VariantLayout :=
  ⟨Size.ofBytes 1, .Scalar tag, #[], #[], none, uninhabited⟩
private def direct : TyAndLayout MIR.TyId := layout (.Multiple tag .Direct 0 #[variant, variant, variant])
private def niche : TyAndLayout MIR.TyId := layout (.Multiple tag (.Niche 2 0 1 255) 0 #[variant, variant, variant])
private def scalar (n : UInt8) : Memory.Scalar AllocId := .fromScalarInt (.ofUInt8 n)
private structure State where
  value : Memory.Scalar AllocId
  trace : List String
  deriving DecidableEq, Repr
private def log (s : String) : RvalueM State Unit := modify fun st => { st with trace := st.trace ++ [s] }
private def hooks : DiscriminantHooks AllocId State Unit (TyAndLayout MIR.TyId) where
  runtimeTarget := RuntimeTargetDataLayout.default
  discriminantLayout := fun _ _ => do log "discriminantLayout"; pure (layout (.Single 0) 10)
  tagLayout := fun _ _ => do log "tagLayout"; pure (layout (.Single 0) 11)
  discriminantValue := fun _ _ v => do
    log "discriminantValue"
    pure (some (10, BitVec.ofNat 128 (v * 2)))
  variantForDiscriminant := fun _ _ bits => do
    log "variantForDiscriminant"
    pure (if bits.toNat == 0 then some 0 else if bits.toNat == 2 then some 1 else if bits.toNat == 4 then some 2 else none)
  adtVariantCount := fun _ _ => do log "adtVariantCount"; pure 3
  projectRead := fun _ op _ => do log "projectRead"; pure op
  readImmediate := fun _ _ => do
    log "readImmediate"
    pure ⟨.scalar (← get).value, layout (.Single 0) 11⟩
  destLayout := id
  projectWrite := fun _ dest _ => do log "projectWrite"; pure dest
  writeScalar := fun _ value _ => do
    log "writeScalar"
    modify fun st => { st with value }
  toOp := fun _ dest => do log "toOp"; pure ⟨.immediate .uninit, dest⟩
  scalarMayBeNull := fun _ _ => do log "mayBeNull"; pure false
private def run (action : RvalueM State A) (n : UInt8 := 0) := runRvalue action ⟨scalar n, []⟩
private def op (l : TyAndLayout MIR.TyId) : OpTy AllocId := ⟨.immediate .uninit, l⟩
private def roundTrip (l : TyAndLayout MIR.TyId) (index : Nat) : RvalueM State Nat := do
  Discriminant.writeDiscriminant hooks () index l
  Discriminant.readDiscriminant hooks () (op l)
example : (run (roundTrip direct 0)).2 = .ok 0 := by decide
example : (run (roundTrip direct 1)).2 = .ok 1 := by decide
example : (run (roundTrip direct 2)).2 = .ok 2 := by decide
-- Niche start=255 crosses the one-byte wrap: variant 1 is encoded by zero.
example : (run (roundTrip niche 0)).1.value = scalar 255 := by decide
example : (run (roundTrip niche 1)).1.value = scalar 0 := by decide
example : (run (roundTrip niche 0)).2 = .ok 0 := by decide
example : (run (roundTrip niche 1)).2 = .ok 1 := by decide
example : (run (roundTrip niche 2) 42).2 = .ok 2 := by decide
example : (run (Discriminant.writeDiscriminant hooks () 2 niche) 0).2 =
    .error (.undefinedBehavior "InvalidNichedEnumVariantWritten") := by decide
-- Direct valid_range includes undeclared 3, which still must be invalid.
example : (run (Discriminant.readDiscriminant hooks () (op direct)) 3).2 =
    .error (.undefinedBehavior "InvalidTag(no declared discriminant)") := by decide
example : (run (Discriminant.readDiscriminant hooks () (op (layout .Empty)))).2 =
    .error (.undefinedBehavior "UninhabitedEnumVariantRead(None)") := by decide
example : (run (Discriminant.writeDiscriminant hooks () 1 (layout (.Single 0)))).2 =
    .error (.undefinedBehavior "UninhabitedEnumVariantWritten(1)") := by decide
-- read queries the discriminant type before even inspecting Empty/Single.
example : (run (Discriminant.readDiscriminant hooks () (op (layout .Empty)))).1.trace =
    ["discriminantLayout"] := by decide
example : (run (Discriminant.writeDiscriminant hooks () 0 direct)).1.trace =
    ["discriminantLayout", "discriminantValue", "projectWrite", "writeScalar"] := by decide
private def deadDirect := layout (.Multiple tag .Direct 0 #[variant, variant true, variant])
example : (run (Discriminant.readDiscriminant hooks () (op deadDirect)) 2).2 =
    .error (.undefinedBehavior "UninhabitedEnumVariantRead(1)") := by decide
example : (run (Discriminant.writeDiscriminant hooks () 1 deadDirect)).1.trace = [] := by decide
-- Missing compiler tables fail explicitly before the tag load.
example : (run (Discriminant.readDiscriminant { hooks with
    discriminantLayout := fun _ _ => throw (.unsupported "missing discriminant type") }
    () (op direct))).2 = .error (.unsupported "missing discriminant type") := by decide

private def pointerScalar : Memory.Scalar AllocId :=
  .fromPointer RuntimeTargetDataLayout.default.base ⟨Size.ZERO, ⟨1, by decide⟩⟩
private def pointerTag : ABI.Scalar := .Initialized
  (value := .Pointer .ZERO) (validRange := ⟨0, BitVec.ofNat 128 (2^64-1)⟩)
private def pointerEnum (start : U128 := 0) :=
  layout (.Multiple pointerTag (.Niche 1 0 0 start) 0 #[variant, variant])
private def pointerHooks : DiscriminantHooks AllocId State Unit (TyAndLayout MIR.TyId) := {
  hooks with
  tagLayout := fun _ _ => pure { (layout (.Single 0) 11) with layout.size := Size.ofBytes 8 }
  readImmediate := fun _ _ => pure ⟨.scalar pointerScalar,
    { (layout (.Single 0) 11) with layout.size := Size.ofBytes 8 }⟩ }
example : (run (Discriminant.readDiscriminant pointerHooks () (op (pointerEnum)))).2 = .ok 1 := by decide
example : (run (Discriminant.readDiscriminant pointerHooks () (op (pointerEnum)))).1.trace =
    ["discriminantLayout", "projectRead", "mayBeNull"] := by decide
example : (run (Discriminant.readDiscriminant pointerHooks () (op (pointerEnum 1)))).2 =
    .error (.undefinedBehavior "InvalidTag(pointer niche)") := by decide
example : (run (Discriminant.readDiscriminant { pointerHooks with
    scalarMayBeNull := fun _ _ => pure true } () (op (pointerEnum)))).2 =
    .error (.undefinedBehavior "InvalidTag(pointer niche)") := by decide
example : (run (Discriminant.readDiscriminant pointerHooks () (op direct))).2 =
    .error (.undefinedBehavior "InvalidTag(pointer)") := by decide
-- Ordinary non-enum (including unions) has a single variant and no tag read.
example : (run (Discriminant.readDiscriminant hooks () (op (layout)))).2 = .ok 0 := by decide
example : (run (Discriminant.discriminantForVariant { hooks with
    discriminantValue := fun _ _ _ => pure none } () 0 0)).2 =
    .ok ⟨.scalar (scalar 0), layout (.Single 0) 10⟩ := by decide
example : (run (Discriminant.discriminantForVariant { hooks with
    discriminantValue := fun _ _ _ => pure none } () 0 1)).2 =
    .error (.invalidProgram "non-enum discriminant variant must be zero") := by decide

/-- Executable finite table consumed by source_compare.py. -/
def main : IO Unit := do
  for l in [direct, niche] do
    for n in List.range 256 do
      match (run (Discriminant.readDiscriminant hooks () (op l)) (UInt8.ofNat n)).2 with
      | .ok index => IO.println s!"ok:{index}"
      | .error (.undefinedBehavior _) => IO.println "invalid"
      | .error error => throw (IO.userError s!"unexpected: {repr error}")

private def signedByteLayout (id : Nat) : TyAndLayout MIR.TyId :=
  { (layout (.Single 0) id) with layout.backendRepr := .Scalar (.Union (value := .Int .I8 true)) }
private def signedHooks : DiscriminantHooks AllocId State Unit (TyAndLayout MIR.TyId) := {
  hooks with
  discriminantLayout := fun _ _ => pure { (layout (.Single 0) 10) with layout.size := Size.ofBytes 2 }
  tagLayout := fun _ _ => pure (signedByteLayout 11)
  readImmediate := fun _ _ => pure ⟨.scalar (scalar 255), signedByteLayout 11⟩
  variantForDiscriminant := fun _ _ bits =>
    if bits.toNat == 65535 then pure (some 1)
    else throw (.invalidProgram "signed tag was not sign extended") }
example : (run (Discriminant.readDiscriminant signedHooks () (op direct))).2 = .ok 1 := by decide
private def malformedNiche := layout (.Multiple tag (.Niche 1 0 1 255) 0 #[variant, variant])
example : (run (Discriminant.readDiscriminant hooks () (op malformedNiche)) 0).2 =
    .error (.undefinedBehavior "InvalidTag(untagged variant encoded in niche)") := by decide
