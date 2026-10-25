import Miri.Interpreter.Immediate

open Miri.Memory Miri.ABI Miri.Interpreter

def normal {α : Type} (value : Except α String) : String :=
  match value with | .ok value => value | .error _ => "internal"

def scalar [PointerProvenance Prov] (s : Scalar Prov) : String :=
  match s.toBitsOrPtrInternal s.size with
  | .ok (.bits bits) => s!"i{s.size.bytes}:{bits.toNat}"
  | .ok (.pointer ptr) => s!"p{s.size.bytes}:{ptr.offset.bytes}"
  | .error _ => "internal"

def snapshot [PointerProvenance Prov] : Immediate Prov → String
  | .scalar s => scalar s
  | .scalarPair a b => s!"({scalar a},{scalar b} )"
  | .uninit => "u"

def inspect [PointerProvenance Prov] (tag : String) (width index : Nat) (value : Immediate Prov) : IO Unit := do
  IO.println s!"I {tag} {width} {index} {snapshot value} {value.hasProvenance}"
  IO.println s!"S {normal (value.toScalar.map scalar)}"
  IO.println s!"N {normal (value.toScalarInt.map fun value => s!"{value.size.bytes}:{value.data.toNat}")}"
  IO.println s!"P {normal (value.toScalarPair.map fun (a,b) => s!"{scalar a},{scalar b}")}"
  IO.println s!"M {normal (value.toScalarAndMeta.map fun (a,b) => s!"{scalar a},{match b with | .none => "n" | .metadata b => scalar b}")}"
  match Immediate.clearProvenance value with
  | .ok _ state => IO.println s!"C true {snapshot state}"
  | .error _ state => IO.println s!"C false {snapshot state}"

def fixtures (prov : Prov) (layout : TargetDataLayout) : Except ImmediateError (Array (Immediate Prov)) := do
  let ptr : Pointer (Option Prov) := ⟨Size.ofBytes 17, some prov⟩
  let noPtr : Pointer (Option Prov) := Pointer.withoutProvenance 23
  let metadata := Scalar.fromScalarInt (ScalarInt.ofUInt32 99)
  return #[.uninit, .scalar (Scalar.fromScalarInt (ScalarInt.ofUInt8 7)),
    ← Immediate.newPointerWithMeta ptr .none layout,
    ← Immediate.newPointerWithMeta ptr (.metadata metadata) layout,
    ← Immediate.newSlice ptr 8 layout, ← Immediate.newSlice noPtr 10 layout,
    ← Immediate.newDynTrait ptr noPtr layout,
    .scalarPair (Scalar.fromScalarInt (ScalarInt.ofUInt8 1)) (Scalar.fromPointer layout ⟨Size.ofBytes 29, prov⟩)]

def run [PointerProvenance Prov] (tag : String) (prov : Prov) : IO Unit := do
  for width in [PointerWidth.w16, .w32, .w64] do
    let layout : TargetDataLayout := ⟨.little, width⟩
    match fixtures prov layout with
    | .error _ => throw (IO.userError "invalid fixture")
    | .ok values =>
      for (value, index) in values.toList.zipIdx do
        inspect tag width.bits.toNat index value

def main : IO Unit := do
  match AllocId.ofUInt64 1 with
  | none => throw (IO.userError "invalid fixture id")
  | some id =>
    match CtfeProvenance.fromAllocId id with
    | .error _ => throw (IO.userError "invalid CTFE fixture")
    | .ok prov => run "ctfe" prov
  run "addr" Provenance.wildcard
