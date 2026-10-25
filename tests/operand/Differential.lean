import Miri.Interpreter.Operand

open Miri.Memory Miri.ABI Miri.Interpreter

def showScalar (s : Scalar CtfeProvenance) : String :=
  match s.toBitsOrPtrInternal s.size with
  | .ok (.bits bits) => s!"i{bits.toNat}"
  | .ok (.pointer p) => s!"p{p.offset.bytes}"
  | .error _ => "error"

def showImm : Immediate CtfeProvenance → String
  | .scalar s => showScalar s
  | .scalarPair a b => s!"{showScalar a},{showScalar b}"
  | .uninit => "u"

def ghost (slot : LocalState CtfeProvenance String) : String :=
  match slot.asMplaceOrImmGhost with
  | none => "dead"
  | some (.inl (ptr, metadata)) => s!"mem{ptr.offset.bytes}:{metadata.hasMeta}"
  | some (.inr value) => showImm value

def main : IO Unit := do
  let some id := AllocId.ofUInt64 1 | throw (IO.userError "id")
  let .ok prov := CtfeProvenance.fromAllocId id | throw (IO.userError "provenance")
  let m : MemPlace CtfeProvenance := ⟨⟨Size.ofBytes 17, some prov⟩,
    .metadata (Scalar.fromScalarInt (ScalarInt.ofUInt32 99)), none⟩
  let values : Array (LocalValue CtfeProvenance) := #[.dead, .live (.immediate .uninit),
    .live (.immediate (.scalar (Scalar.fromScalarInt (ScalarInt.ofUInt8 7)))), .live (.indirect m)]
  for (value, index) in values.toList.zipIdx do
    for cached in [false, true] do
      let slot : LocalState CtfeProvenance String := ⟨value, if cached then some "layout" else none⟩
      IO.println s!"L {index} {cached} {ghost slot} {slot.access.isOk}"
      let replacement := Operand.immediate (.scalar (Scalar.fromScalarInt (ScalarInt.ofUInt8 11)))
      let changed := match slot.modify fun _ => replacement with | .ok next => next | .error _ => slot
      IO.println s!"W {ghost changed} {changed.layout.isSome}"
      let initialized := changed.makeLiveUninit
      IO.println s!"U {ghost initialized} {initialized.layout.isSome}"
  let mapped := m.mapProvenance CtfeProvenance.asImmutable
  let some ptrProv := mapped.ptr.provenance | throw (IO.userError "missing provenance")
  IO.println s!"MAP {ptrProv.immutable} {mapped.metadata.hasMeta} {mapped.misaligned.isSome}"
  let .ok reference := mapped.toRef ⟨.little, .w64⟩ | throw (IO.userError "toRef")
  IO.println s!"REF {showImm reference}"
