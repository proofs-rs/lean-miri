import Miri.Memory.Allocation

open Miri.ABI Miri.Memory

private def must [Repr ε] (value : Except ε α) : IO α :=
  match value with | .ok x => pure x | .error e => throw (IO.userError (reprStr e))
private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def size (n : Nat) := Size.ofBytes (UInt64.ofNat n)
private def range (start count : Nat) := allocRange (size start) (size count)

def main : IO Unit := do
  let some id := AllocId.ofUInt64 37 | throw (IO.userError "fixture ID")
  let provenance ← must (CtfeProvenance.fromParts (id,true,true))
  for endian in [Endian.little, Endian.big] do
    let layout : TargetDataLayout := ⟨endian,.w64⟩
    let mask ← must ((InitMask.new (size 32) true).setRange (range 24 8) false)
    let source : Allocation CtfeProvenance Unit ← must
      (Allocation.fromCompilerImage (Array.replicate 32 7) Align.ONE .Not mask
        ProvenanceMap.new (size 8))
    let pointer := Scalar.fromPointer layout (Pointer.new provenance (size 3))
    let template ← must (Allocation.instantiateImmutable layout source #[(range 0 8,pointer)])
    let line : Scalar CtfeProvenance ← must (Scalar.fromUInt (BitVec.ofNat 128 0x12345678) (size 4))
    let column : Scalar CtfeProvenance ← must (Scalar.fromUInt (BitVec.ofNat 128 0xabcdef01) (size 4))
    let actual ← must (Allocation.instantiateImmutable layout template
      #[(range 16 4,line),(range 20 4,column)])
    check (actual.mutability == .Not) "constructed constant is mutable"
    check (actual.initializationMask == template.initializationMask)
      "construction changed initialization outside its fields"
    check (!(actual.getBytesStripProvenance layout (range 24 8)).isOk)
      "uninitialized padding became readable"
    let readPointer ← must (actual.readScalar layout (range 0 8) true)
    check (readPointer == pointer) "template pointer/provenance changed"
    let readLine ← must (actual.readScalar layout (range 16 4) false)
    let readColumn ← must (actual.readScalar layout (range 20 4) false)
    check (readLine == line && readColumn == column) "target-endian u32 fields differ"
    check ((← must (actual.getBytesUnchecked (range 8 8))) == Array.replicate 8 7)
      "untouched prefix padding changed"
    check ((← must (actual.getBytesUnchecked (range 24 8))) == Array.replicate 8 7)
      "untouched suffix padding changed"
    check ((← must (template.getBytesUnchecked (range 16 8))) == Array.replicate 8 7)
      "construction mutated the original template"
    check (!(Allocation.instantiateImmutable layout template #[(range 31 4,line)]).isOk)
      "out-of-bounds field accepted"
    match Allocation.writeScalar layout (range 16 4) line actual with
    | .error _ _ => pure ()
    | .ok _ _ => throw (IO.userError "constructed constant accepts a guest write")
    let mutable : Allocation CtfeProvenance Unit ← must
      (Allocation.fromBytes (Array.replicate 32 7) Align.ONE .Mut)
    check (!(Allocation.instantiateImmutable layout mutable #[]).isOk) "mutable template accepted"
  IO.println "immutable templates: endian fields, pointer/provenance, padding, isolation and write rejection PASS"
