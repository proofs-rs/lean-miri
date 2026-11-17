import Miri.Interpreter.ProvenanceGC
import duplicate_prefix.GeneralBorrowLoop

namespace DuplicatePrefix.GeneralBorrowGcFrameProvenanceScalar
open Miri Miri.ABI Miri.Memory Miri.Interpreter
open ProvenanceGC
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Raw public scalar representations, independent of any GC outcome. -/
inductive ScalarForm : Scalar Provenance → Prop where
  | integer (value : ScalarInt) : ScalarForm (.fromScalarInt value)
  | pointer (layout : TargetDataLayout) (value : Pointer Provenance) : ScalarForm (.fromPointer layout value)

inductive ImmediateForm : Immediate Provenance → Prop where
  | uninit : ImmediateForm .uninit
  | scalar {value} : ScalarForm value → ImmediateForm (.scalar value)
  | pair {first second} : ScalarForm first → ScalarForm second → ImmediateForm (.scalarPair first second)

def Extends (before after : Roots) : Prop :=
  (∀ tag, tag ∈ before.tags → tag ∈ after.tags) ∧
  (∀ id, id ∈ before.allocations → id ∈ after.allocations)

theorem extends_refl (roots : Roots) : Extends roots roots := ⟨fun _ h => h,fun _ h => h⟩
theorem extends_trans {a b c : Roots} (first : Extends a b) (second : Extends b c) : Extends a c :=
  ⟨fun tag member => second.1 tag (first.1 tag member),fun id member => second.2 id (first.2 id member)⟩

theorem add_extends (roots : Roots) (id : Option AllocId) (tag : Option BorTag) : Extends roots (roots.add id tag) := by
  constructor
  · intro query member
    cases tag with
    | none => exact member
    | some tag =>
      change query ∈ (if roots.tags.contains tag then roots.tags else roots.tags.push tag)
      split
      · exact member
      · exact Array.mem_push.mpr (Or.inl member)
  · intro query member
    cases id with
    | none => exact member
    | some id =>
      change query ∈ (if roots.allocations.contains id then roots.allocations else roots.allocations.push id)
      split
      · exact member
      · exact Array.mem_push.mpr (Or.inl member)

theorem add_tag (roots : Roots) (id : Option AllocId) (tag : BorTag) : tag ∈ (roots.add id (some tag)).tags := by
  change tag ∈ (if roots.tags.contains tag then roots.tags else roots.tags.push tag)
  split
  next present => exact Array.contains_iff_mem.mp present
  next => exact Array.mem_push.mpr (Or.inr rfl)

theorem add_allocation (roots : Roots) (id : AllocId) (tag : Option BorTag) : id ∈ (roots.add (some id) tag).allocations := by
  change id ∈ (if roots.allocations.contains id then roots.allocations else roots.allocations.push id)
  split
  next present => exact Array.contains_iff_mem.mp present
  next => exact Array.mem_push.mpr (Or.inr rfl)

theorem provenance_extends (roots : Roots) (provenance : Provenance) : Extends roots (roots.provenance provenance) := by
  cases provenance with
  | concrete id tag => exact add_extends roots _ _
  | wildcard => exact extends_refl roots

theorem pointer_extends (roots : Roots) (pointer : Pointer (Option Provenance)) : Extends roots (roots.pointer pointer) := by
  cases found : pointer.provenance with
  | none => simpa only [Roots.pointer,found] using extends_refl roots
  | some provenance => simpa only [Roots.pointer,found] using provenance_extends roots provenance

theorem scalar_integer (roots : Roots) (value : ScalarInt) :
    roots.scalar (.fromScalarInt value) = .ok roots := by
  simp [bind,pure,Except.bind,Except.pure,Except.mapError,Except.map,Roots.scalar,Scalar.fromScalarInt,Scalar.toBitsOrPtrInternal,Miri.Memory.Scalar.size,ScalarInt.toBits,ScalarInt.size]

theorem scalar_pointer (roots : Roots) (layout : TargetDataLayout) (value : Pointer Provenance) :
    roots.scalar (.fromPointer layout value) = .ok (roots.strictPointer value) := by
  simp [bind,pure,Except.bind,Except.pure,Except.mapError,Except.map,Roots.scalar,Scalar.fromPointer,Scalar.toBitsOrPtrInternal,Miri.Memory.Scalar.size]

theorem scalar (roots : Roots) (value : Scalar Provenance) (raw : ScalarForm value) :
    ∃ after, roots.scalar value = .ok after ∧ Extends roots after := by
  cases raw with
  | integer value => exact ⟨roots,scalar_integer roots value,extends_refl roots⟩
  | pointer layout value => exact ⟨_,scalar_pointer roots layout value,provenance_extends roots value.provenance⟩

theorem immediate (roots : Roots) (value : Immediate Provenance) (raw : ImmediateForm value) :
    ∃ after, roots.immediate value = .ok after ∧ Extends roots after := by
  cases raw with
  | uninit => exact ⟨roots,rfl,extends_refl roots⟩
  | scalar raw => exact scalar roots _ raw
  | pair first second =>
    obtain ⟨middle,firstDone,firstExtends⟩ := scalar roots _ first
    obtain ⟨after,secondDone,secondExtends⟩ := scalar middle _ second
    refine ⟨after,?_,extends_trans firstExtends secondExtends⟩
    simp only [bind,Roots.immediate,firstDone,Except.bind,secondDone,Except.pure,pure]

/-- A concrete pointer in either word of an actual immediate is a root. The
other word has raw public representation, so no visitor-success field occurs. -/
inductive Carries (id : AllocId) (tag : BorTag) : Immediate Provenance → Prop where
  | scalar (layout : TargetDataLayout) (offset : Size) :
      Carries id tag (.scalar (.fromPointer layout (.new (.concrete id tag) offset)))
  | first (layout : TargetDataLayout) (offset : Size) (second : Scalar Provenance) :
      ScalarForm second → Carries id tag (.scalarPair (.fromPointer layout (.new (.concrete id tag) offset)) second)
  | second (layout : TargetDataLayout) (offset : Size) (first : Scalar Provenance) :
      ScalarForm first → Carries id tag (.scalarPair first (.fromPointer layout (.new (.concrete id tag) offset)))

theorem carries (roots : Roots) (id : AllocId) (tag : BorTag) (value : Immediate Provenance)
    (stored : Carries id tag value) :
    ∃ after, roots.immediate value = .ok after ∧ Extends roots after ∧ tag ∈ after.tags ∧ id ∈ after.allocations := by
  cases stored with
  | scalar layout offset =>
    exact ⟨_,scalar_pointer roots layout _,add_extends roots _ _,add_tag roots _ tag,add_allocation roots id _⟩
  | first layout offset second raw =>
    let middle := roots.add (some id) (some tag)
    obtain ⟨after,done,preserved⟩ := scalar middle second raw
    refine ⟨after,?_,extends_trans (add_extends roots _ _) preserved,preserved.1 tag (add_tag roots _ tag),preserved.2 id (add_allocation roots id _)⟩
    simp only [bind,Roots.immediate,scalar_pointer,Roots.strictPointer,Roots.provenance,Pointer.new,Except.bind,done,Except.pure,pure,middle]
  | second layout offset first raw =>
    obtain ⟨middle,done,preserved⟩ := scalar roots first raw
    refine ⟨_,?_,extends_trans preserved (add_extends middle _ _),add_tag middle _ tag,add_allocation middle id _⟩
    simp only [bind,Roots.immediate,done,Except.bind,scalar_pointer,Except.pure,pure]
    rfl

end DuplicatePrefix.GeneralBorrowGcFrameProvenanceScalar
