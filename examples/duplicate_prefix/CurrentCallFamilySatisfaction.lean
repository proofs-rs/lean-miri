import duplicate_prefix.CurrentCallPointwiseSpatialCover

/-! Current reference-family satisfaction for the fixed interpreter state.
This defines current ownership, not Rust validity or a history equivalence.
Family identity is assigned explicitly; equality of pointer bits never assigns
or merges identities. Physical representation and fragment composition remain
separate obligations. All laws below keep the actual protector table fixed. -/
namespace DuplicatePrefix.CurrentCallFamilySatisfaction
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources CandidateFreezeContentResources
open CurrentCallResourceNormalization CurrentCallSpatialCover
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

/-- Optional raw provenance is preserved. Integer/address encoding has no
provenance and is represented by a wildcard family at the SAME address.
This relation does not assert that a normalization operation has executed. -/
def Represents (raw : Pointer (Option Provenance)) (value : Pointer Provenance) : Prop :=
  raw.offset=value.offset ∧ match raw.provenance with
    | some provenance=>value.provenance=provenance
    | none=>value.provenance=.wildcard

structure Payload where
  allocation : AllocId
  value : Pointer Provenance

structure Assignment (actual : Array (Pointer (Option Provenance))) where
  families : Array Payload
  references : Array (Option Nat)
  size : references.size=actual.size
  coherent : ∀ (occurrence family : Nat),references[occurrence]?=some (some family) →
    ∃ (payload : Payload),families[family]?=some payload ∧
      ∃ (raw : Pointer (Option Provenance)),actual[occurrence]?=some raw ∧ Represents raw payload.value

namespace Assignment
variable {actual : Array (Pointer (Option Provenance))}

def Binds (a : Assignment actual) (occurrence : Nat) (family : Family) : Prop :=
  a.families[family.slot]?=some ⟨family.allocation,family.value⟩ ∧
  a.references[occurrence]?=some (some family.slot)

theorem actual_value (a : Assignment actual) {occurrence family} (bound : a.Binds occurrence family) :
    ∃ (raw : Pointer (Option Provenance)),actual[occurrence]?=some raw ∧ Represents raw family.value := by
  obtain ⟨payload,present,raw,found,represented⟩:=a.coherent occurrence family.slot bound.2
  have same : payload=⟨family.allocation,family.value⟩:=Option.some.inj (present.symm.trans bound.1)
  subst payload
  exact ⟨raw,found,represented⟩

theorem same_family (a : Assignment actual) {first second : Family}
    (firstAt : a.families[first.slot]?=some ⟨first.allocation,first.value⟩)
    (secondAt : a.families[second.slot]?=some ⟨second.allocation,second.value⟩)
    (same : first.slot=second.slot) : first.allocation=second.allocation ∧ first.value=second.value := by
  rw [same] at firstAt
  have equal:=Option.some.inj (firstAt.symm.trans secondAt)
  exact ⟨congrArg Payload.allocation equal,congrArg Payload.value equal⟩

/-- Assignment formation for ONE actual plain copy. The new occurrence has
its actual copied bits; its reference keeps the SAME source family ID. -/
def copy (a : Assignment actual) (family : Family) (source : Nat) (bound : a.Binds source family)
    (raw : Pointer (Option Provenance)) (copied : actual[source]?=some raw) : Assignment (actual.push raw) where
  families:=a.families
  references:=a.references.push (some family.slot)
  size:=by simp [Array.size_push,a.size]
  coherent:=by
    intro occurrence identity found
    by_cases old : occurrence<a.references.size
    · have original : a.references[occurrence]?=some (some identity) := by simpa [Array.getElem?_push,Nat.ne_of_lt old] using found
      obtain ⟨payload,present,value,stored,represented⟩:=a.coherent occurrence identity original
      refine ⟨payload,present,value,?_,represented⟩
      have before : occurrence<actual.size := by rwa [←a.size]
      simpa [Array.getElem?_push,Nat.ne_of_lt before] using stored
    · have atEnd : occurrence=a.references.size := by
        have limit:=(Array.getElem?_eq_some_iff.mp found).1
        simp [Array.size_push] at limit
        omega
      subst occurrence
      have same : identity=family.slot := by simpa [Array.getElem?_push,Option.some.injEq] using found.symm
      subst identity
      obtain ⟨value,stored,represented⟩:=actual_value a bound
      have equal : value=raw:=Option.some.inj (stored.symm.trans copied)
      subst value
      exact ⟨⟨family.allocation,family.value⟩,bound.1,raw,by rw [a.size,Array.getElem?_push];simp,represented⟩

theorem copied_family (a : Assignment actual) (family : Family) (source : Nat) (bound : a.Binds source family)
    (raw : Pointer (Option Provenance)) (copied : actual[source]?=some raw) :
    (copy a family source bound raw copied).Binds actual.size family := by
  refine ⟨bound.1,?_⟩
  change (a.references.push (some family.slot))[actual.size]?=some (some family.slot)
  rw [←a.size,Array.getElem?_push]
  simp

/-- A REAL retag producer may install its returned payload under this fresh
semantic ID. This formation law grants no ownership and asserts no transition
or protector preservation; those use that producer's actual resource laws. -/
def retag (a : Assignment actual) (payload : Payload) (raw : Pointer (Option Provenance))
    (represented : Represents raw payload.value) : Assignment (actual.push raw) where
  families:=a.families.push payload
  references:=a.references.push (some a.families.size)
  size:=by simp [Array.size_push,a.size]
  coherent:=by
    intro occurrence identity found
    by_cases old : occurrence<a.references.size
    · have original : a.references[occurrence]?=some (some identity) := by simpa [Array.getElem?_push,Nat.ne_of_lt old] using found
      obtain ⟨value,present,bits,stored,binding⟩:=a.coherent occurrence identity original
      have familyBound:=(Array.getElem?_eq_some_iff.mp present).1
      have occurrenceBound : occurrence<actual.size := by rwa [←a.size]
      exact ⟨value,by simpa [Array.getElem?_push,Nat.ne_of_lt familyBound] using present,
        bits,by simpa [Array.getElem?_push,Nat.ne_of_lt occurrenceBound] using stored,binding⟩
    · have atEnd : occurrence=a.references.size := by
        have limit:=(Array.getElem?_eq_some_iff.mp found).1
        simp [Array.size_push] at limit
        omega
      subst occurrence
      have same : identity=a.families.size := by simpa [Array.getElem?_push,Option.some.injEq] using found.symm
      subst identity
      exact ⟨payload,by simp,raw,by rw [a.size,Array.getElem?_push];simp,represented⟩

def newFamily (a : Assignment actual) (payload : Payload) : Family := ⟨a.families.size,payload.allocation,payload.value⟩

theorem retagged_family (a : Assignment actual) (payload : Payload) (raw : Pointer (Option Provenance))
    (represented : Represents raw payload.value) :
    (retag a payload raw represented).Binds actual.size (newFamily a payload) := by
  constructor
  · change (a.families.push payload)[a.families.size]?=some payload
    rw [Array.getElem?_push]
    simp
  · change (a.references.push (some a.families.size))[actual.size]?=some (some a.families.size)
    rw [←a.size,Array.getElem?_push]
    simp

theorem old_family_after_retag (a : Assignment actual) (payload : Payload) (raw : Pointer (Option Provenance))
    (represented : Represents raw payload.value) {family : Nat} {old : Payload}
    (present : a.families[family]?=some old) :
    (retag a payload raw represented).families[family]?=some old ∧ family≠(newFamily a payload).slot := by
  have bound:=(Array.getElem?_eq_some_iff.mp present).1
  exact ⟨by simpa [retag,Array.getElem?_push,Nat.ne_of_lt bound] using present,Nat.ne_of_lt bound⟩

/-- Appended copy/retag occurrences leave every existing reference assignment
and family payload intact, in particular the original return destination. -/
theorem old_reference_after_copy (a : Assignment actual) (family : Family) (source : Nat) (bound : a.Binds source family)
    (raw : Pointer (Option Provenance)) (copied : actual[source]?=some raw) {occurrence oldFamily}
    (old : a.Binds occurrence oldFamily) : (copy a family source bound raw copied).Binds occurrence oldFamily := by
  have bound:=(Array.getElem?_eq_some_iff.mp old.2).1
  refine ⟨old.1,?_⟩
  change (a.references.push (some family.slot))[occurrence]?=some (some oldFamily.slot)
  rw [Array.getElem?_push,ite_eq_right (Nat.ne_of_lt bound)]
  exact old.2

theorem old_reference_after_retag (a : Assignment actual) (payload : Payload) (raw : Pointer (Option Provenance))
    (represented : Represents raw payload.value) {occurrence family} (old : a.Binds occurrence family) :
    (retag a payload raw represented).Binds occurrence family := by
  have bound:=(Array.getElem?_eq_some_iff.mp old.2).1
  refine ⟨(old_family_after_retag a payload raw represented old.1).1,?_⟩
  change (a.references.push (some a.families.size))[occurrence]?=some (some family.slot)
  rw [Array.getElem?_push,ite_eq_right (Nat.ne_of_lt bound)]
  exact old.2

end Assignment

/-- Current exclusive content satisfaction. The SAME family/value is fixed
outside per-byte grant/chain choices. ALL actual retained protector guards are
decoded in Carries, including nodes absent from a declared content fragment. -/
def Satisfies (tracker : MachineHooks.BorrowState) (family : Family)
    (allocation : Allocation Provenance BorrowTree) (footprint : Byte→Prop) : Prop :=
  ∀ byte,footprint byte → byte.1=family.allocation ∧ ∃ grant,
    ∃ chain : CurrentCallSupportChain.Chain allocation.extra grant,
      PointerBinds allocation (family.at grant) ∧
      CurrentCallSupportChain.Carries allocation tracker.global.protectedTags chain byte.2 .exclusive

theorem restrict {tracker family allocation P Q}
    (owned : Satisfies tracker family allocation P) (inside : ∀ byte,Q byte→P byte) :
    Satisfies tracker family allocation Q := fun byte hit=>owned byte (inside byte hit)

theorem split_union {tracker family allocation P Q} :
    Satisfies tracker family allocation (fun byte=>P byte∨Q byte) ↔
      Satisfies tracker family allocation P ∧ Satisfies tracker family allocation Q := by
  constructor
  · intro owned
    exact ⟨restrict owned (fun _ hit=>.inl hit),restrict owned (fun _ hit=>.inr hit)⟩
  · rintro ⟨left,right⟩ byte (hit|hit)
    · exact left byte hit
    · exact right byte hit

theorem split_window {tracker family allocation offset left right} :
    Satisfies tracker family allocation (Window family.allocation offset (left+right)) ↔
      Satisfies tracker family allocation (Window family.allocation offset left) ∧
      Satisfies tracker family allocation (Window family.allocation (offset+left) right) := by
  have windows : Window family.allocation offset (left+right)=
      (fun byte=>Window family.allocation offset left byte∨Window family.allocation (offset+left) right byte) := by
    funext byte
    apply propext
    simp only [Window]
    constructor
    · intro hit
      by_cases before : byte.2<offset+left
      · exact .inl ⟨hit.1,hit.2.1,before⟩
      · exact .inr ⟨hit.1,by omega,by have h:=hit.2;omega⟩
    · rintro (hit|hit) <;> exact ⟨hit.1,by have h:=hit.2;omega,by have h:=hit.2;omega⟩
  rw [windows]
  exact split_union

/-- Copy preserves the SAME ownership proof and hence the SAME available
per-byte witnesses; no new origin choice is made by assignment formation. -/
theorem copy_preserves {actual tracker family allocation footprint source}
    (a : Assignment actual) (bound : a.Binds source family)
    (raw : Pointer (Option Provenance)) (copied : actual[source]?=some raw)
    (owned : Satisfies tracker family allocation footprint) :
    (a.copy family source bound raw copied).Binds actual.size family ∧
      Satisfies tracker family allocation footprint := ⟨a.copied_family family source bound raw copied,owned⟩

/-- Adding composable declared contents cannot omit a current protector:
Satisfies still checks the same actual nodes/table independently of fragments. -/
theorem ambient {tracker family allocation footprint F G}
    (owned : Satisfies tracker family allocation footprint) (together : Composable F G) :
    Valid (union F G) ∧ Satisfies tracker family allocation footprint := ⟨union_valid F G together,owned⟩

def reslot (family : Family) (identity : Nat) : Family := {family with slot:=identity}

theorem reslot_satisfies {tracker family allocation footprint} (identity : Nat) :
    Satisfies tracker (reslot family identity) allocation footprint ↔ Satisfies tracker family allocation footprint := Iff.rfl

def reslot_role {before tracker ctx mode offset length}
    (role : RoleCover before tracker ctx mode offset length) (identity : Nat) : RoleCover before tracker ctx mode offset length where
  family:=reslot role.family identity
  backing:=role.backing
  backingAt:=role.backingAt
  id:=role.id
  covered:=role.covered
  roles:=fun i overlap=>let old:=role.roles i overlap;⟨old.grant,old.binding,old.issued,old.available⟩

theorem to_chained {tracker family allocation offset length}
    (owned : Satisfies tracker family allocation (Window family.allocation offset length)) :
    CurrentCallPointwiseSpatialCover.Chained tracker family allocation .mut offset length := by
  intro byte hit
  exact (owned byte hit).2

theorem to_chained_return {tracker family allocation offset}
    (owned : Satisfies tracker family allocation (Window family.allocation offset 1)) :
    CurrentCallPointwiseSpatialCover.Chained tracker family allocation .ret offset 1 := by
  intro byte hit
  exact (owned byte hit).2

/-- The selected per-byte witness accounts for EVERY actual decoded guard,
not only nodes or owners mentioned by any declared fragment/occurrence table. -/
theorem actual_guards {tracker family allocation footprint byte}
    (owned : Satisfies tracker family allocation footprint) (hit : footprint byte) :
    ∃ grant,∃ chain : CurrentCallSupportChain.Chain allocation.extra grant,
      PointerBinds allocation (family.at grant) ∧
      ∀ segment∈allocation.extra.locations.entries.toList,segment.range.start.toNat≤byte.2 → byte.2<segment.range.stop.toNat →
      ∀ index node,allocation.extra.nodes.get index=some node →
        Clash (guard (denote (RawState segment.data index node) (tracker.global.protectedTags.contains node.tag))) .exclusive → chain.Member index := by
  obtain ⟨_,grant,chain,binding,support⟩:=owned byte hit
  exact ⟨grant,chain,binding,fun segment member lower upper index node present clash=>(support segment member lower upper index node present).2 clash⟩

/-- An actual copy preserves a supplied SAME per-byte witness literally.
There is no new origin selection for the copied occurrence. -/
theorem copy_same_witness {actual family allocation source byte grant} {tracker : MachineHooks.BorrowState}
    (a : Assignment actual) (bound : a.Binds source family)
    (raw : Pointer (Option Provenance)) (copied : actual[source]?=some raw)
    (chain : CurrentCallSupportChain.Chain allocation.extra grant)
    (binding : PointerBinds allocation (family.at grant))
    (support : CurrentCallSupportChain.Carries allocation tracker.global.protectedTags chain byte .exclusive) :
    (a.copy family source bound raw copied).Binds actual.size family ∧
      PointerBinds allocation (family.at grant) ∧
      CurrentCallSupportChain.Carries allocation tracker.global.protectedTags chain byte .exclusive :=
  ⟨a.copied_family family source bound raw copied,binding,support⟩


end
end DuplicatePrefix.CurrentCallFamilySatisfaction
