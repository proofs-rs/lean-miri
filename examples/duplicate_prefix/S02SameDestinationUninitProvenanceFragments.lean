import duplicate_prefix.S02SameDestinationUninitProvenanceInput
import duplicate_prefix.S04SyncSortPreserves
import duplicate_prefix.S04ReturnProvenanceClear

namespace DuplicatePrefix.S02SameDestinationUninitProvenanceFragments
open Miri.ABI Miri.Memory
open ProvenanceCopy
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
variable {Prov : Type}

theorem qsort_size {α : Type} (values : Array α) (lt : α → α → Bool) :
    (values.qsort lt).size = values.size := by
  unfold Array.qsort
  split
  · rfl
  · simp

theorem insert_size {α : Type} (values : Array (Size × α)) (offset : Size) (value : α) :
    (insertEntry values offset value).size ≤ values.size + 1 := by
  unfold insertEntry
  unfold_provenance ".Miri.Memory.ProvenanceMap.insertEntry"
  rw [qsort_size, Array.size_push]
  have := Array.size_filter_le (p := fun entry : Size × α => entry.1.bytes != offset.bytes) (xs := values)
  omega

theorem insert_all {α : Type} (P : Size × α → Prop) (values : Array (Size × α)) (entry : Size × α)
    (old : ∀ item ∈ values, P item) (new : P entry) :
    ∀ item ∈ insertEntry values entry.1 entry.2, P item := by
  unfold insertEntry
  unfold_provenance ".Miri.Memory.ProvenanceMap.insertEntry"
  apply S04SyncSortPreserves.qsort_all
  intro item member
  rcases Array.mem_push.mp member with previous | rfl
  · exact old item (Array.mem_filter.mp previous).1
  · exact new

theorem fold_insert_all {α : Type} (P : Size × α → Prop)
    (entries values : Array (Size × α)) (old : ∀ item ∈ values, P item)
    (new : ∀ item ∈ entries, P item) :
    ∀ item ∈ entries.foldl (fun acc entry => insertEntry acc entry.1 entry.2) values, P item := by
  apply Array.foldl_induction (motive := fun _ values => ∀ item ∈ values, P item)
  · exact old
  · intro index values ih
    exact insert_all P values entries[index] ih (new entries[index] (Array.getElem_mem index.isLt))

theorem fold_insert_size {α : Type} (entries values : Array (Size × α)) :
    (entries.foldl (fun acc entry => insertEntry acc entry.1 entry.2) values).size ≤ values.size + entries.size := by
  rcases entries with ⟨entries⟩
  rw [← Array.foldl_toList]
  change (entries.foldl (fun acc entry => insertEntry acc entry.1 entry.2) values).size ≤ values.size + entries.length
  induction entries generalizing values with
  | nil => simp
  | cons first rest ih =>
    simp only [List.foldl_cons, List.length_cons]
    have bound := ih (insertEntry values first.1 first.2)
    have one := insert_size values first.1 first.2
    omega

theorem selected_size (inRange : Size → Bool) (position : Size) (prov : Prov)
    (data : Array UInt8) (available : position.bytes.toNat + 8 ≤ data.size) :
    (selected_pointer_fragments inRange position prov data available).size ≤ 8 := by
  unfold selected_pointer_fragments
  simp only [List.size_toArray]
  have := List.length_filter_le (fun entry : Size × PointerFrag Prov => inRange entry.1) ((List.range 8).map (pointer_fragment_entry position prov (pointer_payload position data available)))
  simpa using this

/-- Every inserted byte comes from an original complete pointer intersecting
this clear range, or from an old byte fragment. -/
def Origin (original : ProvenanceMap Prov) (entries : Array (Size × Prov))
    (fragment : Size × PointerFrag Prov) : Prop :=
  fragment ∈ original.byteFragments.getD #[] ∨
    ∃ pointer ∈ entries, pointer.1.bytes.toNat ≤ fragment.1.bytes.toNat ∧
      fragment.1.bytes.toNat < pointer.1.bytes.toNat + 8

theorem boundary_effect (original : ProvenanceMap Prov) (entries : Array (Size × Prov))
    (inRange : Size → Bool) (position : Size) (prov : Prov) (data : Array UInt8)
    (available : position.bytes.toNat + 8 ≤ data.size)
    (storageFits : data.size < 18446744073709551616)
    (member : (position, prov) ∈ entries)
    (before after : ProvenanceMap Prov)
    (old : ∀ fragment ∈ before.byteFragments.getD #[], Origin original entries fragment)
    (ok : clear_boundary_action inRange position prov data before = .ok () after) :
    after.ptrs = before.ptrs ∧
    (∀ fragment ∈ after.byteFragments.getD #[], Origin original entries fragment) ∧
    (after.byteFragments.getD #[]).size ≤ (before.byteFragments.getD #[]).size + 8 := by
  unfold clear_boundary_action at ok
  rw [pointer_fragments_exact inRange position prov data available storageFits] at ok
  unfold checkedResult at ok
  unfold_provenance_at ".Miri.Memory.ProvenanceMap.checked" at ok
  simp only [Bind.bind, EStateM.bind, EStateM.get, EStateM.set] at ok
  cases ok
  refine ⟨rfl, ?_, ?_⟩
  · apply fold_insert_all _ _ _ old
    intro fragment fragMember
    have geometry := selected_pointer_fragment_bounds inRange position prov data available storageFits fragment fragMember
    exact Or.inr ⟨(position,prov),member,geometry.1,geometry.2.1⟩
  · have bound := fold_insert_size (selected_pointer_fragments inRange position prov data available)
      (before.byteFragments.getD #[])
    have count := selected_size inRange position prov data available
    exact Nat.le_trans bound (by omega)

end DuplicatePrefix.S02SameDestinationUninitProvenanceFragments
