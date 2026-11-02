import duplicate_prefix.S03UninitProvenance
import duplicate_prefix.S04SyncSortPreserves

namespace DuplicatePrefix.S02SameDestinationAcceptedCopyPointerBounds
open Miri.ABI Miri.Memory
open ProvenanceCopy
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
variable {Prov : Type}

def Bounds (capacity : Nat) (state : ProvenanceMap Prov) : Prop :=
  ∀ entry ∈ state.ptrs, entry.1.bytes.toNat + 8 ≤ capacity

theorem list_preserves {α σ ε : Type} (entries : List α)
    (action : α → EStateM ε σ Unit) (P : σ → Prop)
    (step : ∀ entry ∈ entries, ∀ before after, P before →
      action entry before = .ok () after → P after)
    (before after : σ) (initial : P before)
    (ok : (forIn entries () fun entry _ => do action entry; pure (.yield ())) before = .ok () after) :
    P after := by
  induction entries generalizing before with
  | nil =>
    simp only [List.forIn_nil, Pure.pure, EStateM.pure] at ok
    cases ok
    exact initial
  | cons first rest ih =>
    simp only [List.forIn_cons, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure] at ok
    cases result : action first before with
    | error err state => simp [result] at ok
    | ok unit middle =>
      cases unit
      simp only [result] at ok
      exact ih (fun entry member => step entry (List.mem_cons_of_mem first member)) middle
        (step first (by simp) before middle initial result) ok

theorem array_preserves {α σ ε : Type} (entries : Array α)
    (action : α → EStateM ε σ Unit) (P : σ → Prop)
    (step : ∀ entry ∈ entries, ∀ before after, P before →
      action entry before = .ok () after → P after)
    (before after : σ) (initial : P before)
    (ok : (forIn entries () fun entry _ => do action entry; pure (.yield ())) before = .ok () after) :
    P after := by
  rcases entries with ⟨entries⟩
  exact list_preserves entries action P (fun entry member => step entry (by simpa using member))
    before after initial (by simpa using ok)

theorem insert_bounds (values : Array (Size × Prov)) (offset : Size) (prov : Prov) (capacity : Nat)
    (old : ∀ entry ∈ values, entry.1.bytes.toNat + 8 ≤ capacity)
    (new : offset.bytes.toNat + 8 ≤ capacity) :
    ∀ entry ∈ insertEntry values offset prov, entry.1.bytes.toNat + 8 ≤ capacity := by
  intro entry member
  unfold insertEntry at member
  unfold_provenance_at ".Miri.Memory.ProvenanceMap.insertEntry" at member
  apply S04SyncSortPreserves.qsort_all (fun entry : Size × Prov => entry.1.bytes.toNat + 8 ≤ capacity) _ _ ?_ entry member
  intro item hi
  rcases Array.mem_push.mp hi with previous | rfl
  · exact old item (Array.mem_filter.mp previous).1
  · exact new

theorem whole_action_bounds (range : AllocRange) (entry : Size × Prov) (capacity : Nat)
    (fits : entry.1.bytes.toNat + range.start.bytes.toNat < 2^64)
    (new : entry.1.bytes.toNat + range.start.bytes.toNat + 8 ≤ capacity)
    (before after : ProvenanceMap Prov) (old : Bounds capacity before)
    (ok : insert_whole_action range entry before = .ok () after) : Bounds capacity after := by
  unfold insert_whole_action at ok
  rw [shifted_copy_zero range entry.1 fits] at ok
  unfold checkedResult at ok
  unfold_provenance_at ".Miri.Memory.ProvenanceMap.checked" at ok
  simp only [Bind.bind, EStateM.bind, EStateM.get, EStateM.set] at ok
  cases ok
  apply insert_bounds _ _ _ _ old
  simpa [Size.ofBytes, UInt64.toNat_add, Nat.mod_eq_of_lt fits] using new

theorem fragment_action_bounds (range : AllocRange) (entry : Size × PointerFrag Prov)
    (capacity : Nat) (before after : ProvenanceMap Prov) (old : Bounds capacity before)
    (ok : insert_fragment_action range entry before = .ok () after) : Bounds capacity after := by
  unfold insert_fragment_action checkedResult at ok
  unfold_provenance_at ".Miri.Memory.ProvenanceMap.checked" at ok
  cases shifted : shiftedCopyOffset range 0 entry.1 <;>
    simp only [shifted, Bind.bind, EStateM.bind, EStateM.get, EStateM.set] at ok
  · cases ok
  · cases ok
    exact old

theorem whole_loop_bounds (range : AllocRange) (entries : Array (Size × Prov)) (capacity : Nat)
    (fits : ∀ entry ∈ entries, entry.1.bytes.toNat + range.start.bytes.toNat < 2^64)
    (new : ∀ entry ∈ entries, entry.1.bytes.toNat + range.start.bytes.toNat + 8 ≤ capacity)
    (before after : ProvenanceMap Prov) (old : Bounds capacity before)
    (ok : whole_loop range entries before = .ok () after) : Bounds capacity after := by
  apply array_preserves entries (insert_whole_action range) (Bounds capacity)
    (fun entry member => whole_action_bounds range entry capacity (fits entry member) (new entry member))
    before after old
  unfold whole_loop at ok
  change EStateM.bind (forIn entries () (fun entry _ => do
    insert_whole_action range entry; pure (.yield ()))) EStateM.pure before = .ok () after at ok
  rw [estate_bind_pure] at ok
  exact ok

theorem fragment_loop_bounds (range : AllocRange) (entries : Array (Size × PointerFrag Prov))
    (capacity : Nat) (before after : ProvenanceMap Prov) (old : Bounds capacity before)
    (ok : fragment_loop range entries before = .ok () after) : Bounds capacity after := by
  apply array_preserves entries (insert_fragment_action range) (Bounds capacity)
    (fun entry _ => fragment_action_bounds range entry capacity)
    (mkMap before.ptrs (some (before.byteFragments.getD #[]))) after old
  unfold fragment_loop at ok
  change EStateM.bind (forIn entries () (fun entry _ => do
    insert_fragment_action range entry; pure (.yield ()))) EStateM.pure
    (mkMap before.ptrs (some (before.byteFragments.getD #[]))) = .ok () after at ok
  rw [estate_bind_pure] at ok
  exact ok

/-- Complete pointers remain within the allocation after the actual one-copy
insertion. Fragment insertion preserves this property without asserting full
provenance-map well-formedness. -/
theorem apply_copy_once_pointer_bounds (copy : ProvenanceCopy Prov) (range : AllocRange)
    (capacity : Nat) (pointerCountFits : copy.ptrs.size < 2^64)
    (fragmentCountFits : copy.byteFragments.size < 2^64)
    (snapshot : ∀ entry ∈ copy.ptrs, entry.1.bytes.toNat + 8 ≤ range.size.bytes.toNat)
    (contained : range.start.bytes.toNat + range.size.bytes.toNat ≤ capacity)
    (noWrap : capacity < 2^64)
    (before after : ProvenanceMap Prov) (old : Bounds capacity before)
    (ok : ProvenanceMap.applyCopy copy range 1 before = .ok () after) :
    Bounds capacity after := by
  have fits : ∀ entry ∈ copy.ptrs, entry.1.bytes.toNat + range.start.bytes.toNat < 2^64 := by
    intro entry member
    have := snapshot entry member
    omega
  have new : ∀ entry ∈ copy.ptrs, entry.1.bytes.toNat + range.start.bytes.toNat + 8 ≤ capacity := by
    intro entry member
    have := snapshot entry member
    omega
  rw [apply_copy_once_reduces copy range pointerCountFits fragmentCountFits] at ok
  unfold apply_once at ok
  by_cases pe : copy.ptrs.isEmpty <;> by_cases fe : copy.byteFragments.isEmpty
  · simp only [pe, fe, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      Bind.bind, EStateM.bind, Pure.pure, EStateM.pure] at ok
    cases ok
    exact old
  · simp only [pe, fe, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq,
      ↓reduceIte, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure] at ok
    exact fragment_loop_bounds range copy.byteFragments capacity before after old ok
  · simp only [pe, fe, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq,
      ↓reduceIte, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure] at ok
    cases result : whole_loop range copy.ptrs before with
    | error err state => simp [result] at ok
    | ok value middle =>
      cases value
      simp only [result] at ok
      have equal : middle = after := by injection ok
      subst middle
      exact whole_loop_bounds range copy.ptrs capacity fits new before after old result
  · simp only [pe, fe, Bool.not_false, Bool.true_eq, ↓reduceIte,
      Bind.bind, EStateM.bind] at ok
    cases result : whole_loop range copy.ptrs before with
    | error err state => simp [result] at ok
    | ok value middle =>
      cases value
      simp only [result] at ok
      exact fragment_loop_bounds range copy.byteFragments capacity middle after
        (whole_loop_bounds range copy.ptrs capacity fits new before middle old result) ok

end DuplicatePrefix.S02SameDestinationAcceptedCopyPointerBounds
