import duplicate_prefix.GeneralBorrowOwnership
import Miri.TreeBorrows.GlobalState
namespace DuplicatePrefix.GeneralBorrowRelease
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowPermissions
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

theorem contains_iff_entry (tags : ProtectedTags) (tag : BorTag) :
    tags.contains tag = true ↔ ∃ entry ∈ tags.entries, entry.1 = tag := by
  simp [ProtectedTags.contains,ProtectedTags.get,Array.find?_isSome]

theorem remove_weakens (tags : ProtectedTags) (removed query : BorTag)
    (still : (tags.remove removed).contains query = true) : tags.contains query = true := by
  apply (contains_iff_entry tags query).mpr
  obtain ⟨entry,member,same⟩ := (contains_iff_entry (tags.remove removed) query).mp still
  exact ⟨entry,(Array.mem_filter.mp member).1,same⟩

theorem remove_fold_weakens (rows : List (AllocId × BorTag)) (tags : ProtectedTags) (query : BorTag)
    (still : (rows.foldl (fun tags row => tags.remove row.2) tags).contains query = true) :
    tags.contains query = true := by
  induction rows generalizing tags with
  | nil => exact still
  | cons row rest ih =>
    exact remove_weakens tags row.2 query (ih (tags.remove row.2) still)

theorem end_call_weakens (global : GlobalState) (frame : FrameState) (query : BorTag)
    (still : (global.endCall frame).protectedTags.contains query = true) :
    global.protectedTags.contains query = true := by
  apply remove_fold_weakens frame.protectedTags.toList global.protectedTags query
  simpa only [GlobalState.endCall,Array.foldl_toList] using still

theorem required_weakens (state : LocationState) (writable : Bool) (related : AccessRelatedness)
    (before after : Bool) (weaken : after = true → before = true)
    (owned : Required state writable related before) : Required state writable related after := by
  cases writable with
  | true => exact owned_release state related before after weaken owned
  | false =>
    cases related with
    | LocalAccess => exact owned
    | ForeignAccess => exact owned_release state .ForeignAccess before after weaken owned

/-- A released shared leaf may become foreign to its mutable parent. -/
theorem readable_becomes_foreign (state : LocationState) (writable held : Bool)
    (readable : Required state false .LocalAccess held) : Required state writable .ForeignAccess false := by
  have possible := readable.1
  cases writable <;> exact ⟨possible,Or.inl rfl⟩
theorem remove_fold_absent (rows : List (AllocId × BorTag)) (tags : ProtectedTags) (query : BorTag)
    (absent : tags.contains query = false) :
    (rows.foldl (fun tags row => tags.remove row.2) tags).contains query = false := by
  cases final : (rows.foldl (fun tags row => tags.remove row.2) tags).contains query with
  | false => rfl
  | true =>
    have contradiction := remove_fold_weakens rows tags query final
    rw [absent] at contradiction
    cases contradiction

theorem remove_fold_owned (rows : List (AllocId × BorTag)) (tags : ProtectedTags)
    (allocation : AllocId) (query : BorTag) (owned : (allocation,query) ∈ rows) :
    (rows.foldl (fun tags row => tags.remove row.2) tags).contains query = false := by
  induction rows generalizing tags with
  | nil => simp at owned
  | cons row rest ih =>
    rcases List.mem_cons.mp owned with same | later
    · subst row
      exact remove_fold_absent rest (tags.remove query) query (by simp [ProtectedTags.contains])
    · exact ih (tags.remove row.2) later

theorem end_call_owned_absent (global : GlobalState) (frame : FrameState)
    (allocation : AllocId) (query : BorTag) (owned : (allocation,query) ∈ frame.protectedTags.toList) :
    (global.endCall frame).protectedTags.contains query = false := by
  have absent := remove_fold_owned frame.protectedTags.toList global.protectedTags allocation query owned
  simpa only [GlobalState.endCall,Array.foldl_toList] using absent

theorem pointwise_weaken (tree : NormalTreeState) (writable : Nat → Bool) (related : Nat → AccessRelatedness)
    (owned : GeneralBorrowOwnership.Pointwise tree writable related) (protections : List Nat)
    (weaken : ∀ index, protections.contains index = true → tree.protectedNodes.contains index = true) :
    GeneralBorrowOwnership.Pointwise {tree with protectedNodes := protections} writable related := by
  intro index valid
  obtain ⟨state,present,permitted⟩ := owned index valid
  exact ⟨state,present,required_weakens state (writable index) (related index) _ _ (weaken index) permitted⟩

/-- After the real global removal, a temporary shared leaf can be excluded
from the mutable parent's local path. Other nodes retain their strength. -/
theorem pointwise_release_shared (tree : NormalTreeState) (writable : Nat → Bool)
    (before after : Nat → AccessRelatedness) (child : Nat)
    (owned : GeneralBorrowOwnership.Pointwise tree writable before) (protections : List Nat)
    (weaken : ∀ index, protections.contains index = true → tree.protectedNodes.contains index = true)
    (readOnly : writable child = false) (localChild : before child = .LocalAccess)
    (foreignChild : after child = .ForeignAccess) (released : protections.contains child = false)
    (unchanged : ∀ index, index ≠ child → after index = before index) :
    GeneralBorrowOwnership.Pointwise {tree with protectedNodes := protections} writable after := by
  intro index valid
  obtain ⟨state,present,permitted⟩ := owned index valid
  refine ⟨state,present,?_⟩
  by_cases same : index = child
  · subst index
    rw [foreignChild,released]
    apply readable_becomes_foreign state (writable child) (tree.protectedNodes.contains child)
    simpa only [readOnly,localChild] using permitted
  · rw [unchanged index same]
    exact required_weakens state (writable index) (before index) _ _ (weaken index) permitted

end DuplicatePrefix.GeneralBorrowRelease

open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowRelease." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved generic release dependency {dependency}"
