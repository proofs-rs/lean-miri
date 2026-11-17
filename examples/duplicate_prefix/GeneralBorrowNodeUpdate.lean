import duplicate_prefix.GeneralBorrowExposure
namespace DuplicatePrefix.GeneralBorrowNodeUpdate
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposure
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

theorem index_injective (left right : UniIndex) (same : left.toNat = right.toNat) : left = right := by
  cases left with
  | mk left =>
    cases right with
    | mk right =>
      exact congrArg UniIndex.mk (UInt32.toNat_inj.mp same)

theorem lookup_valid {α : Type} (nodes : UniValMap α) (index : UniIndex) (value : α)
    (present : nodes.get index = some value) : index.toNat < nodes.data.size := by
  unfold UniValMap.get at present
  cases source : nodes.data[index.toNat]? with
  | none => simp [source] at present
  | some old => exact (Array.getElem?_eq_some_iff.mp source).1

theorem insert_existing {α : Type} (nodes : UniValMap α) (index : UniIndex) (old next : α)
    (present : nodes.get index = some old) :
    (nodes.insert index next).data = nodes.data.set index.toNat (some next) (lookup_valid nodes index old present) := by
  have valid := lookup_valid nodes index old present
  have noExtra : index.toNat + 1 - nodes.data.size = 0 := by omega
  simp [UniValMap.insert,UniValMap.extendTo,noExtra,valid,Id.run,pure]

theorem insert_existing_get_same {α : Type} (nodes : UniValMap α) (index : UniIndex) (old next : α)
    (present : nodes.get index = some old) : (nodes.insert index next).get index = some next := by
  unfold UniValMap.get
  rw [insert_existing nodes index old next present]
  simp

theorem insert_existing_get_other {α : Type} (nodes : UniValMap α) (index query : UniIndex) (old next : α)
    (present : nodes.get index = some old) (different : query ≠ index) :
    (nodes.insert index next).get query = nodes.get query := by
  have differentNat : query.toNat ≠ index.toNat := fun same => different (index_injective query index same)
  unfold UniValMap.get
  rw [insert_existing nodes index old next present]
  simp [Ne.symm differentNat]

theorem insert_existing_size {α : Type} (nodes : UniValMap α) (index : UniIndex) (old next : α)
    (present : nodes.get index = some old) : (nodes.insert index next).size = nodes.size := by
  unfold UniValMap.size
  rw [insert_existing nodes index old next present]
  simp

/-- Changing non-parent node metadata preserves the real exposed-cache
ancestor certificate and its depth function. -/
def update_depth (nodes : UniValMap TreeNode) (depth : ParentDepth nodes) (index : UniIndex)
    (old next : TreeNode) (present : nodes.get index = some old) (sameParent : next.parent = old.parent) :
    ParentDepth (nodes.insert index next) where
  depth := depth.depth
  bounded := by
    intro query node lookup
    rw [insert_existing_size nodes index old next present]
    by_cases same : query = index
    · subst query
      rw [insert_existing_get_same nodes index old next present] at lookup
      cases lookup
      exact depth.bounded index old present
    · rw [insert_existing_get_other nodes index query old next present same] at lookup
      exact depth.bounded query node lookup
  parent := by
    intro query node lookup before parentEq
    have original : ∃ original, nodes.get query = some original ∧ original.parent = node.parent := by
      by_cases same : query = index
      · subst query
        rw [insert_existing_get_same nodes index old next present] at lookup
        cases lookup
        exact ⟨old,present,sameParent.symm⟩
      · rw [insert_existing_get_other nodes index query old next present same] at lookup
        exact ⟨node,lookup,rfl⟩
    obtain ⟨original,originalLookup,parentSame⟩ := original
    obtain ⟨ancestor,ancestorLookup,smaller⟩ := depth.parent query original originalLookup before (parentSame.trans parentEq)
    by_cases same : before = index
    · subst before
      exact ⟨next,insert_existing_get_same nodes index old next present,smaller⟩
    · exact ⟨ancestor,(insert_existing_get_other nodes index before old next present same).trans ancestorLookup,smaller⟩
end DuplicatePrefix.GeneralBorrowNodeUpdate

open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowNodeUpdate." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved generic node update dependency {dependency}"
