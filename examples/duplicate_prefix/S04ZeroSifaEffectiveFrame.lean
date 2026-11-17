import duplicate_prefix.S04ZeroSifaStateFrame
import duplicate_prefix.GeneralBorrowSifaWritableFrame

namespace DuplicatePrefix.S04ZeroSifaEffectiveFrame
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.DataStructures
open GeneralBorrowSifa GeneralBorrowView GeneralBorrowNodeUpdate S04ZeroSifaStateFrame
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private theorem some_reset (before after : IdempotentForeignAccess)
    (reset : Reset (some before) (some after)) : after = before ∨ after = .None := by
  rcases reset with same | none
  · exact .inl (Option.some.inj same)
  · exact .inr (Option.some.inj none)

/-- The actual protected-constructor ancestor loop changes an effective scalar
state only by retaining it or setting SIFA to None. Lazy defaults and explicitly
stored row states are both covered, on every loop success/error branch. -/
theorem effective (tree : BorrowTree) (start query : UniIndex) (node : TreeNode)
    (present : tree.nodeAt query = some node) (position : Nat) (valid : position < tree.locations.entries.size) :
    let after := (sourceUpdateSifa tree start .None).1
    ∃ next,after.nodeAt query = some next ∧ next.tag = node.tag ∧
      ∃ nextValid : position < after.locations.entries.size,
        let beforeState := ((tree.locations.entries[position]'valid).data.perms.get query).getD node.defaultLocationState
        let afterState := ((after.locations.entries[position]'nextValid).data.perms.get query).getD next.defaultLocationState
        afterState = beforeState ∨ afterState = {beforeState with idempotentForeignAccess := .None} := by
  let after := (sourceUpdateSifa tree start .None).1
  have frame := sifa_frame tree start
  have shape := GeneralBorrowSifaView.preserves tree start .None
  obtain ⟨next,found,tag,parent,children,defaults⟩ := GeneralBorrowFreshMetadata.node_fields tree after shape query node present
  have ranges := congrArg (fun value => value.2.2.1) shape
  change after.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) =
    tree.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) at ranges
  have sizes := congrArg Array.size ranges
  simp only [Array.size_map] at sizes
  have nextValid : position < after.locations.entries.size := by omega
  have point := congrArg (fun rows => rows[position]?) ranges
  simp only [Array.getElem?_map,Array.getElem?_eq_getElem valid,
    Array.getElem?_eq_getElem nextValid,Option.map_some] at point
  have locations : locationShape (after.locations.entries[position]'nextValid).data =
      locationShape (tree.locations.entries[position]'valid).data := congrArg Prod.snd (Option.some.inj point)
  refine ⟨next,found,tag,nextValid,?_⟩
  have scalarShape := GeneralBorrowSifaWritableFrame.effective_shape _ _ query node next locations defaults
  have oldDefault := frame.1 query
  change Reset ((tree.nodes.get query).map TreeNode.defaultInitialSifa)
    ((after.nodes.get query).map TreeNode.defaultInitialSifa) at oldDefault
  change tree.nodes.get query = some node at present
  rw [present,found] at oldDefault
  simp only [Option.map_some] at oldDefault
  have oldStored := frame.2 position query
  change Reset (storedSifa tree position query) (storedSifa after position query) at oldStored
  simp only [storedSifa,Array.getElem?_eq_getElem valid,Array.getElem?_eq_getElem nextValid,
    Option.bind_some] at oldStored
  cases beforeStored : (tree.locations.entries[position]'valid).data.perms.get query with
  | none =>
    cases afterStored : (after.locations.entries[position]'nextValid).data.perms.get query with
    | none =>
      simp only [beforeStored,afterStored,Option.getD_none,GeneralBorrowWildcardVirtualLeaf.effective,
        TreeNode.defaultLocationState,stateShape,Prod.mk.injEq] at scalarShape ⊢
      rcases some_reset _ _ oldDefault with same | reset
      · exact .inl (by rw [defaults,same])
      · exact .inr (by rw [defaults,reset])
    | some state =>
      rcases oldStored with same | reset
      · simp only [beforeStored,afterStored,Option.map_none,Option.map_some] at same
        cases same
      · simp only [beforeStored,afterStored,Option.map_none,Option.map_some] at reset
        cases reset
  | some old =>
    cases afterStored : (after.locations.entries[position]'nextValid).data.perms.get query with
    | none =>
      rcases oldStored with same | reset
      · simp only [beforeStored,afterStored,Option.map_none,Option.map_some] at same
        cases same
      · simp only [beforeStored,afterStored,Option.map_none,Option.map_some] at reset
        cases reset
    | some current =>
      simp only [beforeStored,afterStored,Option.getD_some,GeneralBorrowWildcardVirtualLeaf.effective,
        stateShape,Prod.mk.injEq] at scalarShape ⊢
      simp only [beforeStored,afterStored,Option.map_some] at oldStored
      rcases scalarShape with ⟨permission,accessed⟩
      rcases old with ⟨oldPermission,oldAccessed,oldSifa⟩
      rcases current with ⟨newPermission,newAccessed,newSifa⟩
      dsimp only at permission accessed
      rcases some_reset _ _ oldStored with same | reset
      · exact .inl (by cases permission;cases accessed;cases same;rfl)
      · exact .inr (by cases permission;cases accessed;cases reset;rfl)

end DuplicatePrefix.S04ZeroSifaEffectiveFrame
