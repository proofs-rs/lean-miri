import duplicate_prefix.GeneralBorrowProtectedSiblingWindowLifetimes
import duplicate_prefix.GeneralBorrowProtectedSiblingVacantHistory
import duplicate_prefix.GeneralBorrowStructuralReleaseGeometryFrame
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingWindowResources
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProtectedSiblingGenerationWindow GeneralBorrowProtectedReleaseHistory GeneralRangeMapState
open GeneralBorrowProtectedSiblingWindowLifetimes
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000

theorem frame (tree : BorrowTree) (protections : ProtectedTags) (tags : List BorTag) :
    execute tree protections tags = {tree with locations := (execute tree protections tags).locations} := by
  induction tags generalizing tree with
  | nil => rfl
  | cons tag rest ih =>
    change execute (tree.releaseProtector tag protections).tree protections rest = {tree with locations := (execute (tree.releaseProtector tag protections).tree protections rest).locations}
    rw [ih,GeneralBorrowStructuralReleaseGeometryFrame.release tree protections tag]

theorem geometry (tree : BorrowTree) (protections : ProtectedTags) (tags : List BorTag)
    (well : tree.locations.WellFormed) :
    (execute tree protections tags).locations.WellFormed ∧ (execute tree protections tags).locations.size = tree.locations.size := by
  induction tags generalizing tree with
  | nil => exact ⟨well,rfl⟩
  | cons tag rest ih =>
    have released := GeneralBorrowStructuralReleaseGeometry.release tree protections tag well
    have later := ih (tree.releaseProtector tag protections).tree released.1
    exact ⟨later.1,later.2.trans released.2⟩

/-- Actual generated full-window lifetimes retain the sparse allocator,
partition geometry, graph metadata, vacant permission slots and tag high-water
bound after all real releases. No post-release resource is supplied. -/
theorem formed (capacity : UInt64) (nonzero : capacity ≠ 0) (selected : List Bool) (room : selected.length+2 ≤ 4294967295) :
    match GeneralBorrowProtectedSiblingWindowLifetimes.operation capacity selected with
    | .error _ => False
    | .ok output =>
      GeneralBorrowGcAllocator.Invariant output.tree ∧
      GeneralBorrowGcVacantClean.VacantClean output.tree ∧
      output.tree.locations.WellFormed ∧ output.tree.locations.size = Size.ofBytes capacity ∧
      Nonempty (GeneralBorrowExposure.ParentDepth output.tree.nodes) ∧
      GeneralBorrowGraph.ChildNodes output.tree ∧ GeneralBorrowGraph.RootsCover output.tree ∧
      output.tree.roots = #[GeneralBorrowFullSharedSeed.root] ∧
      GeneralBorrowProtectedSiblingGenerationBounds.KeysBelow output.tree.tagMapping output.ended.nextPointerTag.value.toNat := by
  obtain ⟨ready⟩ := GeneralBorrowProtectedSiblingGenerationWindow.generate capacity nonzero selected room
  have mapped : Tags ready.input.tree ready.state.global.protectedTags ready.state.tags := by
    intro tag member
    obtain ⟨index,node,present,tagged,lookup⟩ := ready.mapped tag member
    exact ⟨index,node,present,lookup,tagged,ready.held tag member⟩
  have clean : GeneralBorrowGcVacantClean.VacantClean ready.input.tree := by
    intro query missing position valid
    exact (ready.physical position valid).vacant query missing
  have fits : ready.input.tree.nodes.data.size ≤ 4294967296 := by have aligned := ready.input.aligned;have room := ready.input.fits;omega
  have vacant := GeneralBorrowProtectedSiblingVacantHistory.vacant ready.input.tree ready.state.global.protectedTags ready.state.tags ready.input.parent
    fits ready.input.depth ready.input.children ready.roots ready.input.covered mapped ready.readable clean
  have shape := frame ready.input.tree ready.state.global.protectedTags ready.state.tags
  have geometric := geometry ready.input.tree ready.state.global.protectedTags ready.state.tags ready.input.well
  simp only [GeneralBorrowProtectedSiblingWindowLifetimes.operation,ready.actual,Except.bind,bind,pure,Except.pure]
  rw [←ready.tree]
  refine ⟨?_,vacant,geometric.1,geometric.2.trans ready.capacity,?_,?_,?_,?_,?_⟩
  · rw [shape]
    exact ⟨ready.allocator.pool,ready.allocator.accounting,ready.allocator.unique,ready.allocator.nodeTags⟩
  · rw [shape]
    exact ⟨ready.input.depth⟩
  · rw [shape]
    exact ready.input.children
  · rw [shape]
    exact ready.input.covered
  · rw [shape]
    exact ready.roots.trans (congrArg (fun root => #[root]) ready.parent)
  · rw [shape]
    exact ready.mapBelow
end DuplicatePrefix.GeneralBorrowProtectedSiblingWindowResources
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowProtectedSiblingWindowResources.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved generated sibling resources dependency {dependency}"
