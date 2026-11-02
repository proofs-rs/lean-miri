import duplicate_prefix.GeneralBorrowConstructorSifaProfile

namespace DuplicatePrefix.S02ConstructorPreSifaProfile
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowLocationSifaConsistency GeneralBorrowFreshNode GeneralBorrowNodeUpdate GeneralRangeMapState
open GeneralBorrowConstructorSifaProfile
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] UniValMap.insert

/-- Existing scalar consistency plus real attachment/materialization establish
the staged profile consumed by arbitrary-root SIFA authorization transport. -/
theorem staged (tree : BorrowTree) (protections : ProtectedTags)
    (index parent : UniIndex) (parentNode newNode : TreeNode) (inside : LocationState) (mapping : UniKeyMap BorTag)
    (vacant : tree.nodes.get index = none) (present : tree.nodeAt parent = some parentNode)
    (offset len : UInt64) (well : tree.locations.WellFormed) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (initial : Every (fun location => Profile tree location protections) tree.locations)
    (newDefault : GeneralBorrowSifaPermissionConsistency.Consistent newNode.defaultLocationState (protections.contains newNode.tag))
    (newInside : GeneralBorrowSifaPermissionConsistency.Consistent inside (protections.contains newNode.tag))
    :
    let staged := GeneralBorrowFreshMetadataChildAttach.staged tree index parent parentNode newNode mapping
      (tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len)
        (fun _ location => GeneralBorrowFreshMaterialization.materialized location index inside)).state
    Every (fun location => Profile staged location protections) staged.locations := by
  dsimp only
  let base := {tree with nodes := attachedNodes tree.nodes index parent parentNode newNode}
  let predicate := fun location => Profile base location protections
  have formed : Every predicate tree.locations := by
    intro position valid
    exact attach tree _ protections index parent parentNode newNode vacant present (initial position valid) newDefault
  have different : index ≠ parent := by
    intro same
    change tree.nodes.get parent = some parentNode at present
    rw [←same,vacant] at present;cases present
  have newPresent : base.nodeAt index = some newNode := by
    change ((tree.nodes.insert index newNode).insert parent _).get index = _
    rw [GeneralBorrowFreshLocation.get_other _ parent index _ different,GeneralBorrowFreshLocation.get_same]
  have modifyStep : ∀ range location,predicate location → predicate
      ((fun (_ : ByteRange) location => GeneralBorrowFreshMaterialization.materialized location index inside) range location) := by
    intro range location good
    exact materialize base location protections index newNode newPresent inside good newInside
  have modified := GeneralBorrowExposureChildAttach.modify_every predicate tree.locations
    (Size.ofBytes offset) (Size.ofBytes len)
    (fun _ location => GeneralBorrowFreshMaterialization.materialized location index inside) well bounds formed modifyStep
  intro position valid
  obtain ⟨consistent,clean⟩ := modified position valid
  exact ⟨consistent,clean⟩

end DuplicatePrefix.S02ConstructorPreSifaProfile
open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms ``DuplicatePrefix.S02ConstructorPreSifaProfile.staged) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
