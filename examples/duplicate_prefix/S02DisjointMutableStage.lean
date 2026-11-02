import duplicate_prefix.S02DisjointConstructorRow
import duplicate_prefix.S02ConstructorPreSifaProfile
import duplicate_prefix.S02SifaAnyPositive
import duplicate_prefix.GeneralBorrowFreshRangeFrame

namespace DuplicatePrefix.S02DisjointMutableStage
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshNode GeneralBorrowFreshGraph DuplicatePrefixBorrowAuthorization GeneralRangeMapOrigins
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 800000
attribute [local irreducible] UniValMap.insert

/-- Real disjoint materialization and attachment preserve a complete Positive
capability on the destination window, including its physical bounds and source. -/
theorem positive (tree : BorrowTree) (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (index parent : UniIndex) (parentNode : TreeNode) (newTag : BorTag)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodeAt parent = some parentNode)
    (slot : index.toNat = tree.nodes.data.size ∨ index.toNat < tree.nodes.data.size)
    (clean : GeneralBorrowGcVacantClean.VacantClean tree)
    (size : tree.nodes.size ≤ (attached tree index parent parentNode (GeneralBorrowFreshChild.child newTag parent)).nodes.size)
    (nextDepth : GeneralBorrowExposure.ParentDepth (attached tree index parent parentNode (GeneralBorrowFreshChild.child newTag parent)).nodes)
    (mapping : UniKeyMap BorTag) (protections : ProtectedTags)
    (source selected : Option UniIndex) (maximum : Option BorTag)
    (offset len lower width : UInt64) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (outside : offset.toNat+len.toNat ≤ lower.toNat ∨ (lower+width).toNat ≤ offset.toNat)
    (old : Positive tree protections source selected maximum lower width) :
    let changed := tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len) (fun _ location =>
      GeneralBorrowFreshMaterialization.materialized location index GeneralBorrowFreshChild.inside)
    let stage := GeneralBorrowFreshMetadataChildAttach.staged tree index parent parentNode
      (GeneralBorrowFreshChild.child newTag parent) mapping changed.state
    Nonempty (Positive stage protections source selected maximum lower width) := by
  dsimp only
  have frame := GeneralBorrowFreshRangeFrame.modifyRange_frame tree.locations (Size.ofBytes offset) (Size.ofBytes len)
    (fun _ location => GeneralBorrowFreshMaterialization.materialized location index GeneralBorrowFreshChild.inside) well bounds
  refine ⟨{positive := old.positive,bounds := ?_,sourcePresent := ?_,wildcardRoot := old.wildcardRoot,rows := ?_}⟩
  · change lower.toNat+width.toNat ≤ _
    dsimp only [GeneralBorrowFreshMetadataChildAttach.staged]
    rw [frame.2]
    exact old.bounds
  · intro anchor same
    obtain ⟨node,present⟩ := old.sourcePresent anchor same
    exact GeneralBorrowFreshMetadataChildReuseGraph.old_present tree index parent anchor parentNode _ node vacant parentPresent present
  · exact S02DisjointConstructorRow.owned tree formed depth index parent parentNode newTag vacant parentPresent slot
      formed.fits clean size nextDepth mapping protections source selected maximum old.sourcePresent
      (Size.ofBytes offset) (Size.ofBytes len) lower (lower+width) well bounds outside old.rows

private theorem reservation_none (accessed held : Bool) :
    GeneralBorrowSifaPermissionConsistency.Consistent ⟨.ReservedFrz false,accessed,.None⟩ held := by
  cases held
  · exact ⟨.Read,rfl,Nat.zero_le _⟩
  · exact GeneralBorrowSifaPermissionConsistency.protected_reservation accessed

/-- The exact mutable pre-SIFA stage has both a full Positive destination
capability and the allocation-wide scalar profile needed by real `.None` SIFA. -/
theorem after_sifa (tree : BorrowTree) (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (index parent : UniIndex) (parentNode : TreeNode) (newTag : BorTag)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodeAt parent = some parentNode)
    (slot : index.toNat = tree.nodes.data.size ∨ index.toNat < tree.nodes.data.size)
    (clean : GeneralBorrowGcVacantClean.VacantClean tree)
    (size : tree.nodes.size ≤ (attached tree index parent parentNode (GeneralBorrowFreshChild.child newTag parent)).nodes.size)
    (nextDepth : GeneralBorrowExposure.ParentDepth (attached tree index parent parentNode (GeneralBorrowFreshChild.child newTag parent)).nodes)
    (mapping : UniKeyMap BorTag) (protections : ProtectedTags)
    (source selected : Option UniIndex) (maximum : Option BorTag)
    (offset len lower width : UInt64) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (outside : offset.toNat+len.toNat ≤ lower.toNat ∨ (lower+width).toNat ≤ offset.toNat)
    (profile : GeneralRangeMapState.Every (fun location => GeneralBorrowLocationSifaConsistency.Profile tree location protections) tree.locations)
    (old : Positive tree protections source selected maximum lower width) :
    let changed := tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len) (fun _ location =>
      GeneralBorrowFreshMaterialization.materialized location index GeneralBorrowFreshChild.inside)
    let stage := GeneralBorrowFreshMetadataChildAttach.staged tree index parent parentNode
      (GeneralBorrowFreshChild.child newTag parent) mapping changed.state
    Nonempty (Positive (sourceUpdateSifa stage parent .None).1 protections source selected maximum lower width) := by
  obtain ⟨initial⟩ := positive tree formed depth index parent parentNode newTag vacant parentPresent slot clean size nextDepth
    mapping protections source selected maximum offset len lower width well bounds outside old
  have nextProfile := S02ConstructorPreSifaProfile.staged tree protections index parent parentNode
    (GeneralBorrowFreshChild.child newTag parent) GeneralBorrowFreshChild.inside mapping vacant parentPresent offset len well bounds
    profile (reservation_none false _) (reservation_none true _)
  let stage := GeneralBorrowFreshMetadataChildAttach.staged tree index parent parentNode
    (GeneralBorrowFreshChild.child newTag parent) mapping
    (tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len) (fun _ location =>
      GeneralBorrowFreshMaterialization.materialized location index GeneralBorrowFreshChild.inside)).state
  exact S02SifaAnyPositive.preserved .None stage nextDepth parent protections source selected maximum lower width nextProfile initial

end DuplicatePrefix.S02DisjointMutableStage

open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S02DisjointMutableStage.positive,``DuplicatePrefix.S02DisjointMutableStage.after_sifa] do
    for ax in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "unapproved axiom {ax}"
