import duplicate_prefix.S02DisjointConstructorGenericRow
import duplicate_prefix.S02ConstructorPreSifaProfile
import duplicate_prefix.S02SifaAnyPositive
import duplicate_prefix.GeneralBorrowFreshRangeFrame

namespace DuplicatePrefix.S02DisjointConstructorGenericPositive
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
    (index parent : UniIndex) (parentNode newNode : TreeNode) (inside : LocationState)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodeAt parent = some parentNode)
    (slot : index.toNat = tree.nodes.data.size ∨ index.toNat < tree.nodes.data.size)
    (clean : GeneralBorrowGcVacantClean.VacantClean tree)
    (size : tree.nodes.size ≤ (attached tree index parent parentNode newNode).nodes.size)
    (nextDepth : GeneralBorrowExposure.ParentDepth (attached tree index parent parentNode newNode).nodes)
    (hidden : newNode.isExposed = false) (leaf : newNode.children = #[]) (childParent : newNode.parent = some parent)
    (foreign : ∀ kind held,DuplicatePrefixScalarAuthorization.Compatible newNode.defaultLocationState kind .ForeignAccess held)
    (foreignQuery : ∀ kind held,DuplicatePrefixCallbackVisitAuthorization.Authorized newNode.defaultLocationState kind held
      (some .ForeignAccess) (some .ForeignAccess))
    (mapping : UniKeyMap BorTag) (protections : ProtectedTags)
    (source selected : Option UniIndex) (maximum : Option BorTag)
    (offset len lower width : UInt64) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (outside : offset.toNat+len.toNat ≤ lower.toNat ∨ (lower+width).toNat ≤ offset.toNat)
    (old : Positive tree protections source selected maximum lower width) :
    let changed := tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len) (fun _ location =>
      GeneralBorrowFreshMaterialization.materialized location index inside)
    let stage := GeneralBorrowFreshMetadataChildAttach.staged tree index parent parentNode
      newNode mapping changed.state
    Nonempty (Positive stage protections source selected maximum lower width) := by
  dsimp only
  have frame := GeneralBorrowFreshRangeFrame.modifyRange_frame tree.locations (Size.ofBytes offset) (Size.ofBytes len)
    (fun _ location => GeneralBorrowFreshMaterialization.materialized location index inside) well bounds
  refine ⟨{positive := old.positive,bounds := ?_,sourcePresent := ?_,wildcardRoot := old.wildcardRoot,rows := ?_}⟩
  · change lower.toNat+width.toNat ≤ _
    dsimp only [GeneralBorrowFreshMetadataChildAttach.staged]
    rw [frame.2]
    exact old.bounds
  · intro anchor same
    obtain ⟨node,present⟩ := old.sourcePresent anchor same
    exact GeneralBorrowFreshMetadataChildReuseGraph.old_present tree index parent anchor parentNode _ node vacant parentPresent present
  · exact S02DisjointConstructorGenericRow.owned tree formed depth index parent parentNode newNode inside vacant parentPresent slot
      formed.fits clean size nextDepth hidden leaf childParent foreign foreignQuery mapping protections source selected maximum old.sourcePresent
      (Size.ofBytes offset) (Size.ofBytes len) lower (lower+width) well bounds outside old.rows

/-- The exact mutable pre-SIFA stage has both a full Positive destination
capability and the allocation-wide scalar profile needed by real `.None` SIFA. -/
theorem after_sifa (tree : BorrowTree) (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (index parent : UniIndex) (parentNode newNode : TreeNode) (inside : LocationState)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodeAt parent = some parentNode)
    (slot : index.toNat = tree.nodes.data.size ∨ index.toNat < tree.nodes.data.size)
    (clean : GeneralBorrowGcVacantClean.VacantClean tree)
    (size : tree.nodes.size ≤ (attached tree index parent parentNode newNode).nodes.size)
    (nextDepth : GeneralBorrowExposure.ParentDepth (attached tree index parent parentNode newNode).nodes)
    (hidden : newNode.isExposed = false) (leaf : newNode.children = #[]) (childParent : newNode.parent = some parent)
    (foreign : ∀ kind held,DuplicatePrefixScalarAuthorization.Compatible newNode.defaultLocationState kind .ForeignAccess held)
    (foreignQuery : ∀ kind held,DuplicatePrefixCallbackVisitAuthorization.Authorized newNode.defaultLocationState kind held
      (some .ForeignAccess) (some .ForeignAccess))
    (mapping : UniKeyMap BorTag) (protections : ProtectedTags)
    (source selected : Option UniIndex) (maximum : Option BorTag)
    (offset len lower width : UInt64) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (outside : offset.toNat+len.toNat ≤ lower.toNat ∨ (lower+width).toNat ≤ offset.toNat)
    (strongest : IdempotentForeignAccess)
    (newDefault : GeneralBorrowSifaPermissionConsistency.Consistent newNode.defaultLocationState (protections.contains newNode.tag))
    (newInside : GeneralBorrowSifaPermissionConsistency.Consistent inside (protections.contains newNode.tag))
    (profile : GeneralRangeMapState.Every (fun location => GeneralBorrowLocationSifaConsistency.Profile tree location protections) tree.locations)
    (old : Positive tree protections source selected maximum lower width) :
    let changed := tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len) (fun _ location =>
      GeneralBorrowFreshMaterialization.materialized location index inside)
    let stage := GeneralBorrowFreshMetadataChildAttach.staged tree index parent parentNode
      newNode mapping changed.state
    Nonempty (Positive (sourceUpdateSifa stage parent strongest).1 protections source selected maximum lower width) := by
  obtain ⟨initial⟩ := positive tree formed depth index parent parentNode newNode inside vacant parentPresent slot clean size nextDepth hidden leaf childParent foreign foreignQuery
    mapping protections source selected maximum offset len lower width well bounds outside old
  have nextProfile := S02ConstructorPreSifaProfile.staged tree protections index parent parentNode
    newNode inside mapping vacant parentPresent offset len well bounds
    profile newDefault newInside
  let stage := GeneralBorrowFreshMetadataChildAttach.staged tree index parent parentNode
    newNode mapping
    (tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len) (fun _ location =>
      GeneralBorrowFreshMaterialization.materialized location index inside)).state
  exact S02SifaAnyPositive.preserved strongest stage nextDepth parent protections source selected maximum lower width nextProfile initial

end DuplicatePrefix.S02DisjointConstructorGenericPositive

open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S02DisjointConstructorGenericPositive.positive,``DuplicatePrefix.S02DisjointConstructorGenericPositive.after_sifa] do
    for ax in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "unapproved axiom {ax}"
