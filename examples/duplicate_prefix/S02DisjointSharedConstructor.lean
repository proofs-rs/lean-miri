import duplicate_prefix.S02DisjointConstructorGenericPositive
import duplicate_prefix.S02FrozenOutside
import duplicate_prefix.GeneralBorrowFreshMetadataChildShared
import duplicate_prefix.GeneralBorrowFreshMetadataChildSharedReuse

namespace DuplicatePrefix.S02DisjointSharedConstructor
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshNode GeneralBorrowFreshGraph GeneralBorrowFreshAnchor DuplicatePrefixBorrowAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 800000
attribute [local irreducible] UniValMap.insert

/-- Actual shared append succeeds and retains a disjoint destination's full
positive capability after real `.Read` SIFA. -/
theorem append (input : GeneralBorrowFreshMetadataChildShared.Input)
    (formed : GeneralBorrowStructuralHistoryState.GraphState input.tree)
    (clean : GeneralBorrowGcVacantClean.VacantClean input.tree)
    (protections : ProtectedTags) (source selected : Option UniIndex) (maximum : Option BorTag)
    (lower width : UInt64)
    (outside : input.offset.toNat+input.len.toNat ≤ lower.toNat ∨ (lower+width).toNat ≤ input.offset.toNat)
    (profile : GeneralRangeMapState.Every (fun location => GeneralBorrowLocationSifaConsistency.Profile input.tree location protections) input.tree.locations)
    (old : Positive input.tree protections source selected maximum lower width) :
    (input.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) sharedState) .Frozen input.isProtected).outcome = .ok () ∧
    Nonempty (Positive (GeneralBorrowFreshMetadataChildShared.result input) protections source selected maximum lower width) := by
  let index := GeneralBorrowFreshMetadataChildShared.index input
  have atEnd : index.toNat = input.tree.nodes.data.size := GeneralBorrowFreshMetadataChildShared.at_end input
  have vacant : input.tree.nodes.get index = none := by
    simp only [UniValMap.get,atEnd,Array.getElem?_eq_none (Nat.le_refl _) ]
  have depth := attached_depth input.tree.nodes input.depth index input.parent input.parentNode (sharedNode input.newTag input.parent)
    atEnd input.parentPresent rfl
  have allocator := GeneralBorrowFreshMetadataChildAttach.allocator input.tree index input.parent input.parentNode
    (sharedNode input.newTag input.parent) atEnd input.parentPresent (GeneralBorrowFreshMetadataChildShared.mapping input)
    (GeneralBorrowFreshMetadataChildShared.locations input) (GeneralBorrowFreshMetadataChildShared.stage input) rfl
  have size : input.tree.nodes.size ≤ (attached input.tree index input.parent input.parentNode (sharedNode input.newTag input.parent)).nodes.size := by
    change input.tree.nodes.size ≤ (GeneralBorrowFreshMetadataChildShared.stage input).nodes.size
    rw [allocator.2.2]
    omega
  have positive := S02DisjointConstructorGenericPositive.after_sifa input.tree formed input.depth index input.parent input.parentNode
    (sharedNode input.newTag input.parent) sharedState
    vacant input.parentPresent (Or.inl atEnd) clean size depth rfl rfl rfl S02FrozenOutside.foreign S02FrozenOutside.query (GeneralBorrowFreshMetadataChildShared.mapping input)
    protections source selected maximum input.offset input.len lower width input.well input.bounds outside .Read
      (GeneralBorrowSifaPermissionConsistency.frozen false _) (GeneralBorrowSifaPermissionConsistency.frozen true _) profile old
  refine ⟨(GeneralBorrowFreshMetadataChildShared.append input).success,?_⟩
  rw [GeneralBorrowFreshMetadataChildShared.tree_eq input]
  exact positive

/-- Actual shared bounded reuse has the same destination guarantee, without
assuming the old normal support excludes its vacant insertion slot. -/
theorem reuse (input : GeneralBorrowFreshMetadataChildSharedReuse.Input)
    (formed : GeneralBorrowStructuralHistoryState.GraphState input.tree)
    (clean : GeneralBorrowGcVacantClean.VacantClean input.tree)
    (protections : ProtectedTags) (source selected : Option UniIndex) (maximum : Option BorTag)
    (lower width : UInt64)
    (outside : input.offset.toNat+input.len.toNat ≤ lower.toNat ∨ (lower+width).toNat ≤ input.offset.toNat)
    (profile : GeneralRangeMapState.Every (fun location => GeneralBorrowLocationSifaConsistency.Profile input.tree location protections) input.tree.locations)
    (old : Positive input.tree protections source selected maximum lower width) :
    (input.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) sharedState) .Frozen input.isProtected).outcome = .ok () ∧
    Nonempty (Positive (GeneralBorrowFreshMetadataChildSharedReuse.result input) protections source selected maximum lower width) := by
  have depth := GeneralBorrowFreshReuseNode.attached_depth input.tree.nodes input.depth input.index input.parent input.parentNode
    (sharedNode input.newTag input.parent) input.valid input.vacant input.parentPresent rfl input.parentSlack
  have allocator := GeneralBorrowFreshMetadataChildReuseAttach.allocator input.tree input.index input.parent input.parentNode
    (sharedNode input.newTag input.parent) input.valid input.vacant input.parentPresent (GeneralBorrowFreshMetadataChildSharedReuse.mapping input)
    (GeneralBorrowFreshMetadataChildSharedReuse.locations input) (GeneralBorrowFreshMetadataChildSharedReuse.stage input) rfl
  have size : input.tree.nodes.size ≤ (attached input.tree input.index input.parent input.parentNode (sharedNode input.newTag input.parent)).nodes.size := by
    change input.tree.nodes.size ≤ (GeneralBorrowFreshMetadataChildSharedReuse.stage input).nodes.size
    rw [allocator.2.2]
    exact Nat.le_refl _
  have positive := S02DisjointConstructorGenericPositive.after_sifa input.tree formed input.depth input.index input.parent input.parentNode
    (sharedNode input.newTag input.parent) sharedState
    input.vacant input.parentPresent (Or.inr input.valid) clean size depth rfl rfl rfl S02FrozenOutside.foreign S02FrozenOutside.query (GeneralBorrowFreshMetadataChildSharedReuse.mapping input)
    protections source selected maximum input.offset input.len lower width input.well input.bounds outside .Read
      (GeneralBorrowSifaPermissionConsistency.frozen false _) (GeneralBorrowSifaPermissionConsistency.frozen true _) profile old
  refine ⟨(GeneralBorrowFreshMetadataChildSharedReuse.reuse input).success,?_⟩
  rw [GeneralBorrowFreshMetadataChildSharedReuse.tree_eq input]
  exact positive

/-- Public constructor endpoint over the actual allocator's append/reuse data.
Both operation success and full post-constructor destination capability are
conclusions; destination root/source need not equal the constructor's parent. -/
theorem construct (tree : BorrowTree) (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (parentTagPresent : tree.indexOfTag parentTag = some parent) (parentPresent : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag)
    (slot : GeneralBorrowFreshReborrowStages.Slot tree depth parent)
    (isProtected : Bool) (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (clean : GeneralBorrowGcVacantClean.VacantClean tree)
    (protections : ProtectedTags) (source selected : Option UniIndex) (maximum : Option BorTag)
    (lower width : UInt64) (outside : offset.toNat+len.toNat ≤ lower.toNat ∨ (lower+width).toNat ≤ offset.toNat)
    (profile : GeneralRangeMapState.Every (fun location => GeneralBorrowLocationSifaConsistency.Profile tree location protections) tree.locations)
    (old : Positive tree protections source selected maximum lower width) :
    let result := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) sharedState) .Frozen isProtected
    result.outcome = .ok () ∧ Nonempty (Positive result.tree protections source selected maximum lower width) := by
  cases slot with
  | append noFree aligned fits =>
    exact append ⟨tree,depth,formed.children,formed.covered,parentTag,newTag,parent,parentNode,parentTagPresent,parentPresent,
      fresh,noFree,aligned,fits,isProtected,offset,len,nonzero,well,bounds⟩ formed clean protections source selected maximum lower width outside profile old
  | reuse index available bounded vacant slack =>
    exact reuse ⟨tree,depth,formed.children,formed.covered,parentTag,newTag,parent,parentNode,parentTagPresent,parentPresent,
      fresh,index,available,bounded,vacant,slack,isProtected,offset,len,nonzero,well,bounds⟩ formed clean protections source selected maximum lower width outside profile old

end DuplicatePrefix.S02DisjointSharedConstructor

open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S02DisjointSharedConstructor.append,``DuplicatePrefix.S02DisjointSharedConstructor.reuse,
      ``DuplicatePrefix.S02DisjointSharedConstructor.construct] do
    for ax in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "unapproved axiom {ax}"
