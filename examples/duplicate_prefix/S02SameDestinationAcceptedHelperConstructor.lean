import duplicate_prefix.S02DisjointConstructorGenericPositive
import duplicate_prefix.S02SameDestinationAcceptedMutableForeign
import duplicate_prefix.GeneralBorrowFreshMetadataChildMutable
import duplicate_prefix.GeneralBorrowFreshMetadataChildMutableReuse

namespace DuplicatePrefix.S02SameDestinationAcceptedHelperConstructor
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshNode GeneralBorrowFreshGraph GeneralBorrowFreshChild DuplicatePrefixBorrowAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 800000
attribute [local irreducible] UniValMap.insert

/-- Actual shared append succeeds and retains a disjoint destination's full
positive capability after real `.Read` SIFA. -/
theorem append (input : GeneralBorrowFreshMetadataChildMutable.Input)
    (formed : GeneralBorrowStructuralHistoryState.GraphState input.tree)
    (clean : GeneralBorrowGcVacantClean.VacantClean input.tree)
    (protections : ProtectedTags) (source selected : Option UniIndex) (maximum : Option BorTag)
    (lower width : UInt64)
    (outside : input.offset.toNat+input.len.toNat ≤ lower.toNat ∨ (lower+width).toNat ≤ input.offset.toNat)
    (profile : GeneralRangeMapState.Every (fun location => GeneralBorrowLocationSifaConsistency.Profile input.tree location protections) input.tree.locations)
    (held : protections.contains input.newTag = true)
    (old : Positive input.tree protections source selected maximum lower width) :
    (input.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) inside) (.ReservedFrz false) true).outcome = .ok () ∧
    Nonempty (Positive (GeneralBorrowFreshMetadataChildMutable.result input) protections source selected maximum lower width) := by
  let index := GeneralBorrowFreshMetadataChildMutable.index input
  have atEnd : index.toNat = input.tree.nodes.data.size := GeneralBorrowFreshMetadataChildMutable.at_end input
  have vacant : input.tree.nodes.get index = none := by
    simp only [UniValMap.get,atEnd,Array.getElem?_eq_none (Nat.le_refl _) ]
  have depth := attached_depth input.tree.nodes input.depth index input.parent input.parentNode (child input.newTag input.parent)
    atEnd input.parentPresent rfl
  have allocator := GeneralBorrowFreshMetadataChildAttach.allocator input.tree index input.parent input.parentNode
    (child input.newTag input.parent) atEnd input.parentPresent (GeneralBorrowFreshMetadataChildMutable.mapping input)
    (GeneralBorrowFreshMetadataChildMutable.locations input) (GeneralBorrowFreshMetadataChildMutable.stage input) rfl
  have size : input.tree.nodes.size ≤ (attached input.tree index input.parent input.parentNode (child input.newTag input.parent)).nodes.size := by
    change input.tree.nodes.size ≤ (GeneralBorrowFreshMetadataChildMutable.stage input).nodes.size
    rw [allocator.2.2]
    omega
  have positive := S02DisjointConstructorGenericPositive.after_sifa input.tree formed input.depth index input.parent input.parentNode
    (child input.newTag input.parent) inside
    vacant input.parentPresent (Or.inl atEnd) clean size depth rfl rfl rfl (S02SameDestinationAcceptedMutableForeign.foreign .None) (S02SameDestinationAcceptedMutableForeign.query .None) (GeneralBorrowFreshMetadataChildMutable.mapping input)
    protections source selected maximum input.offset input.len lower width input.well input.bounds outside .None
      (by change GeneralBorrowSifaPermissionConsistency.Consistent ⟨.ReservedFrz false,false,.None⟩ (protections.contains input.newTag);rw [held];exact GeneralBorrowSifaPermissionConsistency.protected_reservation false)
      (by change GeneralBorrowSifaPermissionConsistency.Consistent ⟨.ReservedFrz false,true,.None⟩ (protections.contains input.newTag);rw [held];exact GeneralBorrowSifaPermissionConsistency.protected_reservation true) profile old
  refine ⟨(GeneralBorrowFreshMetadataChildMutable.append input).success,?_⟩
  rw [GeneralBorrowFreshMetadataChildMutable.tree_eq input]
  exact positive

/-- Actual shared bounded reuse has the same destination guarantee, without
assuming the old normal support excludes its vacant insertion slot. -/
theorem reuse (input : GeneralBorrowFreshMetadataChildMutableReuse.Input)
    (formed : GeneralBorrowStructuralHistoryState.GraphState input.tree)
    (clean : GeneralBorrowGcVacantClean.VacantClean input.tree)
    (protections : ProtectedTags) (source selected : Option UniIndex) (maximum : Option BorTag)
    (lower width : UInt64)
    (outside : input.offset.toNat+input.len.toNat ≤ lower.toNat ∨ (lower+width).toNat ≤ input.offset.toNat)
    (profile : GeneralRangeMapState.Every (fun location => GeneralBorrowLocationSifaConsistency.Profile input.tree location protections) input.tree.locations)
    (held : protections.contains input.newTag = true)
    (old : Positive input.tree protections source selected maximum lower width) :
    (input.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) inside) (.ReservedFrz false) true).outcome = .ok () ∧
    Nonempty (Positive (GeneralBorrowFreshMetadataChildMutableReuse.result input) protections source selected maximum lower width) := by
  have depth := GeneralBorrowFreshReuseNode.attached_depth input.tree.nodes input.depth input.index input.parent input.parentNode
    (child input.newTag input.parent) input.valid input.vacant input.parentPresent rfl input.parentSlack
  have allocator := GeneralBorrowFreshMetadataChildReuseAttach.allocator input.tree input.index input.parent input.parentNode
    (child input.newTag input.parent) input.valid input.vacant input.parentPresent (GeneralBorrowFreshMetadataChildMutableReuse.mapping input)
    (GeneralBorrowFreshMetadataChildMutableReuse.locations input) (GeneralBorrowFreshMetadataChildMutableReuse.stage input) rfl
  have size : input.tree.nodes.size ≤ (attached input.tree input.index input.parent input.parentNode (child input.newTag input.parent)).nodes.size := by
    change input.tree.nodes.size ≤ (GeneralBorrowFreshMetadataChildMutableReuse.stage input).nodes.size
    rw [allocator.2.2]
    exact Nat.le_refl _
  have positive := S02DisjointConstructorGenericPositive.after_sifa input.tree formed input.depth input.index input.parent input.parentNode
    (child input.newTag input.parent) inside
    input.vacant input.parentPresent (Or.inr input.valid) clean size depth rfl rfl rfl (S02SameDestinationAcceptedMutableForeign.foreign .None) (S02SameDestinationAcceptedMutableForeign.query .None) (GeneralBorrowFreshMetadataChildMutableReuse.mapping input)
    protections source selected maximum input.offset input.len lower width input.well input.bounds outside .None
      (by change GeneralBorrowSifaPermissionConsistency.Consistent ⟨.ReservedFrz false,false,.None⟩ (protections.contains input.newTag);rw [held];exact GeneralBorrowSifaPermissionConsistency.protected_reservation false)
      (by change GeneralBorrowSifaPermissionConsistency.Consistent ⟨.ReservedFrz false,true,.None⟩ (protections.contains input.newTag);rw [held];exact GeneralBorrowSifaPermissionConsistency.protected_reservation true) profile old
  refine ⟨(GeneralBorrowFreshMetadataChildMutableReuse.reuse input).success,?_⟩
  rw [GeneralBorrowFreshMetadataChildMutableReuse.tree_eq input]
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
    (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (clean : GeneralBorrowGcVacantClean.VacantClean tree)
    (protections : ProtectedTags) (source selected : Option UniIndex) (maximum : Option BorTag)
    (lower width : UInt64) (outside : offset.toNat+len.toNat ≤ lower.toNat ∨ (lower+width).toNat ≤ offset.toNat)
    (profile : GeneralRangeMapState.Every (fun location => GeneralBorrowLocationSifaConsistency.Profile tree location protections) tree.locations)
    (held : protections.contains newTag = true)
    (old : Positive tree protections source selected maximum lower width) :
    let result := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) inside) (.ReservedFrz false) true
    result.outcome = .ok () ∧ Nonempty (Positive result.tree protections source selected maximum lower width) := by
  cases slot with
  | append noFree aligned fits =>
    exact append ⟨tree,depth,formed.children,formed.covered,parentTag,newTag,parent,parentNode,parentTagPresent,parentPresent,
      fresh,noFree,aligned,fits,offset,len,nonzero,well,bounds⟩ formed clean protections source selected maximum lower width outside profile held old
  | reuse index available bounded vacant slack =>
    exact reuse ⟨tree,depth,formed.children,formed.covered,parentTag,newTag,parent,parentNode,parentTagPresent,parentPresent,
      fresh,index,available,bounded,vacant,slack,offset,len,nonzero,well,bounds⟩ formed clean protections source selected maximum lower width outside profile held old

end DuplicatePrefix.S02SameDestinationAcceptedHelperConstructor

open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S02SameDestinationAcceptedHelperConstructor.append,``DuplicatePrefix.S02SameDestinationAcceptedHelperConstructor.reuse,
      ``DuplicatePrefix.S02SameDestinationAcceptedHelperConstructor.construct] do
    for ax in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "unapproved axiom {ax}"
