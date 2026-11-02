import duplicate_prefix.S02DisjointConstructorGenericPositive
import duplicate_prefix.S02SameDestinationAcceptedMutableForeign
import duplicate_prefix.GeneralBorrowFreshMetadataChildDefault
import duplicate_prefix.GeneralBorrowFreshMetadataChildDefaultReuse

namespace DuplicatePrefix.S02SameDestinationAcceptedDefaultConstructor
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshNode GeneralBorrowFreshGraph GeneralBorrowFreshDefaultChild DuplicatePrefixBorrowAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 800000
attribute [local irreducible] UniValMap.insert

/-- Actual shared append succeeds and retains a disjoint destination's full
positive capability after real `.Read` SIFA. -/
theorem append (input : GeneralBorrowFreshMetadataChildDefault.Input)
    (formed : GeneralBorrowStructuralHistoryState.GraphState input.tree)
    (clean : GeneralBorrowGcVacantClean.VacantClean input.tree)
    (protections : ProtectedTags) (source selected : Option UniIndex) (maximum : Option BorTag)
    (lower width : UInt64)
    (outside : input.offset.toNat+input.len.toNat ≤ lower.toNat ∨ (lower+width).toNat ≤ input.offset.toNat)
    (profile : GeneralRangeMapState.Every (fun location => GeneralBorrowLocationSifaConsistency.Profile input.tree location protections) input.tree.locations)
    (held : protections.contains input.newTag = false)
    (old : Positive input.tree protections source selected maximum lower width) :
    (input.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) inside) (.ReservedFrz false) false).outcome = .ok () ∧
    Nonempty (Positive (GeneralBorrowFreshMetadataChildDefault.result input) protections source selected maximum lower width) := by
  let index := GeneralBorrowFreshMetadataChildDefault.index input
  have atEnd : index.toNat = input.tree.nodes.data.size := GeneralBorrowFreshMetadataChildDefault.at_end input
  have vacant : input.tree.nodes.get index = none := by
    simp only [UniValMap.get,atEnd,Array.getElem?_eq_none (Nat.le_refl _) ]
  have depth := attached_depth input.tree.nodes input.depth index input.parent input.parentNode (child input.newTag input.parent)
    atEnd input.parentPresent rfl
  have allocator := GeneralBorrowFreshMetadataChildAttach.allocator input.tree index input.parent input.parentNode
    (child input.newTag input.parent) atEnd input.parentPresent (GeneralBorrowFreshMetadataChildDefault.mapping input)
    (GeneralBorrowFreshMetadataChildDefault.locations input) (GeneralBorrowFreshMetadataChildDefault.stage input) rfl
  have size : input.tree.nodes.size ≤ (attached input.tree index input.parent input.parentNode (child input.newTag input.parent)).nodes.size := by
    change input.tree.nodes.size ≤ (GeneralBorrowFreshMetadataChildDefault.stage input).nodes.size
    rw [allocator.2.2]
    omega
  have positive := S02DisjointConstructorGenericPositive.after_sifa input.tree formed input.depth index input.parent input.parentNode
    (child input.newTag input.parent) inside
    vacant input.parentPresent (Or.inl atEnd) clean size depth rfl rfl rfl (S02SameDestinationAcceptedMutableForeign.foreign .Read) (S02SameDestinationAcceptedMutableForeign.query .Read) (GeneralBorrowFreshMetadataChildDefault.mapping input)
    protections source selected maximum input.offset input.len lower width input.well input.bounds outside .Read
      (by change GeneralBorrowSifaPermissionConsistency.Consistent ⟨.ReservedFrz false,false,.Read⟩ (protections.contains input.newTag);rw [held];exact GeneralBorrowSifaPermissionConsistency.unprotected_reservation false)
      (by change GeneralBorrowSifaPermissionConsistency.Consistent ⟨.ReservedFrz false,true,.Read⟩ (protections.contains input.newTag);rw [held];exact GeneralBorrowSifaPermissionConsistency.unprotected_reservation true) profile old
  refine ⟨(GeneralBorrowFreshMetadataChildDefault.append input).success,?_⟩
  rw [GeneralBorrowFreshMetadataChildDefault.tree_eq input]
  exact positive

/-- Actual shared bounded reuse has the same destination guarantee, without
assuming the old normal support excludes its vacant insertion slot. -/
theorem reuse (input : GeneralBorrowFreshMetadataChildDefaultReuse.Input)
    (formed : GeneralBorrowStructuralHistoryState.GraphState input.tree)
    (clean : GeneralBorrowGcVacantClean.VacantClean input.tree)
    (protections : ProtectedTags) (source selected : Option UniIndex) (maximum : Option BorTag)
    (lower width : UInt64)
    (outside : input.offset.toNat+input.len.toNat ≤ lower.toNat ∨ (lower+width).toNat ≤ input.offset.toNat)
    (profile : GeneralRangeMapState.Every (fun location => GeneralBorrowLocationSifaConsistency.Profile input.tree location protections) input.tree.locations)
    (held : protections.contains input.newTag = false)
    (old : Positive input.tree protections source selected maximum lower width) :
    (input.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) inside) (.ReservedFrz false) false).outcome = .ok () ∧
    Nonempty (Positive (GeneralBorrowFreshMetadataChildDefaultReuse.result input) protections source selected maximum lower width) := by
  have depth := GeneralBorrowFreshReuseNode.attached_depth input.tree.nodes input.depth input.index input.parent input.parentNode
    (child input.newTag input.parent) input.valid input.vacant input.parentPresent rfl input.parentSlack
  have allocator := GeneralBorrowFreshMetadataChildReuseAttach.allocator input.tree input.index input.parent input.parentNode
    (child input.newTag input.parent) input.valid input.vacant input.parentPresent (GeneralBorrowFreshMetadataChildDefaultReuse.mapping input)
    (GeneralBorrowFreshMetadataChildDefaultReuse.locations input) (GeneralBorrowFreshMetadataChildDefaultReuse.stage input) rfl
  have size : input.tree.nodes.size ≤ (attached input.tree input.index input.parent input.parentNode (child input.newTag input.parent)).nodes.size := by
    change input.tree.nodes.size ≤ (GeneralBorrowFreshMetadataChildDefaultReuse.stage input).nodes.size
    rw [allocator.2.2]
    exact Nat.le_refl _
  have positive := S02DisjointConstructorGenericPositive.after_sifa input.tree formed input.depth input.index input.parent input.parentNode
    (child input.newTag input.parent) inside
    input.vacant input.parentPresent (Or.inr input.valid) clean size depth rfl rfl rfl (S02SameDestinationAcceptedMutableForeign.foreign .Read) (S02SameDestinationAcceptedMutableForeign.query .Read) (GeneralBorrowFreshMetadataChildDefaultReuse.mapping input)
    protections source selected maximum input.offset input.len lower width input.well input.bounds outside .Read
      (by change GeneralBorrowSifaPermissionConsistency.Consistent ⟨.ReservedFrz false,false,.Read⟩ (protections.contains input.newTag);rw [held];exact GeneralBorrowSifaPermissionConsistency.unprotected_reservation false)
      (by change GeneralBorrowSifaPermissionConsistency.Consistent ⟨.ReservedFrz false,true,.Read⟩ (protections.contains input.newTag);rw [held];exact GeneralBorrowSifaPermissionConsistency.unprotected_reservation true) profile old
  refine ⟨(GeneralBorrowFreshMetadataChildDefaultReuse.reuse input).success,?_⟩
  rw [GeneralBorrowFreshMetadataChildDefaultReuse.tree_eq input]
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
    (held : protections.contains newTag = false)
    (old : Positive tree protections source selected maximum lower width) :
    let result := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) inside) (.ReservedFrz false) false
    result.outcome = .ok () ∧ Nonempty (Positive result.tree protections source selected maximum lower width) := by
  cases slot with
  | append noFree aligned fits =>
    exact append ⟨tree,depth,formed.children,formed.covered,parentTag,newTag,parent,parentNode,parentTagPresent,parentPresent,
      fresh,noFree,aligned,fits,offset,len,nonzero,well,bounds⟩ formed clean protections source selected maximum lower width outside profile held old
  | reuse index available bounded vacant slack =>
    exact reuse ⟨tree,depth,formed.children,formed.covered,parentTag,newTag,parent,parentNode,parentTagPresent,parentPresent,
      fresh,index,available,bounded,vacant,slack,offset,len,nonzero,well,bounds⟩ formed clean protections source selected maximum lower width outside profile held old

end DuplicatePrefix.S02SameDestinationAcceptedDefaultConstructor

open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S02SameDestinationAcceptedDefaultConstructor.append,``DuplicatePrefix.S02SameDestinationAcceptedDefaultConstructor.reuse,
      ``DuplicatePrefix.S02SameDestinationAcceptedDefaultConstructor.construct] do
    for ax in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "unapproved axiom {ax}"
