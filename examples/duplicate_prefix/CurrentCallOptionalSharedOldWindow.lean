import duplicate_prefix.CurrentCallSpatialDefaultShared
import duplicate_prefix.CurrentCallOptionalLenFuture
namespace DuplicatePrefix.CurrentCallOptionalSharedOldWindow
open Miri Miri.ABI Miri.Memory Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership OrdinaryBorrowAuthority CurrentCallResourceNormalization
open GeneralBorrowView GeneralBorrowProjection GeneralRangeMapOrigins
open S05ConcreteProtectedChildCompletion
open S05CompletedAncestryReadMutable (Authority)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
open GeneralBorrowFreshGraph
open GeneralBorrowFreshAnchor (sharedNode sharedState)
noncomputable section

private theorem stage_owned (tree : BorrowTree) (completion : Completion) (held : ProtectedTags)
    (complete : ParentInterpretation tree completion) (source : UniIndex) (sourceLive : ∃ node, tree.nodes.get source = some node)
    (child parent : UniIndex) (parentNode : TreeNode) (tag : BorTag)
    (vacant : tree.nodes.get child = none) (parentAt : tree.nodes.get parent = some parentNode)
    (unheld : held.contains tag = false) (mapping : UniKeyMap BorTag)
    (offset len : UInt64) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (lower upper : UInt64) (insideLower : offset.toNat≤lower.toNat) (insideUpper : upper.toNat≤offset.toNat+len.toNat)
    (owned : OwnedOn (Authority tree completion held source) lower upper tree.locations) :
    let locations := (tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len)
      (fun _ location => GeneralBorrowFreshMaterialization.materialized location child sharedState)).state
    let stage := GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode
      (sharedNode tag parent) mapping locations
    OwnedOn (Authority stage (extend completion child parent) held source) lower upper locations := by
  let locations := (tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len)
    (fun _ location => GeneralBorrowFreshMaterialization.materialized location child sharedState)).state
  let stage := GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode
    (sharedNode tag parent) mapping locations
  refine (spatial_install_rule ".CurrentCallSharedConstructorWindow.modify_owned") tree.locations (Size.ofBytes offset) (Size.ofBytes len) well bounds
    (fun location => GeneralBorrowFreshMaterialization.materialized location child sharedState)
    (fun location => GeneralBorrowFreshInstallation.materialized_idempotent location child sharedState)
    (Authority tree completion held source) (Authority stage (extend completion child parent) held source) ?_ lower upper insideLower insideUpper owned
  intro location authority
  exact (spatial_install_rule ".CurrentCallOptionalSharedOldAuthority.stage_location") tree completion held complete source sourceLive child parent parentNode tag vacant parentAt unheld mapping locations location authority

theorem construct_window (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (complete : ParentInterpretation tree completion)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (tagBound : newTag.value.toNat < global.nextPointerTag.value.toNat)
    (unheld : global.protectedTags.contains newTag = false)
    (source : UniIndex) (sourceLive : ∃ node, tree.nodes.get source = some node)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (lower upper : UInt64) (insideLower : offset.toNat≤lower.toNat) (insideUpper : upper.toNat≤offset.toNat+len.toNat)
    (owned : OwnedOn (Authority tree completion global.protectedTags source) lower upper tree.locations) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) sharedState) .Frozen false
    actual.outcome = .ok () ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global ∧
      actual.tree.locations.size = tree.locations.size ∧ actual.tree.nodes.size ≤ tree.nodes.size+1 ∧
      ∃ child, actual.tree.indexOfTag newTag = some child ∧
        OwnedOn (Authority actual.tree (extend completion child parent) global.protectedTags source)
          lower upper actual.tree.locations := by
  obtain ⟨done,afterRuntime,capacity,growth⟩ := GeneralBorrowSharedConstructorRuntime.construct
    tree global runtime parentTag newTag parent parentNode tagged present fresh room tagBound false unheld offset len nonzero bounds
  obtain ⟨child,lookup,_,_⟩ := GeneralBorrowSharedChildGraph.construct
    tree global runtime parentTag newTag parent parentNode tagged present fresh room false offset len nonzero bounds
  refine ⟨done,afterRuntime,capacity,growth,child,lookup,?_⟩
  let rank := GeneralBorrowStructuralHistoryShared.depth tree runtime.formed.toState
  let slot := GeneralBorrowStructuralHistoryShared.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildShared.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        noFree,aligned,fits,false,offset,len,nonzero,runtime.formed.well,bounds⟩
    have data := GeneralBorrowFreshMetadataChildShared.append input
    have same : GeneralBorrowFreshMetadataChildShared.index input = child := Option.some.inj (data.freshLookup.symm.trans lookup)
    have atEnd : (GeneralBorrowFreshMetadataChildShared.index input).toNat = tree.nodes.data.size :=
      GeneralBorrowFreshMetadataChildShared.at_end input
    have vacant : tree.nodes.get (GeneralBorrowFreshMetadataChildShared.index input) = none := by
      simp only [UniValMap.get,atEnd,Array.getElem?_eq_none (Nat.le_refl _)]
    have staged := stage_owned tree completion global.protectedTags complete source sourceLive _ parent parentNode newTag vacant present unheld
      (GeneralBorrowFreshMetadataChildShared.mapping input) offset len runtime.formed.well bounds lower upper insideLower insideUpper owned
    have result := (spatial_install_rule ".CurrentCallOptionalSharedOldAuthority.shape_owned") (GeneralBorrowFreshMetadataChildShared.stage input)
      (GeneralBorrowFreshMetadataChildShared.result input) _ global.protectedTags source lower upper
      (GeneralBorrowFreshMetadataChildShared.shape input) staged
    rw [same] at result
    simpa only [GeneralBorrowFreshMetadataChildShared.result,input] using result
  | reuse index available bounded vacant slack =>
    let input : GeneralBorrowFreshMetadataChildSharedReuse.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        index,available,bounded,vacant,slack,false,offset,len,nonzero,runtime.formed.well,bounds⟩
    have data := GeneralBorrowFreshMetadataChildSharedReuse.reuse input
    have same : index = child := Option.some.inj (data.freshLookup.symm.trans lookup)
    have staged := stage_owned tree completion global.protectedTags complete source sourceLive index parent parentNode newTag vacant present unheld
      (GeneralBorrowFreshMetadataChildSharedReuse.mapping input) offset len runtime.formed.well bounds lower upper insideLower insideUpper owned
    have result := (spatial_install_rule ".CurrentCallOptionalSharedOldAuthority.shape_owned") (GeneralBorrowFreshMetadataChildSharedReuse.stage input)
      (GeneralBorrowFreshMetadataChildSharedReuse.result input) _ global.protectedTags source lower upper
      (GeneralBorrowFreshMetadataChildSharedReuse.shape input) staged
    rw [same] at result
    simpa only [GeneralBorrowFreshMetadataChildSharedReuse.result,input] using result

theorem future (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (complete : ParentInterpretation tree completion)
    (allocation : AllocId) (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (nodeFresh : GeneralBorrowProtector.Fresh tree newTag)
    (room : tree.nodes.size+1 ≤ 4294967295) (tagBound : newTag.value.toNat < global.nextPointerTag.value.toNat)
    (source : UniIndex) (sourceLive : ∃ node, tree.nodes.get source = some node)
    (offset len : UInt64) (nonzero : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (lower upper : UInt64) (insideLower : offset.toNat≤lower.toNat) (insideUpper : upper.toNat≤offset.toNat+len.toNat)
    (owned : OwnedOn (S05CompletedAncestryReadMutable.Authority tree completion
      (global.endCall (({} : FrameState).addProtector allocation newTag)).protectedTags source)
      lower upper tree.locations) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen true
    ∃ child, actual.tree.indexOfTag newTag = some child ∧
      OwnedOn (S05CompletedAncestryReadMutable.Authority actual.tree (extend completion child parent)
        (global.endCall (({} : FrameState).addProtector allocation newTag)).protectedTags source)
        lower upper actual.tree.locations := by
  let future := global.endCall (({} : FrameState).addProtector allocation newTag)
  have futureRuntime : DuplicatePrefixBorrowContract.RuntimeFacts tree future := by
    apply (spatial_install_rule ".CurrentCallOptionalLenFuture.absent_tag_view") tree global runtime allocation newTag
    intro index node found
    exact nodeFresh (index,node) (Array.mem_toList_iff.mp
      ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes index node).mpr found))
  have unheld : future.protectedTags.contains newTag = false := by
    change (global.protectedTags.remove newTag).contains newTag = false
    simp only [ProtectedTags.contains,ProtectedTags.get_remove_same,Option.isSome_none]
  obtain ⟨_,_,_,_,child,lookup,authority⟩ := construct_window tree future completion
    futureRuntime complete parentTag newTag parent parentNode tagged present fresh room tagBound unheld source sourceLive
    offset len nonzero bounds lower upper insideLower insideUpper owned
  have same := (spatial_install_rule ".CurrentCallOptionalLenFuture.shared_held_tree") tree global runtime parentTag newTag parent parentNode tagged present fresh room true false offset len nonzero bounds
  refine ⟨child,?_,?_⟩
  · rw [same];exact lookup
  · rw [same];exact authority
theorem future_parents (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (complete : ParentInterpretation tree completion)
    (allocation : AllocId) (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (nodeFresh : GeneralBorrowProtector.Fresh tree newTag)
    (room : tree.nodes.size+1 ≤ 4294967295) (tagBound : newTag.value.toNat < global.nextPointerTag.value.toNat)
    (source : UniIndex) (sourceLive : ∃ node, tree.nodes.get source = some node)
    (offset len : UInt64) (nonzero : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (lower upper : UInt64) (insideLower : offset.toNat≤lower.toNat) (insideUpper : upper.toNat≤offset.toNat+len.toNat)
    (primaryLive : ∃node,tree.nodes.get allocationRoot=some node)
    (parentOrder : parentNode.tag.value≤newTag.value)
    (owned : OwnedOn (S05CompletedAncestryReadMutable.Authority tree completion
      (global.endCall (({} : FrameState).addProtector allocation newTag)).protectedTags source)
      lower upper tree.locations) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen true
    ∃ child, actual.tree.indexOfTag newTag = some child ∧
      ParentInterpretation actual.tree (extend completion child parent) ∧
      OwnedOn (S05CompletedAncestryReadMutable.Authority actual.tree (extend completion child parent)
        (global.endCall (({} : FrameState).addProtector allocation newTag)).protectedTags source)
        lower upper actual.tree.locations := by
  obtain ⟨child,lookup,ownedAfter⟩ := future tree global completion runtime complete allocation parentTag newTag parent parentNode
    tagged present fresh nodeFresh room tagBound source sourceLive offset len nonzero bounds lower upper insideLower insideUpper owned
  let afterGlobal:=global.endCall (({} : FrameState).addProtector allocation newTag)
  have afterRuntime : DuplicatePrefixBorrowContract.RuntimeFacts tree afterGlobal := by
    apply (spatial_install_rule ".CurrentCallOptionalLenFuture.absent_tag_view") tree global runtime allocation newTag
    intro index node found
    exact nodeFresh (index,node) (Array.mem_toList_iff.mp ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes index node).mpr found))
  have unheld : afterGlobal.protectedTags.contains newTag=false := by
    change (global.protectedTags.remove newTag).contains newTag=false
    simp only [ProtectedTags.contains,ProtectedTags.get_remove_same,Option.isSome_none]
  obtain ⟨_,runtimeFalse,_,_,other,otherLookup,leaf,_⟩ := CurrentCallSharedConstructorFrame.metadata tree afterGlobal afterRuntime
    parentTag newTag parent parentNode tagged present fresh room tagBound unheld offset len nonzero bounds
  have sameTree := (spatial_install_rule ".CurrentCallOptionalLenFuture.shared_held_tree") tree global runtime parentTag newTag parent parentNode tagged present fresh room true false offset len nonzero bounds
  have same : other=child := by
    rw [sameTree] at lookup
    exact Option.some.inj (otherLookup.symm.trans lookup)
  subst other
  have order:=GeneralBorrowSharedChildParentTagOrder.construct tree global runtime parentTag newTag parent parentNode
    tagged present fresh room true offset len nonzero bounds complete.order parentOrder
  refine ⟨child,lookup,?_,ownedAfter⟩
  apply CurrentCallParentInsertion.of_leaf tree _ completion complete child parent _ primaryLive _ order
  · rw [sameTree];exact leaf
  · rw [sameTree];exact runtimeFalse.formed.toGraphState

end
end DuplicatePrefix.CurrentCallOptionalSharedOldWindow
