import duplicate_prefix.GeneralBorrowExposedScopedRestore
import duplicate_prefix.GeneralBorrowFreshSharedPrefix
import duplicate_prefix.GeneralBorrowExposedScopedLeafWriteSeed
import duplicate_prefix.GeneralBorrowProtectorCacheMap
namespace DuplicatePrefix.GeneralBorrowExposedScopedRestoredWriteData
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralBorrowProjection
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- The post-read mixed component itself proves that the registered helper
is hidden. Raw node/tag accounting excludes any exposed node with its tag. -/
theorem helper_hidden (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (child selected head : UniIndex) (tail : List UniIndex) (support : Nat → Prop) (writable : Nat → Bool)
    (data : GeneralBorrowExposedScopedMixedRangeData.Data tree location protections child selected head tail support writable)
    (node : TreeNode) (present : tree.nodeAt child=some node)
    (nodeTags : ∀ index value,tree.nodeAt index=some value → tree.indexOfTag value.tag=some index) :
    ∀ index value,tree.nodeAt index=some value → value.tag=node.tag → value.isExposed=false := by
  intro index value found tag
  have one:=nodeTags index value found
  have two:=nodeTags child node present
  rw [tag,two] at one
  have same : child=index:=Option.some.inj one
  subst index
  have equal : value=node:=Option.some.inj (found.symm.trans present)
  subst value
  exact data.base.hidden child node data.base.component.anchor present

/-- Actual singleton helper endCall retains cache coherence because its helper
belongs to the hidden component. No post-endCall cache premise is needed. -/
theorem coherent (tree : BorrowTree) (location : LocationTree) (global : GlobalState)
    (allocation : AllocId) (child selected head : UniIndex) (tail : List UniIndex)
    (support : Nat → Prop) (writable : Nat → Bool)
    (data : GeneralBorrowExposedScopedMixedRangeData.Data tree location global.protectedTags child selected head tail support writable)
    (node : TreeNode) (present : tree.nodeAt child=some node)
    (nodeTags : ∀ index value,tree.nodeAt index=some value → tree.indexOfTag value.tag=some index) :
    GeneralBorrowExposureCardinality.LocationCoherent tree location
      (global.endCall (({} : FrameState).addProtector allocation node.tag)).protectedTags := by
  have hidden:=helper_hidden tree location global.protectedTags child selected head tail support writable data node present nodeTags
  have kept:=GeneralBorrowProtectorCacheMap.remove_hidden tree location global.protectedTags node.tag data.base.coherent hidden
  simpa only [GlobalState.endCall,FrameState.addProtector,Array.foldl_push,Array.foldl_empty] using kept

/-- Recover an older target's full scoped Write data from actual helper
post-read/release mixed rows and the real endCall. Outside exposed leaves are
raw retained Unique states; no restored Write profile or successful operation
is accepted. -/
noncomputable def restore (tree : BorrowTree) (location : LocationTree) (global : GlobalState)
    (allocation : AllocId) (child target selected head : UniIndex) (tail : List UniIndex)
    (support : Nat → Prop) (writable : Nat → Bool)
    (data : GeneralBorrowExposedScopedMixedRangeData.Data tree location global.protectedTags child selected head tail support writable)
    (context : GeneralBorrowExposedKnownRootRangeData.Context tree target selected head tail)
    (childNode : TreeNode) (childPresent : tree.nodeAt child=some childNode)
    (nodeTags : ∀ index value,tree.nodeAt index=some value → tree.indexOfTag value.tag=some index)
    (targetSupported : support target.toNat)
    (restoration : GeneralBorrowFreshLifetimeRestore.RestoreTo tree global.protectedTags
      (global.endCall (({} : FrameState).addProtector allocation childNode.tag)).protectedTags child target writable)
    (rootPath : ((source_normal_projection tree location global.protectedTags).topology.ancestorPath target.toNat).getLast!=selected.toNat)
    (short : tree.nodes.size<65536)
    (leaves : ∀ index,area.support index → ∃ node,tree.nodeAt index=some node ∧ node.children=#[] ∧ node.isExposed=true ∧
      GeneralBorrowWildcardVirtualLeaf.effective location index node=GeneralBorrowWildcardLeaf.unique)
    (first : head≠selected → area.support head) (rest : ∀ root∈tail,root≠selected → area.support root) :
    GeneralBorrowExposedKnownRootRangeData.Data tree location
      (global.endCall (({} : FrameState).addProtector allocation childNode.tag)).protectedTags target selected head tail .Write := by
  let after:=(global.endCall (({} : FrameState).addProtector allocation childNode.tag)).protectedTags
  let component : GeneralBorrowExposedScopedNormal.Component (source_normal_projection tree location after).topology target.toNat:={
    support:=data.base.component.support
    anchor:=by rw [data.support_eq];exact targetSupported
    parents:=data.base.component.parents
    children:=data.base.component.children }
  have mixed:=GeneralBorrowExposedScopedRestore.location tree location global.protectedTags after
    (GeneralBorrowRelease.end_call_weakens global _) child target support writable restoration data.mixed
  exact GeneralBorrowExposedScopedLeafWriteSeed.seed tree location after target selected head tail support context data.base.forest
    component data.support_eq mixed rootPath data.base.hidden data.base.separate
    (coherent tree location global allocation child selected head tail support writable data childNode childPresent nodeTags) short leaves first rest
end DuplicatePrefix.GeneralBorrowExposedScopedRestoredWriteData
