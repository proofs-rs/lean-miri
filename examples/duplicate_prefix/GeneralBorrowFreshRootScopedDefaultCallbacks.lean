import duplicate_prefix.GeneralBorrowFreshRootScopedConstructor
import duplicate_prefix.GeneralBorrowDefaultConstructorRuntime

namespace DuplicatePrefix.GeneralBorrowFreshRootScopedDefaultCallbacks
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshNode GeneralBorrowNodeUpdate GeneralRangeMapOrigins GeneralBorrowFreshDefaultChild
open GeneralBorrowFreshRootScopedSifa
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] UniValMap.insert

namespace Append
open GeneralBorrowFreshMetadataChildDefault
 theorem callbacks (input : Input) (formed : GeneralBorrowStructuralHistoryState.GraphState input.tree)
    (protections : ProtectedTags) (selected : UniIndex) (maximum : BorTag)
    (owned : OwnedOn (fun location => Nonempty (GeneralBorrowFreshRootScopedRow.Row input.tree location protections
      input.parent selected maximum)) input.offset (input.offset+input.len) input.tree.locations) :
    OwnedOn (Callbacks (result input) protections selected maximum) input.offset (input.offset+input.len) (result input).locations := by
  have atEnd := at_end input
  have vacant : input.tree.nodes.get (index input) = none := by simp [UniValMap.get,atEnd]
  have different := parent_not_fresh input.tree.nodes (index input) input.parent input.parentNode atEnd input.parentPresent
  have parentAfter : (input.tree.nodes.insert (index input) (child input.newTag input.parent)).get input.parent = some input.parentNode :=
    (GeneralBorrowFreshLocation.get_other _ (index input) input.parent _ different).trans input.parentPresent
  have size : input.tree.nodes.size ≤ (attachedNodes input.tree.nodes (index input) input.parent input.parentNode (child input.newTag input.parent)).size := by
    unfold attachedNodes
    rw [insert_existing_size _ input.parent input.parentNode _ parentAfter,append_size _ (index input) _ atEnd]
    omega
  let nextDepth := attached_depth input.tree.nodes input.depth (index input) input.parent input.parentNode
    (child input.newTag input.parent) atEnd input.parentPresent rfl
  have output := GeneralBorrowFreshRootScopedConstructor.staged input.tree formed input.depth (index input) input.parent input.parentNode (child input.newTag input.parent) inside .Read vacant input.parentPresent rfl
    size nextDepth (mapping input) protections selected maximum (Size.ofBytes input.offset) (Size.ofBytes input.len) input.well input.bounds owned
  rw [tree_eq input]
  exact output
end Append

namespace Reuse
open GeneralBorrowFreshMetadataChildDefaultReuse
 theorem callbacks (input : Input) (formed : GeneralBorrowStructuralHistoryState.GraphState input.tree)
    (protections : ProtectedTags) (selected : UniIndex) (maximum : BorTag)
    (owned : OwnedOn (fun location => Nonempty (GeneralBorrowFreshRootScopedRow.Row input.tree location protections
      input.parent selected maximum)) input.offset (input.offset+input.len) input.tree.locations) :
    OwnedOn (Callbacks (result input) protections selected maximum) input.offset (input.offset+input.len) (result input).locations := by
  have different := GeneralBorrowFreshReuseNode.parent_not_vacant input.tree.nodes input.index input.parent input.parentNode input.vacant input.parentPresent
  have parentAfter : (input.tree.nodes.insert input.index (child input.newTag input.parent)).get input.parent = some input.parentNode :=
    (GeneralBorrowFreshLocation.get_other _ input.index input.parent _ different).trans input.parentPresent
  have size : input.tree.nodes.size ≤ (attachedNodes input.tree.nodes input.index input.parent input.parentNode (child input.newTag input.parent)).size := by
    unfold attachedNodes
    rw [insert_existing_size _ input.parent input.parentNode _ parentAfter,
      GeneralBorrowFreshReuseNode.bounded_size _ input.index _ input.valid]
    exact Nat.le_refl _
  let nextDepth := GeneralBorrowFreshReuseNode.attached_depth input.tree.nodes input.depth input.index input.parent input.parentNode
    (child input.newTag input.parent) input.valid input.vacant input.parentPresent rfl input.parentSlack
  have output := GeneralBorrowFreshRootScopedConstructor.staged input.tree formed input.depth input.index input.parent input.parentNode (child input.newTag input.parent) inside .Read input.vacant input.parentPresent rfl
    size nextDepth (mapping input) protections selected maximum (Size.ofBytes input.offset) (Size.ofBytes input.len) input.well input.bounds owned
  rw [tree_eq input]
  exact output
end Reuse

/-- Full-source Default construction derives both other-root callback kinds on
the original owner window, with arbitrary coherent append/reuse pools. The
selected physical root and its cutoff are unchanged for parent and child. -/
theorem construct (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodes.get parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (tagBound : newTag.value.toNat < global.nextPointerTag.value.toNat)
    (unprotected : global.protectedTags.contains newTag = false)
    (selected : UniIndex) (maximum : BorTag) (offset len : UInt64)
    (positive : GeneralBorrowFreshRootScopedRow.Positive tree global.protectedTags parent selected maximum offset len) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) inside) (.ReservedFrz false) false
    actual.outcome = .ok () ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global ∧
    actual.tree.locations.size = tree.locations.size ∧ actual.tree.nodes.size ≤ tree.nodes.size+1 ∧
    ∃ child,actual.tree.indexOfTag newTag = some child ∧ actual.tree.roots = tree.roots ∧
      OwnedOn (Callbacks actual.tree global.protectedTags selected maximum) offset (offset+len) actual.tree.locations := by
  have nonzero : len ≠ 0 := by intro zero;rw [zero] at positive;have := positive.base.positive;contradiction
  have output := GeneralBorrowDefaultConstructorRuntime.construct tree global runtime parentTag newTag parent parentNode
    tagged present fresh room tagBound unprotected offset len nonzero positive.base.bounds
  refine ⟨output.1,output.2.1,output.2.2.1,output.2.2.2,?_⟩
  let rank := GeneralBorrowStructuralHistoryDefault.depth tree runtime.formed.toState
  have slot := GeneralBorrowStructuralHistoryDefault.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree accounting fits =>
    let input : GeneralBorrowFreshMetadataChildDefault.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        noFree,accounting,fits,offset,len,nonzero,runtime.formed.well,positive.base.bounds⟩
    have metadata := GeneralBorrowFreshMetadataChildDefault.append input
    exact ⟨GeneralBorrowFreshMetadataChildDefault.index input,metadata.freshLookup,metadata.roots,
      Append.callbacks input runtime.formed.toGraphState global.protectedTags selected maximum positive.rows⟩
  | reuse index available valid vacant slack =>
    let input : GeneralBorrowFreshMetadataChildDefaultReuse.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        index,available,valid,vacant,slack,offset,len,nonzero,runtime.formed.well,positive.base.bounds⟩
    have metadata := GeneralBorrowFreshMetadataChildDefaultReuse.reuse input
    exact ⟨index,metadata.freshLookup,metadata.roots,
      Reuse.callbacks input runtime.formed.toGraphState global.protectedTags selected maximum positive.rows⟩

end DuplicatePrefix.GeneralBorrowFreshRootScopedDefaultCallbacks
