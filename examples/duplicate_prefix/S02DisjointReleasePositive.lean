import duplicate_prefix.S02DisjointReleaseFrame
import duplicate_prefix.S02ConstructorOutsideRow
import duplicate_prefix.GeneralBorrowReadProtectorRelease
import duplicate_prefix.GeneralBorrowHiddenProtectorRowWeakens
namespace DuplicatePrefix.S02DisjointReleasePositive
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixBorrowAuthorization GeneralBorrowFreshActiveWithin
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
/-- The real hidden Read-helper release preserves a disjoint owner's complete capability. -/
theorem release (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (tag : BorTag) (helper selected : UniIndex) (maximum : Option BorTag) (offset len : UInt64)
    (helperPositive : GeneralBorrowReadRowRange.Positive tree global.protectedTags helper selected maximum offset len)
    (node : TreeNode) (present : tree.nodeAt helper = some node) (hidden : node.isExposed = false)
    (tagged : tree.indexOfTag tag = some helper) (distinct : tree.roots.toList.Nodup)
    (order : ∀ valid : 0 < tree.roots.size, selected ≠ tree.roots[0] → GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (short : tree.nodes.size < 65536)
    (active : ActiveWithin tree helper .Read offset (offset+len))
    (source destinationSelected : Option UniIndex) (destinationMaximum : Option BorTag) (lower width : UInt64)
    (outside : (offset+len).toNat ≤ lower.toNat ∨ (lower+width).toNat ≤ offset.toNat)
    (destination : Positive tree global.protectedTags source destinationSelected destinationMaximum lower width) :
    Nonempty (Positive (tree.releaseProtector tag global.protectedTags).tree global.protectedTags source destinationSelected destinationMaximum lower width) := by
  obtain ⟨done,afterRuntime,afterPositive,afterActive,frame,capacity⟩ := GeneralBorrowReadProtectorRelease.release tree global runtime
    tag helper selected maximum offset len helperPositive node present hidden tagged distinct order short active
  have writeActive : ActiveWithin tree helper .Write offset (offset+len) := by
    intro point location atPoint state stored accessed kind associated
    have old := active point location atPoint state stored accessed kind associated
    exact ⟨old.1,old.2.1,by intro impossible;cases impossible⟩
  have kept := S02DisjointReleaseFrame.release tree global.protectedTags tag helper helper node tagged present hidden offset (offset+len)
    writeActive writeActive (fun location => Nonempty (Row tree location global.protectedTags source destinationSelected destinationMaximum))
    lower (lower+width) outside destination.rows runtime.formed.well
  refine ⟨{positive := destination.positive,bounds := ?_,sourcePresent := ?_,wildcardRoot := ?_,rows := ?_}⟩
  · rw [capacity];exact destination.bounds
  · intro anchor same
    rw [frame]
    exact destination.sourcePresent anchor same
  · intro same
    rw [frame]
    exact destination.wildcardRoot same
  · rw [frame]
    intro position valid nonempty start stop
    obtain ⟨row⟩ := kept position valid nonempty start stop
    exact S02ConstructorOutsideRow.context tree tree.tagMapping _ _ global.protectedTags source destinationSelected destinationMaximum row
/-- Dropping the singleton hidden helper protector preserves an arbitrary full owner. -/
theorem end_call (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (allocation : AllocId) (tag : BorTag) (anchor : UniIndex) (node : TreeNode)
    (present : tree.nodeAt anchor = some node) (sameTag : node.tag = tag) (hidden : node.isExposed = false)
    (source selected : Option UniIndex) (maximum : Option BorTag) (offset len : UInt64)
    (destination : Positive tree global.protectedTags source selected maximum offset len) :
    Nonempty (Positive tree (global.endCall (({} : FrameState).addProtector allocation tag)).protectedTags source selected maximum offset len) := by
  have protectorEq : (global.endCall (({} : FrameState).addProtector allocation tag)).protectedTags = global.protectedTags.remove tag := by
    simp only [GlobalState.endCall,FrameState.addProtector,Array.foldl_push,Array.foldl_empty]
  rw [protectorEq]
  apply GeneralBorrowHiddenProtectorRowWeakens.positive tree global.protectedTags (global.protectedTags.remove tag)
    (GeneralBorrowRelease.remove_weakens global.protectedTags tag) _ source selected maximum offset len destination
  intro index value found exposed
  have different : value.tag ≠ tag := by
    intro equal
    have first := runtime.formed.allocator.nodeTags index value found
    have second := runtime.formed.allocator.nodeTags anchor node present
    rw [equal,←sameTag,second] at first
    have equalIndex : index = anchor := (Option.some.inj first).symm
    subst index
    have equalNode := Option.some.inj (found.symm.trans present)
    subst value
    rw [hidden] at exposed
    contradiction
  unfold ProtectedTags.contains
  rw [GeneralBorrowProtectorCacheMap.remove_other global.protectedTags tag value.tag different]
end DuplicatePrefix.S02DisjointReleasePositive
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S02DisjointReleasePositive.release, ``DuplicatePrefix.S02DisjointReleasePositive.end_call] do
   for ax in (← collectAxioms name) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
