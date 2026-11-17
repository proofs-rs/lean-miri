import duplicate_prefix.GeneralBorrowSnapshotReadDFSEffectsInvariant
import duplicate_prefix.GeneralBorrowSnapshotReadTransfer
import duplicate_prefix.GeneralBorrowSnapshotReadWriteEffects
import duplicate_prefix.GeneralBorrowSnapshotReadDFSRuntimeData
namespace DuplicatePrefix.GeneralBorrowSnapshotReadDFSTransferInvariant
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization
open GeneralBorrowWildcardVirtualLeaf (effective)
open GeneralBorrowExposedNonleafState (ReadFrame)
open GeneralBorrowWildcardSubtreeData (Weights)
open GeneralBorrowWildcardSubtreeStack
open GeneralBorrowWildcardPrimaryReadWitness (PointwiseReadFrame)
open GeneralBorrowSnapshotReadDFSPlan
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

abbrev LoopState := GeneralBorrowSnapshotReadDFSEffectsInvariant.LoopState

/-- Proof bookkeeping extends the original graph/snapshot invariant without
changing its API or any interpreter argument. -/
structure Invariant (enabled effectsEnabled : Bool) {tree : BorrowTree} {initial : LocationTree} {protections : ProtectedTags}
    {root : UniIndex} {rootPosition : Nat} {maximum : Option BorTag}
    (weights : Weights tree) (support : GeneralBorrowWildcardControlStack.Support tree root)
    (plan : WitnessPlan tree initial protections root rootPosition maximum) (state : LoopState) : Prop
    extends toEffects : GeneralBorrowSnapshotReadDFSEffectsInvariant.Invariant enabled effectsEnabled weights support plan state where
  transfer : GeneralBorrowSnapshotReadTransfer.Global tree initial state.1 protections root rootPosition maximum support.contains

theorem initial {tree : BorrowTree} {location : LocationTree} {protections : ProtectedTags}
    {enabled effectsEnabled : Bool} {root : UniIndex} {rootPosition : Nat} {maximum : Option BorTag}
    (weights : Weights tree) (support : GeneralBorrowWildcardControlStack.Support tree root)
    (plan : WitnessPlan tree location protections root rootPosition maximum)
    (snapshot : Snapshot tree location protections root rootPosition maximum .Read support.contains)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (runtime : enabled = true → GeneralBorrowLocationSifaConsistency.Profile tree location protections ∧ GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location) :
    Invariant enabled effectsEnabled weights support plan (location,false,.Completed,#[(root,false)],0) := by
  exact ⟨GeneralBorrowSnapshotReadDFSEffectsInvariant.initial weights support plan snapshot coherent runtime,
    GeneralBorrowSnapshotReadTransfer.initial tree location protections root rootPosition maximum support.contains⟩

theorem pop {tree : BorrowTree} {initial : LocationTree} {protections : ProtectedTags}
    {enabled effectsEnabled : Bool} {root : UniIndex} {rootPosition : Nat} {maximum : Option BorTag}
    (weights : Weights tree) (support : GeneralBorrowWildcardControlStack.Support tree root)
    (plan : WitnessPlan tree initial protections root rootPosition maximum)
    (location : LocationTree) (witness : Bool) (stack : Array Task) (index : UniIndex) (node : TreeNode) (steps : Nat)
    (valid : Invariant enabled effectsEnabled weights support plan (location,witness,.Completed,stack.push (index,false),steps))
    (present : tree.nodes.get index = some node)
    (skipped : DuplicatePrefixCallbackVisitAuthorization.entrySkip (effective location index node) .Read
      (relation location root index node maximum .Read rootPosition) = true) :
    Invariant enabled effectsEnabled weights support plan (location,witness,.Completed,stack,steps+1) := by
  exact ⟨GeneralBorrowSnapshotReadDFSEffectsInvariant.pop weights support plan location witness stack index node steps valid.toEffects present skipped,valid.transfer⟩

theorem expand {tree : BorrowTree} {initial : LocationTree} {protections : ProtectedTags}
    {enabled effectsEnabled : Bool} {root : UniIndex} {rootPosition : Nat} {maximum : Option BorTag}
    (weights : Weights tree) (support : GeneralBorrowWildcardControlStack.Support tree root)
    (plan : WitnessPlan tree initial protections root rootPosition maximum)
    (location : LocationTree) (witness : Bool) (stack : Array Task) (index : UniIndex) (node : TreeNode) (steps : Nat)
    (valid : Invariant enabled effectsEnabled weights support plan (location,witness,.Completed,stack.push (index,false),steps))
    (present : tree.nodes.get index = some node)
    (recurse : DuplicatePrefixCallbackVisitAuthorization.entrySkip (effective location index node) .Read
      (relation location root index node maximum .Read rootPosition) = false) :
    Invariant enabled effectsEnabled weights support plan (location,witness,.Completed,expanded stack index node.children,steps+1) := by
  exact ⟨GeneralBorrowSnapshotReadDFSEffectsInvariant.expand weights support plan location witness stack index node steps valid.toEffects present recurse,valid.transfer⟩

theorem post {tree : BorrowTree} {initial : LocationTree} {protections : ProtectedTags}
    {enabled effectsEnabled : Bool} {root : UniIndex} {rootPosition : Nat} {maximum : Option BorTag}
    (weights : Weights tree) (support : GeneralBorrowWildcardControlStack.Support tree root)
    (plan : WitnessPlan tree initial protections root rootPosition maximum)
    (location after : LocationTree) (witness : Bool) (stack : Array Task) (index : UniIndex) (node : TreeNode) (steps : Nat)
    (valid : Invariant enabled effectsEnabled weights support plan (location,witness,.Completed,stack.push (index,true),steps))
    (present : tree.nodes.get index = some node)
    (snapshot : Snapshot tree after protections root rootPosition maximum .Read support.contains)
    (frame : ReadFrame location after)
    (pointwise : PointwiseReadFrame tree protections location after)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree after protections)
    (other : ∀ query, query ≠ index → after.perms.get query = location.perms.get query)
    (runtime : enabled = true → GeneralBorrowLocationSifaConsistency.Profile tree after protections ∧ GeneralBorrowSnapshotReadRuntime.GlobalPossible tree after)
    (effects : effectsEnabled = true → GeneralBorrowSnapshotReadWriteEffects.Effects tree initial after protections maximum)
    (transfer : GeneralBorrowSnapshotReadTransfer.Global tree initial after protections root rootPosition maximum support.contains) :
    Invariant enabled effectsEnabled weights support plan
      (after,seen location index node maximum protections witness,.Completed,stack,steps+1) := by
  exact ⟨GeneralBorrowSnapshotReadDFSEffectsInvariant.post weights support plan location after witness stack index node steps valid.toEffects present snapshot frame pointwise coherent other runtime effects,transfer⟩

end DuplicatePrefix.GeneralBorrowSnapshotReadDFSTransferInvariant
