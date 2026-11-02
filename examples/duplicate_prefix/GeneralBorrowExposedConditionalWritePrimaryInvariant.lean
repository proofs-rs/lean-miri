import duplicate_prefix.GeneralBorrowExposedConditionalWritePrimaryWitness
import duplicate_prefix.GeneralBorrowExposedConditionalWriteInvariant
namespace DuplicatePrefix.GeneralBorrowExposedConditionalWritePrimaryInvariant
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowWildcardSubtreeData (Weights)
open GeneralBorrowWildcardSubtreeStack
open GeneralBorrowExposedNonleafState (updated)
open GeneralBorrowExposedConditionalWriteState
open GeneralBorrowExposedConditionalWriteInvariant (LoopState)
open GeneralBorrowExposedConditionalWritePrimaryWitness (Data Pending)
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

structure Invariant {tree initial root protections} (weights : Weights tree)
    (data : GeneralBorrowExposedConditionalWritePrimaryWitness.Data tree initial root protections) (state : LoopState) : Prop where
  base : GeneralBorrowExposedConditionalWriteInvariant.Invariant weights data.base none state
  witness : Pending tree data.witness state.2.1 state.2.2.2.1

theorem initial {tree location root protections} (weights : Weights tree) (data : GeneralBorrowExposedConditionalWritePrimaryWitness.Data tree location root protections) :
    Invariant weights data (location,false,.Completed,#[(root,false)],0) :=
  ⟨GeneralBorrowExposedConditionalWriteInvariant.initial weights data.base none,GeneralBorrowExposedConditionalWritePrimaryWitness.initial data⟩

theorem pop {tree initial root protections} (weights : Weights tree) (data : GeneralBorrowExposedConditionalWritePrimaryWitness.Data tree initial root protections)
    (location : LocationTree) (seen : Bool) (stack : Array Task) (index : UniIndex) (steps : Nat)
    (valid : Invariant weights data (location,seen,.Completed,stack.push (index,false),steps))
    (positive : 1 ≤ cost weights.weight (index,false))
    (zero : GeneralBorrowWildcardRelatednessBounds.count initial.exposedCache index .Write = 0) :
    Invariant weights data (location,seen,.Completed,stack,steps+1) :=
  ⟨GeneralBorrowExposedConditionalWriteInvariant.pop weights data.base none location seen stack (index,false) steps valid.base positive,
    GeneralBorrowExposedConditionalWritePrimaryWitness.pop data seen stack index false valid.witness zero⟩

theorem expand {tree initial root protections} (weights : Weights tree) (data : GeneralBorrowExposedConditionalWritePrimaryWitness.Data tree initial root protections)
    (location : LocationTree) (seen : Bool) (stack : Array Task) (index : UniIndex) (node : TreeNode) (steps : Nat)
    (valid : Invariant weights data (location,seen,.Completed,stack.push (index,false),steps))
    (present : tree.nodes.get index = some node)
    (recurse : foreign initial index node none = true → (GeneralBorrowWildcardVirtualLeaf.effective location index node).skipIfKnownNoop .Write .ForeignAccess = .Recurse) :
    Invariant weights data (location,seen,.Completed,expanded stack index node.children,steps+1) :=
  ⟨GeneralBorrowExposedConditionalWriteInvariant.expand weights data.base none location seen stack index node steps valid.base present recurse,
    GeneralBorrowExposedConditionalWritePrimaryWitness.expand data seen stack index node present valid.witness⟩

theorem post {tree initial root protections} (weights : Weights tree) (data : GeneralBorrowExposedConditionalWritePrimaryWitness.Data tree initial root protections)
    (location after : LocationTree) (seen afterSeen : Bool) (stack : Array Task) (index : UniIndex) (steps : Nat)
    (valid : Invariant weights data (location,seen,.Completed,stack.push (index,true),steps))
    (frame : WriteFrame location after) (profile : Profile tree after protections)
    (unchanged : ∀ query, query ≠ index → after.perms.get query = location.perms.get query)
    (monotone : seen = true → afterSeen = true) (found : index = data.witness → afterSeen = true)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree after protections) :
    Invariant weights data (after,afterSeen,.Completed,stack,steps+1) :=
  ⟨GeneralBorrowExposedConditionalWriteInvariant.post weights data.base none location after seen afterSeen stack index steps valid.base frame profile unchanged coherent,
    GeneralBorrowExposedConditionalWritePrimaryWitness.post seen afterSeen stack index valid.witness monotone found⟩
end DuplicatePrefix.GeneralBorrowExposedConditionalWritePrimaryInvariant
