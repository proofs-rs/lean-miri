import duplicate_prefix.GeneralBorrowExposedConditionalReadPrimaryWitness
import duplicate_prefix.GeneralBorrowExposedConditionalReadExactInvariant
namespace DuplicatePrefix.GeneralBorrowExposedConditionalReadExactPrimaryInvariant
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowWildcardSubtreeData (Weights)
open GeneralBorrowWildcardSubtreeStack
open GeneralBorrowExposedNonleafState (ReadFrame foreign)
open GeneralBorrowExposedConditionalReadState
open GeneralBorrowExposedConditionalReadExactInvariant (LoopState)
open GeneralBorrowExposedConditionalReadPrimaryWitness (Data Pending)
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

structure Invariant {tree initial root protections} (weights : Weights tree)
    (data : GeneralBorrowExposedConditionalReadPrimaryWitness.Data tree initial root protections) (state : LoopState) : Prop where
  base : GeneralBorrowExposedConditionalReadExactInvariant.Invariant weights data.base none state
  witness : Pending tree data.witness state.2.1 state.2.2.2.1

theorem initial {tree location root protections} (weights : Weights tree) (data : GeneralBorrowExposedConditionalReadPrimaryWitness.Data tree location root protections) :
    Invariant weights data (location,false,.Completed,#[(root,false)],0) :=
  ⟨GeneralBorrowExposedConditionalReadExactInvariant.initial weights data.base none,GeneralBorrowExposedConditionalReadPrimaryWitness.initial data⟩

theorem pop {tree initial root protections} (weights : Weights tree) (data : GeneralBorrowExposedConditionalReadPrimaryWitness.Data tree initial root protections)
    (location : LocationTree) (seen : Bool) (stack : Array Task) (index : UniIndex) (steps : Nat)
    (valid : Invariant weights data (location,seen,.Completed,stack.push (index,false),steps))
    (positive : 1 ≤ cost weights.weight (index,false))
    (zero : GeneralBorrowWildcardRelatednessBounds.count initial.exposedCache index .Read = 0) :
    Invariant weights data (location,seen,.Completed,stack,steps+1) :=
  ⟨GeneralBorrowExposedConditionalReadExactInvariant.pop weights data.base none location seen stack (index,false) steps valid.base positive,
    GeneralBorrowExposedConditionalReadPrimaryWitness.pop data seen stack index false valid.witness zero⟩

theorem expand {tree initial root protections} (weights : Weights tree) (data : GeneralBorrowExposedConditionalReadPrimaryWitness.Data tree initial root protections)
    (location : LocationTree) (seen : Bool) (stack : Array Task) (index : UniIndex) (node : TreeNode) (steps : Nat)
    (valid : Invariant weights data (location,seen,.Completed,stack.push (index,false),steps))
    (present : tree.nodes.get index = some node)
    (recurse : foreign initial index node none = true → (GeneralBorrowWildcardVirtualLeaf.effective location index node).skipIfKnownNoop .Read .ForeignAccess = .Recurse) :
    Invariant weights data (location,seen,.Completed,expanded stack index node.children,steps+1) :=
  ⟨GeneralBorrowExposedConditionalReadExactInvariant.expand weights data.base none location seen stack index node steps valid.base present recurse,
    GeneralBorrowExposedConditionalReadPrimaryWitness.expand data seen stack index node present valid.witness⟩

theorem post {tree initial root protections} (weights : Weights tree) (data : GeneralBorrowExposedConditionalReadPrimaryWitness.Data tree initial root protections)
    (location after : LocationTree) (seen afterSeen : Bool) (stack : Array Task) (index : UniIndex) (steps : Nat)
    (valid : Invariant weights data (location,seen,.Completed,stack.push (index,true),steps))
    (frame : ReadFrame location after) (readable : Readable tree after protections)
    (unchanged : ∀ query, query ≠ index → after.perms.get query = location.perms.get query)
    (monotone : seen = true → afterSeen = true) (found : index = data.witness → afterSeen = true)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree after protections)
    (cache : after.exposedCache = location.exposedCache) :
    Invariant weights data (after,afterSeen,.Completed,stack,steps+1) :=
  ⟨GeneralBorrowExposedConditionalReadExactInvariant.post weights data.base none location after seen afterSeen stack index steps valid.base frame readable unchanged coherent cache,
    GeneralBorrowExposedConditionalReadPrimaryWitness.post seen afterSeen stack index valid.witness monotone found⟩
end DuplicatePrefix.GeneralBorrowExposedConditionalReadExactPrimaryInvariant
