import duplicate_prefix.GeneralBorrowSnapshotReadSupport
import duplicate_prefix.GeneralBorrowWildcardControlStack
namespace DuplicatePrefix.GeneralBorrowSnapshotReadDFSPlan
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization
open GeneralBorrowWildcardVirtualLeaf (effective)
open GeneralBorrowExposedNonleafState (ReadFrame)
open GeneralBorrowWildcardSubtreeStack
open GeneralBorrowWildcardPrimaryReadWitness (PointwiseReadFrame)
set_option autoImplicit false

def seen (location : LocationTree) (index : UniIndex) (node : TreeNode)
    (maximum : Option BorTag) (protections : ProtectedTags) (witness : Bool) : Bool :=
  if node.isExposed &&
      ((effective location index node).permission.strongestAllowedLocalAccess (protections.contains node.tag)).allows .Read &&
      (maximum.isNone || maximum.any (fun tag => tag.value >= node.tag.value)) then true else witness

/-- Ghost witness bookkeeping for the general source DFS proof. Virtual roots
instantiate pending with True; physical roots instantiate a concrete supporting
path. These are graph/Boolean invariant rules, not a caller success predicate. -/
structure WitnessPlan (tree : BorrowTree) (initialLocation : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag) where
  pending : Bool → Array Task → Prop
  initial : pending false #[(root,false)]
  finish : ∀ witness, pending witness #[] → (rootPosition != 0) = true ∨ witness = true
  pop : ∀ (location : LocationTree) (witness : Bool) (stack : Array Task) (index : UniIndex) (node : TreeNode),
    tree.nodes.get index = some node → ReadFrame initialLocation location → pending witness (stack.push (index,false)) →
    DuplicatePrefixCallbackVisitAuthorization.entrySkip (effective location index node) .Read
      (relation location root index node maximum .Read rootPosition) = true → pending witness stack
  expand : ∀ (witness : Bool) (stack : Array Task) (index : UniIndex) (node : TreeNode),
    tree.nodes.get index = some node → pending witness (stack.push (index,false)) →
    pending witness (expanded stack index node.children)
  post : ∀ (location : LocationTree) (witness : Bool) (stack : Array Task) (index : UniIndex) (node : TreeNode),
    tree.nodes.get index = some node → PointwiseReadFrame tree protections initialLocation location →
    pending witness (stack.push (index,true)) →
    pending (seen location index node maximum protections witness) stack

end DuplicatePrefix.GeneralBorrowSnapshotReadDFSPlan
