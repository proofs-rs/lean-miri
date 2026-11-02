import duplicate_prefix.GeneralBorrowWildcardControlReadWitness
namespace DuplicatePrefix.GeneralBorrowWildcardParentTagOrder
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposedNonleafPrimaryPath DuplicatePrefixCallbackAuthorization
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Independent raw graph condition. Current RuntimeFacts do not imply this
condition; necessity and valid-input coverage are separate obligations. -/
def ParentTagOrder (tree : BorrowTree) : Prop :=
  ∀ child childNode, tree.nodes.get child = some childNode → ∀ parent parentNode,
    childNode.parent = some parent → tree.nodes.get parent = some parentNode →
    parentNode.tag.value ≤ childNode.tag.value

theorem path_tag_le (tree : BorrowTree) (order : ParentTagOrder tree)
    (root witness : UniIndex) (path : Path tree root witness)
    (rootNode witnessNode : TreeNode) (rootPresent : tree.nodes.get root = some rootNode)
    (witnessPresent : tree.nodes.get witness = some witnessNode) :
    rootNode.tag.value ≤ witnessNode.tag.value := by
  induction path generalizing witnessNode with
  | refl node present =>
    have first := Option.some.inj (rootPresent.symm.trans present)
    have last := Option.some.inj (witnessPresent.symm.trans present)
    simp [first,last]
  | @step parent child earlier node present edge ih =>
    obtain ⟨parentNode,parentPresent⟩ := earlier.present
    have before := ih parentNode parentPresent
    have after := order child node present parent parentNode edge parentPresent
    have same := Option.some.inj (witnessPresent.symm.trans present)
    subst witnessNode
    exact Nat.le_trans before after

/-- An eligible supporter has no forced-foreign ancestor on a real witness
path under independent parent-tag ordering. No operation outcome is assumed. -/
theorem path_not_above (tree : BorrowTree) (order : ParentTagOrder tree)
    (location : LocationTree) (protections : ProtectedTags) (maximum : Option BorTag) (kind : AccessKind)
    (index witness : UniIndex) (node witnessNode : TreeNode)
    (present : tree.nodes.get index = some node) (witnessPresent : tree.nodes.get witness = some witnessNode)
    (path : Path tree index witness) (eligible : Supports location protections witness witnessNode maximum kind) :
    aboveMaximum node maximum = false := by
  have bounded := path_tag_le tree order index witness path node witnessNode present witnessPresent
  cases maximum with
  | none => rfl
  | some maximum =>
    have eligibleTag : witnessNode.tag.value ≤ maximum.value := by
      simpa only [Option.isNone_some,Option.any_some,Bool.false_or,decide_eq_true_eq] using eligible.2.2
    simp only [aboveMaximum,decide_eq_false_iff_not]
    exact Nat.not_lt.mpr (Nat.le_trans bounded eligibleTag)

end DuplicatePrefix.GeneralBorrowWildcardParentTagOrder
