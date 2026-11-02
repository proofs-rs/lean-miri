import duplicate_prefix.GeneralBorrowExposedNonleafPrimaryState
namespace DuplicatePrefix.GeneralBorrowExposedNonleafPrimaryPath
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposedNonleafState
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

inductive Path (tree : BorrowTree) : UniIndex → UniIndex → Prop
  | refl (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node) : Path tree index index
  | step {root parent child : UniIndex} (earlier : Path tree root parent) (node : TreeNode)
      (present : tree.nodes.get child = some node) (edge : node.parent = some parent) : Path tree root child

def Reciprocal (tree : BorrowTree) : Prop :=
  ∀ child node, tree.nodes.get child = some node → ∀ parent, node.parent = some parent →
    ∃ parentNode, tree.nodes.get parent = some parentNode ∧ child ∈ parentNode.children.toList

theorem Path.present {tree root index} (path : Path tree root index) : ∃ node, tree.nodes.get index = some node := by
  cases path with
  | refl node present => exact ⟨node,present⟩
  | step earlier node present edge => exact ⟨node,present⟩

theorem Path.first {tree root witness} (path : Path tree root witness)
    (graph : Reciprocal tree) (different : root ≠ witness) :
    ∃ node child, tree.nodes.get root = some node ∧ child ∈ node.children.toList ∧ Path tree child witness := by
  induction path with
  | refl node present => exact False.elim (different rfl)
  | @step parent child earlier node present edge ih =>
    by_cases same : root = parent
    · subst parent
      obtain ⟨parentNode,parentPresent,member⟩ := graph child node present root edge
      exact ⟨parentNode,child,parentPresent,member,.refl child node present⟩
    · obtain ⟨parentNode,first,parentPresent,member,path⟩ := ih same
      exact ⟨parentNode,first,parentPresent,member,.step path node present edge⟩

theorem Path.walk {tree root witness} (path : Path tree root witness)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) :
    root ∈ GeneralBorrowExposureAncestorFold.walk tree.nodes (tree.nodes.size+1) witness := by
  have run : ∀ fuel index, ∀ node, tree.nodes.get index = some node → depth.depth index < fuel →
      Path tree root index → root ∈ GeneralBorrowExposureAncestorFold.walk tree.nodes fuel index := by
    intro fuel
    induction fuel with
    | zero => intro index node present bound path;omega
    | succ fuel ih =>
      intro index node present bound path
      cases path with
      | refl old oldPresent => simp [GeneralBorrowExposureAncestorFold.walk]
      | step earlier childNode childPresent edge =>
        have same : node = childNode := Option.some.inj (present.symm.trans childPresent)
        subst node
        obtain ⟨parentNode,parentPresent,smaller⟩ := depth.parent index childNode childPresent _ edge
        simp only [GeneralBorrowExposureAncestorFold.walk,childPresent,edge,List.mem_cons]
        exact Or.inr (ih _ parentNode parentPresent (by omega) earlier)
  obtain ⟨node,present⟩ := path.present
  exact run _ witness node present (by have bound := depth.bounded witness node present;omega) path

theorem positive {tree initial root protections} (data : Data tree initial root protections)
    (witness : UniIndex) (node : TreeNode) (present : tree.nodes.get witness = some node)
    (exposed : node.isExposed = true)
    (support : GeneralBorrowExposureCardinality.supports (GeneralBorrowExposureCardinality.effective initial protections witness node) .Read = true)
    (index : UniIndex) (path : Path tree index witness) :
    0 < GeneralBorrowWildcardRelatednessBounds.count initial.exposedCache index .Read := by
  exact GeneralBorrowExposedNonleafRead.exposed_descendant tree initial protections data.coherent data.short index witness node
    present exposed support (path.walk data.depth)
end DuplicatePrefix.GeneralBorrowExposedNonleafPrimaryPath
