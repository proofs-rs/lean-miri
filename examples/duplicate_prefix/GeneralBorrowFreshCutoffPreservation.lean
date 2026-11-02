import duplicate_prefix.GeneralBorrowPrimaryWitnessVisibility
import duplicate_prefix.GeneralBorrowFreshParentTagOrder
namespace DuplicatePrefix.GeneralBorrowFreshCutoffPreservation
open Miri Miri.Memory Miri.ABI Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization
open GeneralBorrowPrimaryWitnessVisibility GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowFreshGraph GeneralBorrowExposure
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
private def Edges (tree : BorrowTree) (maximum : Option BorTag) : Prop :=
  ∀ child node, tree.nodes.get child=some node → aboveMaximum node maximum=false →
    ∀ parent parentNode, node.parent=some parent → tree.nodes.get parent=some parentNode →
      aboveMaximum parentNode maximum=false
private theorem edges_of_closed (tree : BorrowTree) (maximum : Option BorTag)
    (closed : CutoffClosed tree maximum) : Edges tree maximum := by
  intro child node present below parent parentNode edge parentPresent
  exact closed child node present below parent parentNode parentPresent (.step (.refl parent parentNode parentPresent) node present edge)
private theorem closed_of_edges (tree : BorrowTree) (maximum : Option BorTag)
    (edges : Edges tree maximum) : CutoffClosed tree maximum := by
  have bound : ∀ {a b}, Path tree a b → ∀ node, tree.nodes.get b=some node → aboveMaximum node maximum=false →
      ∀ ancestor, tree.nodes.get a=some ancestor → aboveMaximum ancestor maximum=false := by
    intro a b path
    induction path with
    | refl original present =>
      intro node found below ancestor ancestorFound
      have same := Option.some.inj (found.symm.trans ancestorFound)
      simpa only [same] using below
    | @step parent child earlier node present edge ih =>
      intro last found below ancestor ancestorFound
      have same : node=last := Option.some.inj (present.symm.trans found)
      obtain ⟨parentNode,parentPresent⟩ := earlier.present
      exact ih parentNode parentPresent (edges child node present (by simpa only [same] using below) parent parentNode edge parentPresent) ancestor ancestorFound
  intro witness node present below index ancestor ancestorPresent path
  exact bound path node present below ancestor ancestorPresent

private theorem old_fields (tree : BorrowTree) (index parent query : UniIndex) (parentNode newNode node : TreeNode)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodeAt parent = some parentNode)
    (different : query ≠ index) (present : (attached tree index parent parentNode newNode).nodeAt query = some node) :
    ∃ old, tree.nodeAt query = some old ∧ old.tag = node.tag ∧ old.parent = node.parent := by
  by_cases isParent : query = parent
  · subst query
    rw [GeneralBorrowFreshMetadataChildReuseGraph.parent_lookup tree index parent parentNode newNode vacant parentPresent] at present
    cases present
    exact ⟨parentNode,parentPresent,rfl,rfl⟩
  · rw [GeneralBorrowFreshMetadataChildReuseGraph.other_lookup tree index parent query parentNode newNode vacant parentPresent isParent different] at present
    exact ⟨node,present,rfl,rfl⟩

private theorem retained_fields (tree : BorrowTree) (index parent query : UniIndex) (parentNode newNode old : TreeNode)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodeAt parent = some parentNode)
    (present : tree.nodeAt query = some old) :
    ∃ node, (attached tree index parent parentNode newNode).nodeAt query = some node ∧ node.tag = old.tag ∧ node.parent = old.parent := by
  by_cases isParent : query = parent
  · subst query
    cases Option.some.inj (present.symm.trans parentPresent)
    exact ⟨_,GeneralBorrowFreshMetadataChildReuseGraph.parent_lookup tree index parent parentNode newNode vacant parentPresent,rfl,rfl⟩
  · have different : query ≠ index := by intro equal;subst query;change tree.nodes.get index = some old at present;rw [vacant] at present;cases present
    exact ⟨old,(GeneralBorrowFreshMetadataChildReuseGraph.other_lookup tree index parent query parentNode newNode vacant parentPresent isParent different).trans present,rfl,rfl⟩

/-- During the function, adding a fresh ABOVE-cutoff child preserves the
old cutoff invariant. No chronological history or global parent order is used. -/
theorem attached (tree : BorrowTree) (maximum : Option BorTag)
    (closed : CutoffClosed tree maximum) (depth : ParentDepth tree.nodes)
    (index parent : UniIndex) (parentNode newNode : TreeNode)
    (vacant : tree.nodes.get index=none) (parentPresent : tree.nodeAt parent=some parentNode)
    (above : aboveMaximum newNode maximum=true) :
    CutoffClosed (GeneralBorrowFreshGraph.attached tree index parent parentNode newNode) maximum := by
  apply closed_of_edges
  intro child node present below ancestor ancestorNode edge ancestorPresent
  change (GeneralBorrowFreshGraph.attached tree index parent parentNode newNode).nodeAt child=some node at present
  change (GeneralBorrowFreshGraph.attached tree index parent parentNode newNode).nodeAt ancestor=some ancestorNode at ancestorPresent
  by_cases isNew : child=index
  · subst child
    rw [GeneralBorrowFreshMetadataChildReuseGraph.new_lookup tree index parent parentNode newNode vacant parentPresent] at present
    cases present
    rw [above] at below
    contradiction
  · obtain ⟨old,oldPresent,tag,parents⟩ := old_fields tree index parent child parentNode newNode node vacant parentPresent isNew present
    obtain ⟨oldParent,oldParentPresent,_⟩ := depth.parent child old oldPresent ancestor (parents.trans edge)
    obtain ⟨next,nextPresent,nextTag,_⟩ := retained_fields tree index parent ancestor parentNode newNode oldParent vacant parentPresent oldParentPresent
    have equal : next=ancestorNode := Option.some.inj (nextPresent.symm.trans ancestorPresent)
    subst next
    have oldBelow : aboveMaximum old maximum=false := by cases maximum <;> simpa only [aboveMaximum,tag] using below
    have result := edges_of_closed tree maximum closed child old oldPresent oldBelow ancestor oldParent (parents.trans edge) oldParentPresent
    cases maximum <;> simpa only [aboveMaximum,←nextTag] using result
theorem transfer (before after : BorrowTree) (maximum : Option BorTag)
    (same : GeneralBorrowView.treeShape after=GeneralBorrowView.treeShape before)
    (closed : CutoffClosed before maximum) : CutoffClosed after maximum := by
  apply closed_of_edges
  intro child node present below parent parentNode edge parentPresent
  obtain ⟨old,oldPresent,tag,parents,_,_⟩ := GeneralBorrowFreshMetadata.node_fields after before same.symm child node present
  obtain ⟨oldParent,oldParentPresent,parentTag,_,_,_⟩ := GeneralBorrowFreshMetadata.node_fields after before same.symm parent parentNode parentPresent
  have oldBelow : aboveMaximum old maximum=false := by cases maximum <;> simpa only [aboveMaximum,tag] using below
  have result := edges_of_closed before maximum closed child old oldPresent oldBelow parent oldParent (parents.trans edge) oldParentPresent
  cases maximum <;> simpa only [aboveMaximum,parentTag] using result

theorem staged (tree : BorrowTree) (depth : ParentDepth tree.nodes) (maximum : Option BorTag)
    (closed : CutoffClosed tree maximum) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (vacant : tree.nodes.get index=none) (parentPresent : tree.nodeAt parent=some parentNode)
    (above : aboveMaximum newNode maximum=true) (mapping : UniKeyMap BorTag)
    (locations : Miri.DataStructures.DedupRangeMap LocationTree) (after : BorrowTree)
    (same : GeneralBorrowView.treeShape after=GeneralBorrowView.treeShape
      (GeneralBorrowFreshMetadataChildAttach.staged tree index parent parentNode newNode mapping locations)) :
    CutoffClosed after maximum := by
  let stage := GeneralBorrowFreshMetadataChildAttach.staged tree index parent parentNode newNode mapping locations
  have stageClosed : CutoffClosed stage maximum :=
    closed_nodes (before := GeneralBorrowFreshGraph.attached tree index parent parentNode newNode)
      (after := stage) rfl maximum
      (attached tree maximum closed depth index parent parentNode newNode vacant parentPresent above)
  exact transfer stage after maximum same stageClosed

end DuplicatePrefix.GeneralBorrowFreshCutoffPreservation
