import duplicate_prefix.GeneralBorrowResidualPrimaryWitness
namespace DuplicatePrefix.GeneralBorrowPrimaryWitnessVisibility
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposedNonleafPrimaryPath DuplicatePrefixCallbackAuthorization
open DuplicatePrefixResidualSupportAuthorization GeneralBorrowWildcardParentTagOrder
set_option autoImplicit false
set_option maxHeartbeats 1000000
/-- Static cutoff visibility on one witness's actual parent path. No operation,
execution plan, future state, success or safety is part of this condition. -/
def Visible (tree : BorrowTree) (maximum : Option BorTag) (witness : UniIndex) : Prop :=
  ∀ index node, tree.nodes.get index = some node → Path tree index witness → aboveMaximum node maximum = false

theorem no_cutoff (tree : BorrowTree) (witness : UniIndex) : Visible tree Option.none witness := by
  intro index node present path
  rfl

theorem of_tag_bound (tree : BorrowTree) (maximum : BorTag) (witness : UniIndex)
    (bound : ∀ index node, tree.nodes.get index = some node → node.tag.value ≤ maximum.value) :
    Visible tree (some maximum) witness := by
  intro index node present path
  simp only [aboveMaximum,decide_eq_false_iff_not]
  exact Nat.not_lt.mpr (bound index node present)

/-- At ONE fixed cutoff, each below-cutoff node has only below-cutoff
ancestors. This is independent of permissions, cache contents and executions. -/
def CutoffClosed (tree : BorrowTree) (maximum : Option BorTag) : Prop :=
  ∀ witness node, tree.nodes.get witness = some node → aboveMaximum node maximum = false → Visible tree maximum witness

theorem closed_none (tree : BorrowTree) : CutoffClosed tree Option.none := by
  intro witness node present bound
  exact no_cutoff tree witness

theorem closed_of_order (tree : BorrowTree) (order : ParentTagOrder tree)
    (maximum : Option BorTag) : CutoffClosed tree maximum := by
  intro witness witnessNode witnessPresent below index node present path
  cases maximum with
  | none => rfl
  | some maximum =>
    have bounded := path_tag_le tree order index witness path node witnessNode present witnessPresent
    have witnessBound : ¬maximum.value < witnessNode.tag.value := by
      simpa only [aboveMaximum,decide_eq_false_iff_not] using below
    simp only [aboveMaximum,decide_eq_false_iff_not]
    exact Nat.not_lt.mpr (Nat.le_trans bounded (Nat.le_of_not_gt witnessBound))

theorem visible_of_closed (tree : BorrowTree) (maximum : Option BorTag)
    (closed : CutoffClosed tree maximum) (location : LocationTree) (protections : ProtectedTags)
    (kind : AccessKind) (witness : UniIndex) (node : TreeNode) (present : tree.nodes.get witness = some node)
    (eligible : Supports location protections witness node maximum kind) : Visible tree maximum witness := by
  apply closed witness node present
  cases maximum with
  | none => rfl
  | some maximum =>
    have bound : node.tag.value ≤ maximum.value := by
      simpa only [Option.isNone_some,Option.any_some,Bool.false_or,decide_eq_true_eq] using eligible.2.2
    simp only [aboveMaximum,decide_eq_false_iff_not]
    exact Nat.not_lt.mpr bound

theorem path_nodes {before after : BorrowTree} (nodes : after.nodes=before.nodes)
    {root witness : UniIndex} (path : Path after root witness) : Path before root witness := by
  induction path with
  | refl node present => exact .refl _ node (by simpa only [nodes] using present)
  | step earlier node present edge ih => exact .step ih node (by simpa only [nodes] using present) edge

theorem closed_nodes {before after : BorrowTree} (nodes : after.nodes=before.nodes)
    (maximum : Option BorTag) (closed : CutoffClosed before maximum) : CutoffClosed after maximum := by
  intro witness node present below index ancestor found path
  exact closed witness node (by simpa only [nodes] using present) below index ancestor
    (by simpa only [nodes] using found) (path_nodes nodes path)

theorem of_order (tree : BorrowTree) (order : ParentTagOrder tree)
    (location : LocationTree) (protections : ProtectedTags) (maximum : Option BorTag) (kind : AccessKind)
    (witness : UniIndex) (witnessNode : TreeNode) (present : tree.nodes.get witness = some witnessNode)
    (eligible : Supports location protections witness witnessNode maximum kind) : Visible tree maximum witness := by
  intro index node found path
  exact path_not_above tree order location protections maximum kind index witness node witnessNode found present path eligible

theorem entry_not_skip (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (maximum : Option BorTag) (kind : AccessKind) (removed : List UniIndex)
    (legal : Removal tree location protections maximum kind removed)
    (root index witness : UniIndex) (node witnessNode : TreeNode)
    (present : tree.nodes.get index = some node) (witnessPresent : tree.nodes.get witness = some witnessNode)
    (eligible : Supports location protections witness witnessNode maximum kind)
    (visible : Visible tree maximum witness) (rootPath : Path tree root witness) (path : Path tree index witness) (state : LocationState) :
    DuplicatePrefixCallbackVisitAuthorization.entrySkip state kind
      (residualRelation tree location protections root index node maximum kind 0 removed) = false := by
  have rootPositive := GeneralBorrowResidualPrimaryWitness.positive tree location protections depth maximum kind removed legal root witness witnessNode witnessPresent eligible rootPath
  have localPositive := GeneralBorrowResidualPrimaryWitness.positive tree location protections depth maximum kind removed legal index witness witnessNode witnessPresent eligible path
  have unclamped := visible index node present path
  simp only [residualRelation,unclamped,classify,show (0 != 0) = false from rfl,Bool.false_eq_true,ite_false,Nat.add_zero]
  have notZeroRoot : (residualCount tree location protections kind removed root == 0) = false := by simp [Nat.ne_of_gt rootPositive]
  have notZeroLocal : (residualCount tree location protections kind removed index == 0) = false := by simp [Nat.ne_of_gt localPositive]
  simp only [notZeroRoot,notZeroLocal,Bool.false_eq_true,ite_false]
  split
  · simp [DuplicatePrefixCallbackVisitAuthorization.entrySkip,skip,AccessRelatedness.isForeign]
  · rfl

end DuplicatePrefix.GeneralBorrowPrimaryWitnessVisibility
