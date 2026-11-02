import duplicate_prefix.GeneralBorrowRootLocalCounterFrame
namespace DuplicatePrefix.GeneralBorrowRootLocalAuthorization
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality GeneralBorrowExposureAncestorFold
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- Only removals in this actual ancestor-walk component can affect its
residual root/query counts. This is a finite data filter, not an operation. -/
def componentMask (tree : BorrowTree) (root : UniIndex) (removed : List UniIndex) : List UniIndex :=
  removed.filter (fun index => (walk tree.nodes (tree.nodes.size+1) index).contains root)

theorem componentMask_member (tree : BorrowTree) (root : UniIndex) (removed : List UniIndex) (index : UniIndex) :
    index ∈ componentMask tree root removed ↔ index ∈ removed ∧ root ∈ walk tree.nodes (tree.nodes.size+1) index := by
  simp [componentMask,List.contains_iff_mem]

theorem mask_legal (tree : BorrowTree) (before after : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (maximum : Option BorTag) (kind : AccessKind) (removed : List UniIndex)
    (legal : Removal tree after protections maximum kind removed)
    (slots : ∀ index node, tree.nodes.get index = some node →
      root ∈ walk tree.nodes (tree.nodes.size+1) index → after.perms.get index = before.perms.get index) :
    Removal tree before protections maximum kind (componentMask tree root removed) := by
  refine ⟨legal.distinct.filter _,?_⟩
  intro index member
  obtain ⟨inside,component⟩ := (componentMask_member tree root removed index).mp member
  obtain ⟨node,present,allowed⟩ := legal.allowed index inside
  refine ⟨node,present,?_⟩
  simpa only [removable,GeneralBorrowExposureCardinality.effective,slots index node present component] using allowed

theorem mask_subset (tree : BorrowTree) (root : UniIndex) (before after : List UniIndex)
    (subset : ∀ index ∈ before, index ∈ after) :
    ∀ index ∈ componentMask tree root before, index ∈ componentMask tree root after := by
  intro index member
  obtain ⟨earlier,component⟩ := (componentMask_member tree root before index).mp member
  exact (componentMask_member tree root after index).mpr ⟨subset index earlier,component⟩

/-- Exact residual Nat counts below a root depend only on that component's
slots and the component-filtered removal mask. No cache equality is assumed. -/
theorem count_frame (tree : BorrowTree) (before after : LocationTree) (protections : ProtectedTags)
    (root query : UniIndex) (kind : AccessKind) (removed : List UniIndex)
    (covers : Covers tree.nodes root query)
    (slots : ∀ index node, tree.nodes.get index = some node →
      root ∈ walk tree.nodes (tree.nodes.size+1) index → after.perms.get index = before.perms.get index) :
    residualCount tree after protections kind removed query =
      residualCount tree before protections kind (componentMask tree root removed) query := by
  unfold residualCount
  simp only [List.filter_filter]
  apply congrArg List.length
  apply List.filter_congr
  intro row member
  by_cases path : query ∈ walk tree.nodes (tree.nodes.size+1) row.1
  · have present := (GeneralBorrowFreshReuseProtection.entries_get tree.nodes row.1 row.2).mp member
    have component := covers row member path
    have same := slots row.1 row.2 present component
    have maskEq : (componentMask tree root removed).contains row.1 = removed.contains row.1 := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.contains_iff_mem,componentMask_member,component,and_true]
    simp only [contributes,GeneralBorrowExposureCardinality.effective,same,maskEq]
  · have absent : (walk tree.nodes (tree.nodes.size+1) row.1).contains query = false := by
      apply Bool.eq_false_iff.mpr
      intro positive
      exact path (List.contains_iff_mem.mp positive)
    simp only [contributes,absent,Bool.and_false]

theorem relation_frame (tree : BorrowTree) (before after : LocationTree) (protections : ProtectedTags)
    (root index : UniIndex) (node : TreeNode) (position : Nat) (maximum : Option BorTag)
    (kind : AccessKind) (removed : List UniIndex) (covers : Covers tree.nodes root index)
    (slots : ∀ query queryNode, tree.nodes.get query = some queryNode →
      root ∈ walk tree.nodes (tree.nodes.size+1) query → after.perms.get query = before.perms.get query) :
    residualRelation tree after protections root index node maximum kind position removed =
      residualRelation tree before protections root index node maximum kind position (componentMask tree root removed) := by
  unfold residualRelation
  rw [count_frame tree before after protections root root kind removed (fun _ _ h => h) slots,
    count_frame tree before after protections root index kind removed covers slots]

/-- Full any-kind/any-cutoff residual authorization transports across an
unchanged root component. Current legal masks are filtered internally; they
need not be empty, and permissions outside the component may change freely.
This data theorem needs no coherent-cache or finite-width assumption. -/
theorem authorization (tree : BorrowTree) (before after : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (kind : AccessKind) (support : UniIndex → Prop)
    (old : Authorization tree before protections root position maximum kind support)
    (slots : ∀ index node, tree.nodes.get index = some node →
      root ∈ walk tree.nodes (tree.nodes.size+1) index → after.perms.get index = before.perms.get index) :
    Authorization tree after protections root position maximum kind support := by
  have supportSlots : ∀ index, support index → after.perms.get index = before.perms.get index := by
    intro index inside
    obtain ⟨node,present⟩ := old.present index inside
    apply slots index node present
    apply old.covers index inside (index,node) ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes index node).mpr present)
    simp [walk]
  refine ⟨old.rooted,old.present,old.children,old.covers,?_,?_,?_⟩
  · intro index node inside present
    simpa only [supportSlots index inside] using old.possible index node inside present
  · intro entry exit legalEntry legalExit subset index node inside present retained
    have oldEntry := mask_legal tree before after protections root maximum kind entry legalEntry slots
    have oldExit := mask_legal tree before after protections root maximum kind exit legalExit slots
    have nested := mask_subset tree root entry exit subset
    have notRemoved : index ∉ componentMask tree root exit := by
      intro member
      exact retained ((componentMask_member tree root exit index).mp member).1
    rw [relation_frame tree before after protections root index node position maximum kind entry (old.covers index inside) slots,
      relation_frame tree before after protections root index node position maximum kind exit (old.covers index inside) slots]
    simpa only [supportSlots index inside] using old.queries _ _ oldEntry oldExit nested index node inside present notRemoved
  · intro physical
    obtain ⟨index,node,inside,present,witness⟩ := old.witness physical
    exact ⟨index,node,inside,present,by simpa only [Supports,supportSlots index inside] using witness⟩

/-- Distinct physical-root components obtain the required frame from the real
operation's outside-support storage result. No separation, operation-success,
permission profile, tag-order, cutoff exclusion or empty-mask premise is used. -/
theorem authorization_other (tree : BorrowTree) (before after : LocationTree)
    (protections : ProtectedTags) (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (root other : UniIndex) (rootMember : root ∈ tree.roots.toList)
    (otherMember : other ∈ tree.roots.toList) (different : root ≠ other)
    (support otherSupport : UniIndex → Prop)
    (covers : ∀ index, support index → Covers tree.nodes root index)
    (position : Nat) (maximum : Option BorTag) (kind : AccessKind)
    (old : Authorization tree before protections other position maximum kind otherSupport)
    (outside : ∀ index, ¬support index → after.perms.get index = before.perms.get index) :
    Authorization tree after protections other position maximum kind otherSupport := by
  apply authorization tree before after protections other position maximum kind otherSupport old
  intro index node present inOther
  apply outside index
  intro inside
  have own : index ∈ walk tree.nodes (tree.nodes.size+1) index := by simp [walk]
  have inRoot := covers index inside (index,node) ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes index node).mpr present) own
  exact GeneralBorrowRootLocalCounterFrame.components_disjoint tree before protections formed root other index node present rootMember otherMember different inRoot inOther
end DuplicatePrefix.GeneralBorrowRootLocalAuthorization
