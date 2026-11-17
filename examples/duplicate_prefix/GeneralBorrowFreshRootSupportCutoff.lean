import duplicate_prefix.GeneralBorrowFreshRootCutoff
namespace DuplicatePrefix.GeneralBorrowFreshRootSupportCutoff
open Miri Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- Hidden later descendants are permitted above the original fresh cutoff. -/
def ExposedBound (tree : BorrowTree) (maximum : BorTag) : Prop :=
  ∀ index node,tree.nodeAt index = some node → node.isExposed = true → node.tag.value ≤ maximum.value

/-- The old other-root support contains only nodes below the fresh cutoff. -/
def SupportBound (tree : BorrowTree) (maximum : BorTag) (support : UniIndex → Prop) : Prop :=
  ∀ index node,support index → tree.nodeAt index = some node → node.tag.value ≤ maximum.value

theorem exposed_of_bound (tree : BorrowTree) (maximum : BorTag) (bound : GeneralBorrowFreshRootCutoff.Bound tree maximum) :
    ExposedBound tree maximum := by intro index node present exposed;exact bound index node present

/-- A later hidden node cannot invalidate the exposed contributor bound even
if its fresh tag is larger than the original selected-root cutoff. -/
theorem exposed_insert_hidden (tree : BorrowTree) (maximum : BorTag) (bound : ExposedBound tree maximum)
    (index : UniIndex) (node : TreeNode) (hidden : node.isExposed = false) :
    ExposedBound {tree with nodes := tree.nodes.insert index node} maximum := by
  intro query value found exposed
  change (tree.nodes.insert index node).get query = some value at found
  by_cases same : query = index
  · subst query
    rw [GeneralBorrowFreshLocation.get_same] at found
    cases found
    rw [hidden] at exposed
    contradiction
  · rw [GeneralBorrowFreshLocation.get_other _ index query _ same] at found
    exact bound query value found exposed

/-- Removable contributors are identical at maxnone and a fresh cutoff when
all exposed contributors remain below it. Hidden newer nodes are arbitrary. -/
theorem removable_eq (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (maximum : BorTag) (bound : ExposedBound tree maximum) (index : UniIndex) (node : TreeNode)
    (present : tree.nodeAt index = some node) (kind : AccessKind) :
    removable location protections (some maximum) kind index node = removable location protections none kind index node := by
  cases exposed : node.isExposed with
  | false => cases kind <;> simp only [removable,exposed,Bool.false_and]
  | true => cases kind <;> simp only [removable,GeneralBorrowFreshRootCutoff.above node maximum (bound index node present exposed)]

private theorem removal (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (maximum : BorTag) (bound : ExposedBound tree maximum) (kind : AccessKind) (removed : List UniIndex) :
    Removal tree location protections (some maximum) kind removed ↔ Removal tree location protections none kind removed := by
  constructor
  all_goals
    intro legal
    refine ⟨legal.distinct,?_⟩
    intro index member
    obtain ⟨node,present,allowed⟩ := legal.allowed index member
    refine ⟨node,present,?_⟩
    simpa only [removable_eq tree location protections maximum bound index node present kind] using allowed

/-- Full finite query/witness authorization equivalence using distinct exposed
and visited-support bounds. No bound is imposed on newer hidden nodes outside
the actual old-root support, and no ParentTagOrder is assumed. -/
theorem authorization_iff (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (maximum : BorTag) (exposed : ExposedBound tree maximum) (root : UniIndex) (position : Nat) (kind : AccessKind)
    (support : UniIndex → Prop) (bounded : SupportBound tree maximum support) :
    Authorization tree location protections root position none kind support ↔
      Authorization tree location protections root position (some maximum) kind support := by
  have relations (index : UniIndex) (node : TreeNode) (included : support index) (present : tree.nodeAt index = some node) (removed : List UniIndex) :
      residualRelation tree location protections root index node (some maximum) kind position removed =
        residualRelation tree location protections root index node none kind position removed := by
    simp only [residualRelation,GeneralBorrowFreshRootCutoff.above node maximum (bounded index node included present)]
  constructor
  · intro old
    refine ⟨old.rooted,old.present,old.children,old.covers,old.possible,?_,?_⟩
    · intro entry exit legalEntry legalExit subset index node included present retained
      rw [relations index node included present entry,relations index node included present exit]
      exact old.queries entry exit ((removal tree location protections maximum exposed kind entry).mp legalEntry)
        ((removal tree location protections maximum exposed kind exit).mp legalExit) subset index node included present retained
    · intro primary
      obtain ⟨index,node,included,present,witnessExposed,allowed,_⟩ := old.witness primary
      refine ⟨index,node,included,present,witnessExposed,allowed,?_⟩
      simpa only [Option.isNone_some,Option.any_some,Bool.false_or,decide_eq_true_eq] using bounded index node included present
  · intro old
    refine ⟨old.rooted,old.present,old.children,old.covers,old.possible,?_,?_⟩
    · intro entry exit legalEntry legalExit subset index node included present retained
      rw [←relations index node included present entry,←relations index node included present exit]
      exact old.queries entry exit ((removal tree location protections maximum exposed kind entry).mpr legalEntry)
        ((removal tree location protections maximum exposed kind exit).mpr legalExit) subset index node included present retained
    · intro primary
      obtain ⟨index,node,included,present,witnessExposed,allowed,_⟩ := old.witness primary
      exact ⟨index,node,included,present,witnessExposed,allowed,by simp⟩
end DuplicatePrefix.GeneralBorrowFreshRootSupportCutoff
