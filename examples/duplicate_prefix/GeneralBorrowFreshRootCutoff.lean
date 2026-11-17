import duplicate_prefix.DuplicatePrefixResidualSupportAuthorization
import duplicate_prefix.DuplicatePrefixBorrowContract
import duplicate_prefix.GeneralBorrowPositiveWildcardConstructor
namespace DuplicatePrefix.GeneralBorrowFreshRootCutoff
open Miri Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- A fresh root's cutoff dominates every old present tag. This says nothing
about unrelated physical parent ordering or Rust caller histories. -/
def Bound (tree : BorrowTree) (maximum : BorTag) : Prop :=
  ∀ index node,tree.nodeAt index = some node → node.tag.value ≤ maximum.value

theorem runtime (tree : BorrowTree) (global : GlobalState)
    (facts : DuplicatePrefixBorrowContract.RuntimeFacts tree global) : Bound tree global.nextPointerTag := by
  intro index node present
  have mapped := facts.formed.allocator.nodeTags index node present
  have below := GeneralBorrowForestTagHighWater.mapped tree global.protectedTags global.nextPointerTag node.tag facts.below index mapped
  exact UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt below)

theorem insert (tree : BorrowTree) (maximum : BorTag) (bound : Bound tree maximum)
    (index : UniIndex) (node : TreeNode) (newBound : node.tag.value ≤ maximum.value) :
    Bound {tree with nodes := tree.nodes.insert index node} maximum := by
  intro query value found
  change (tree.nodes.insert index node).get query = some value at found
  by_cases same : query = index
  · subst query
    rw [GeneralBorrowFreshLocation.get_same] at found
    cases found
    exact newBound
  · rw [GeneralBorrowFreshLocation.get_other _ index query _ same] at found
    exact bound query value found

/-- Root installation/materialization changes no tag except the actual fresh
root's known tag. Thus the fresh cutoff still dominates the complete new tree. -/
theorem constructor (tree : BorrowTree) (mapping : UniKeyMap BorTag) (index : UniIndex) (tag : BorTag)
    (bound : Bound tree tag) (outside : Permission) (sifa : IdempotentForeignAccess) (inside : LocationState) (offset len : UInt64) :
    Bound (GeneralBorrowPositiveWildcardConstructor.result tree mapping index tag outside sifa inside offset len) tag := by
  exact insert tree tag bound index (WildcardHitZeroConstructor.rootNode tag outside sifa) (UInt64.le_refl _)

theorem above (node : TreeNode) (maximum : BorTag) (bound : node.tag.value ≤ maximum.value) :
    aboveMaximum node (some maximum) = aboveMaximum node none := by
  simp only [aboveMaximum]
  apply decide_eq_false
  intro strict
  have first := UInt64.le_iff_toNat_le.mp bound
  have second := UInt64.lt_iff_toNat_lt.mp strict
  omega

/-- No removability or residual query changes when a real cutoff lies above
every present node. This keeps root position and access kind explicit. -/
theorem removable_eq (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (maximum : BorTag) (bound : Bound tree maximum) (index : UniIndex) (node : TreeNode)
    (present : tree.nodeAt index = some node) (kind : AccessKind) :
    removable location protections (some maximum) kind index node = removable location protections none kind index node := by
  cases kind <;> simp only [removable,above node maximum (bound index node present)]

theorem removal (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (maximum : BorTag) (bound : Bound tree maximum) (kind : AccessKind) (removed : List UniIndex)
    (legal : Removal tree location protections (some maximum) kind removed) : Removal tree location protections none kind removed := by
  refine ⟨legal.distinct,?_⟩
  intro index member
  obtain ⟨node,present,allowed⟩ := legal.allowed index member
  exact ⟨node,present,by rw [←removable_eq tree location protections maximum bound index node present kind];exact allowed⟩

theorem relation (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (maximum : BorTag) (bound : Bound tree maximum) (root index : UniIndex) (node : TreeNode)
    (present : tree.nodeAt index = some node) (kind : AccessKind) (position : Nat) (removed : List UniIndex) :
    residualRelation tree location protections root index node (some maximum) kind position removed =
      residualRelation tree location protections root index node none kind position removed := by
  simp only [residualRelation,above node maximum (bound index node present)]

/-- Every full finite callback authorization at maxnone transports to a fresh
cutoff above all nodes, with its original support and root-position bit. This
is data transport, not an assumed successful traversal or parent-tag order. -/
theorem authorization (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (maximum : BorTag) (bound : Bound tree maximum) (root : UniIndex) (position : Nat) (kind : AccessKind) (support : UniIndex → Prop)
    (old : Authorization tree location protections root position none kind support) :
    Authorization tree location protections root position (some maximum) kind support := by
  refine ⟨old.rooted,old.present,old.children,old.covers,old.possible,?_,?_⟩
  · intro entry exit legalEntry legalExit subset index node included present retained
    rw [relation tree location protections maximum bound root index node present kind position entry,
      relation tree location protections maximum bound root index node present kind position exit]
    exact old.queries entry exit (removal tree location protections maximum bound kind entry legalEntry)
      (removal tree location protections maximum bound kind exit legalExit) subset index node included present retained
  · intro physical
    obtain ⟨index,node,included,present,exposed,allowed,_⟩ := old.witness physical
    refine ⟨index,node,included,present,exposed,allowed,?_⟩
    simpa only [Option.isNone_some,Option.any_some,Bool.false_or,decide_eq_true_eq] using bound index node present
end DuplicatePrefix.GeneralBorrowFreshRootCutoff
