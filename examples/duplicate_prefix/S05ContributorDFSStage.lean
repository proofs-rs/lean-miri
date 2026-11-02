import duplicate_prefix.S05ContributorForeignCone
import duplicate_prefix.GeneralBorrowExposedNonleafState

namespace DuplicatePrefix.S05ContributorDFSStage
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality GeneralBorrowExposureAncestorFold GeneralBorrowExposedNonleafPrimaryPath
open GeneralBorrowWildcardControlWitness GeneralBorrowWildcardSubtreeStack
open S05ContributorCacheOrder S05ContributorVisitorStep
open DuplicatePrefixCallbackAuthorization
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- A retained contributor has either acquired Write cache strength or remains
reachable from the actual DFS task stack. This tracks state, not safety. -/
def Certified (tree : BorrowTree) (location : LocationTree)
    (witness : UniIndex) (node : TreeNode) (stack : Array Task) : Prop :=
  Pending tree witness
    (decide (((location.perms.get witness).getD node.defaultLocationState).idempotentForeignAccess = .Write)) stack

theorem initial (tree : BorrowTree) (location : LocationTree) (root witness : UniIndex)
    (node : TreeNode) (path : Path tree root witness) : Certified tree location witness node #[(root,false)] := by
  exact .inr ⟨(root,false),by simp,path,by simp⟩

theorem empty (tree : BorrowTree) (location : LocationTree) (witness : UniIndex) (node : TreeNode)
    (certified : Certified tree location witness node #[]) :
    ((location.perms.get witness).getD node.defaultLocationState).idempotentForeignAccess = .Write := by
  exact of_decide_eq_true (GeneralBorrowWildcardControlWitness.empty certified)

theorem expand (tree : BorrowTree) (location : LocationTree) (witness : UniIndex) (witnessNode : TreeNode)
    (graph : Reciprocal tree) (stack : Array Task) (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node)
    (certified : Certified tree location witness witnessNode (stack.push (index,false))) :
    Certified tree location witness witnessNode (expanded stack index node.children) :=
  GeneralBorrowWildcardControlWitness.expand graph _ _ _ _ present certified

/-- Popping a task whose subtree excludes the retained contributor preserves
its processed-or-pending certificate, including Either/unrelated regions. -/
theorem pop_outside (tree : BorrowTree) (location : LocationTree) (witness : UniIndex)
    (witnessNode : TreeNode) (stack : Array Task) (index : UniIndex) (post : Bool)
    (certified : Certified tree location witness witnessNode (stack.push (index,post)))
    (outside : ¬ Path tree index witness) : Certified tree location witness witnessNode stack :=
  GeneralBorrowWildcardControlWitness.pop stack index post certified outside

/-- The actual foreign callback's map write discharges a retained contributor
when that contributor is the postvisited node; writes elsewhere frame it.
The historical classifier certificate supplies the Foreign branch separately. -/
theorem post_foreign (tree : BorrowTree) (location : LocationTree)
    (witness : UniIndex) (witnessNode : TreeNode) (stack : Array Task)
    (index : UniIndex) (old : LocationState) (held : Bool)
    (stored : location.perms.get index = some old)
    (notDisabled : old.permission ≠ .Disabled)
    (certified : Certified tree location witness witnessNode (stack.push (index,true))) :
    Certified tree {location with perms := location.perms.insert index (foreignWriteStep old held)} witness witnessNode stack := by
  have same := GeneralBorrowNodeUpdate.insert_existing_get_same location.perms index old (foreignWriteStep old held) stored
  have other := GeneralBorrowNodeUpdate.insert_existing_get_other location.perms index
  apply GeneralBorrowWildcardControlWitness.post _ _ stack index certified
  · intro cached
    by_cases equal : witness = index
    · subst witness
      simp only [same,Option.getD_some,decide_eq_true_eq]
      rcases old with ⟨permission,accessed,cache⟩
      cases permission with
      | ReservedFrz conflicted =>
        cases conflicted <;> cases accessed <;> cases cache <;> cases held <;> decide +kernel
      | Cell | ReservedIM | Unique | Frozen | Disabled =>
        cases accessed <;> cases cache <;> cases held <;> first | contradiction | decide +kernel
    · simpa only [other witness old (foreignWriteStep old held) stored equal] using cached
  · intro equal
    subst witness
    simp only [same,Option.getD_some,decide_eq_true_eq]
    rcases old with ⟨permission,accessed,cache⟩
    cases permission with
    | ReservedFrz conflicted =>
      cases conflicted <;> cases accessed <;> cases cache <;> cases held <;> decide +kernel
    | Cell | ReservedIM | Unique | Frozen | Disabled =>
      cases accessed <;> cases cache <;> cases held <;> first | contradiction | decide +kernel

/-- Local/Either callbacks outside the retained contributor only frame its
cache. This postvisit rule uses the actual effective-state equality, including
lazy default materialization, rather than demanding identical physical maps. -/
theorem post_unrelated (tree : BorrowTree) (before after : LocationTree)
    (witness : UniIndex) (node : TreeNode) (stack : Array Task) (index : UniIndex)
    (different : index ≠ witness)
    (frame : ((after.perms.get witness).getD node.defaultLocationState).idempotentForeignAccess =
      ((before.perms.get witness).getD node.defaultLocationState).idempotentForeignAccess)
    (certified : Certified tree before witness node (stack.push (index,true))) :
    Certified tree after witness node stack := by
  unfold Certified
  rw [frame]
  apply GeneralBorrowWildcardControlWitness.post _ _ stack index certified
  · exact fun cached => cached
  · intro same
    exact False.elim (different same)

/-- Every actual foreign callback map write is cache-monotone at every
physical contributor, even when the callback has an error outcome. -/
theorem foreign_cache_monotone (location : LocationTree) (index witness : UniIndex)
    (node : TreeNode) (old : LocationState) (held : Bool)
    (stored : location.perms.get index = some old) :
    ((location.perms.get witness).getD node.defaultLocationState).idempotentForeignAccess.rank ≤
      (((location.perms.insert index (foreignWriteStep old held)).get witness).getD node.defaultLocationState).idempotentForeignAccess.rank := by
  by_cases same : witness = index
  · subst witness
    rw [GeneralBorrowNodeUpdate.insert_existing_get_same location.perms index old _ stored,stored]
    simp only [Option.getD_some]
    rcases old with ⟨permission,accessed,cache⟩
    cases permission with
    | ReservedFrz conflicted =>
      cases conflicted <;> cases accessed <;> cases cache <;> cases held <;> decide +kernel
    | Cell | ReservedIM | Unique | Frozen | Disabled =>
      cases accessed <;> cases cache <;> cases held <;> decide +kernel
  · rw [GeneralBorrowNodeUpdate.insert_existing_get_other location.perms index witness old _ stored same]
    exact Nat.le_refl _

/-- A skipped ancestor discharges its retained contributor without visiting
it. Ownership excludes Disabled skips on a supporting path; contributor order
then forces Write cache strength down that path. The monotone cache premise
is a per-stage relation, to be preserved by the historical-Foreign certificate. -/
theorem pop_skipped (tree : BorrowTree) (initial current : LocationTree)
    (protections : ProtectedTags) (root : UniIndex) (position : Nat)
    (rights : S05NoCutoffOwnershipBridge.Ownership tree initial protections root position)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (order : ContributorOrder tree initial protections rights.area.contains)
    (witness : UniIndex) (witnessNode : TreeNode) (found : tree.nodes.get witness = some witnessNode)
    (exposed : witnessNode.isExposed = true)
    (supported : supports (effective initial protections witness witnessNode) .Write = true)
    (stack : Array Task) (index : UniIndex) (node : TreeNode)
    (inside : rights.area.contains index) (present : tree.nodes.get index = some node)
    (path : Path tree index witness)
    (untouched : current.perms.get index = initial.perms.get index)
    (skipped : skip ((current.perms.get index).getD node.defaultLocationState) .Write .ForeignAccess = true)
    (monotone : ((initial.perms.get witness).getD witnessNode.defaultLocationState).idempotentForeignAccess.rank ≤
      ((current.perms.get witness).getD witnessNode.defaultLocationState).idempotentForeignAccess.rank) :
    Certified tree current witness witnessNode stack := by
  have walked := path.walk depth
  have writable := rights.localRights index node inside present witness witnessNode found exposed walked .Write supported
  have notDisabled := writable.2.1
  rw [untouched] at skipped
  have queryCached : ((initial.perms.get index).getD node.defaultLocationState).idempotentForeignAccess = .Write := by
    generalize stateEq : (initial.perms.get index).getD node.defaultLocationState = state at notDisabled skipped ⊢
    rcases state with ⟨permission,accessed,cache⟩
    cases permission with
    | ReservedFrz conflicted =>
      cases conflicted <;> cases cache <;>
        simp_all [skip,AccessRelatedness.isForeign,IdempotentForeignAccess.canSkipForeignAccess,
          IdempotentForeignAccess.fromForeign,IdempotentForeignAccess.isLocal,IdempotentForeignAccess.le,
          IdempotentForeignAccess.rank,Permission.isDisabled,Permission.isFrozen]
    | Cell | ReservedIM | Unique | Frozen | Disabled =>
      cases cache <;>
        simp_all [skip,AccessRelatedness.isForeign,IdempotentForeignAccess.canSkipForeignAccess,
          IdempotentForeignAccess.fromForeign,IdempotentForeignAccess.isLocal,IdempotentForeignAccess.le,
          IdempotentForeignAccess.rank,Permission.isDisabled,Permission.isFrozen]
  have bound := Nat.le_trans (order index node inside present witness witnessNode found exposed walked supported) monotone
  rw [queryCached] at bound
  apply Or.inl
  simp only [decide_eq_true_eq]
  cases value : ((current.perms.get witness).getD witnessNode.defaultLocationState).idempotentForeignAccess <;>
    simp_all [IdempotentForeignAccess.rank]

end DuplicatePrefix.S05ContributorDFSStage
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S05ContributorDFSStage.initial,
      ``DuplicatePrefix.S05ContributorDFSStage.empty,
      ``DuplicatePrefix.S05ContributorDFSStage.expand,
      ``DuplicatePrefix.S05ContributorDFSStage.pop_outside,
      ``DuplicatePrefix.S05ContributorDFSStage.post_foreign,
      ``DuplicatePrefix.S05ContributorDFSStage.pop_skipped,
      ``DuplicatePrefix.S05ContributorDFSStage.post_unrelated,
      ``DuplicatePrefix.S05ContributorDFSStage.foreign_cache_monotone] do
    for ax in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "unapproved axiom {ax}"
