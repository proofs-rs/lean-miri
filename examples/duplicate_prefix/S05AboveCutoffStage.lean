import duplicate_prefix.S05ContributorDFSStage
import duplicate_prefix.GeneralBorrowResidualSavedWriteRuntime

namespace DuplicatePrefix.S05AboveCutoffStage
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality GeneralBorrowExposureAncestorFold GeneralBorrowExposedNonleafPrimaryPath
open GeneralBorrowWildcardSubtreeStack GeneralBorrowWildcardControlWitness
open S05ContributorCacheOrder S05ContributorDFSStage
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization
open GeneralBorrowWildcardVirtualLeaf (effective materialized)
open GeneralBorrowExposedNonleafState (updated updated_other)
set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local irreducible] UniValMap.insert

/-- Only initial above-cutoff Write supporters are tracked. Their own
callbacks cannot be Local/Either; unrelated local callbacks frame them. -/
def Stage (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (maximum : Option BorTag) (stack : Array Task) : Prop :=
  ∀ witness node, tree.nodes.get witness = some node → node.isExposed = true →
    aboveMaximum node maximum = true →
    supports (GeneralBorrowExposureCardinality.effective initial protections witness node) .Write = true →
    Path tree root witness →
    Certified tree current witness node stack ∧
      ((initial.perms.get witness).getD node.defaultLocationState).idempotentForeignAccess.rank ≤
        ((current.perms.get witness).getD node.defaultLocationState).idempotentForeignAccess.rank

theorem initial (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (maximum : Option BorTag) : Stage tree location location protections root maximum #[(root,false)] := by
  intro witness node _ _ _ _ path
  exact ⟨S05ContributorDFSStage.initial tree location root witness node path,Nat.le_refl _⟩

theorem expand (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (maximum : Option BorTag) (graph : Reciprocal tree)
    (stack : Array Task) (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node)
    (stage : Stage tree initial current protections root maximum (stack.push (index,false))) :
    Stage tree initial current protections root maximum (expanded stack index node.children) := by
  intro witness witnessNode found exposed above supported path
  obtain ⟨certified,monotone⟩ := stage witness witnessNode found exposed above supported path
  exact ⟨S05ContributorDFSStage.expand tree current witness witnessNode graph stack index node present certified,monotone⟩

theorem pop (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag)
    (rights : S05NoCutoffOwnershipBridge.Ownership tree initial protections root position)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (order : ContributorOrder tree initial protections rights.area.contains)
    (stack : Array Task) (index : UniIndex) (node : TreeNode)
    (inside : rights.area.contains index) (present : tree.nodes.get index = some node)
    (untouched : current.perms.get index = initial.perms.get index)
    (skipped : skip (effective current index node) .Write .ForeignAccess = true)
    (stage : Stage tree initial current protections root maximum (stack.push (index,false))) :
    Stage tree initial current protections root maximum stack := by
  intro witness witnessNode found exposed above supported rootPath
  obtain ⟨certified,monotone⟩ := stage witness witnessNode found exposed above supported rootPath
  refine ⟨?_,monotone⟩
  by_cases path : Path tree index witness
  · exact pop_skipped tree initial current protections root position rights depth order witness witnessNode found exposed supported
      stack index node inside present path untouched skipped monotone
  · exact pop_outside tree current witness witnessNode stack index false certified path

private theorem clamp_ne_exact (total localCount : Nat) (virtual : Bool) :
    classify total localCount virtual true ≠ some .EitherAccess ∧
    classify total localCount virtual true ≠ some .LocalAccess := by
  cases virtual <;> by_cases zero : total = 0 <;> by_cases same : total = localCount <;>
    by_cases next : total+1 = localCount <;> by_cases localZero : localCount = 0 <;> simp_all [classify]

private theorem foreign_record_cache (state recorded : LocationState)
    (record : state.recordNewAccess .Write .ForeignAccess = .Recorded recorded) :
    recorded.idempotentForeignAccess = .Write := by
  unfold LocationState.recordNewAccess at record
  split at record
  · cases record
    cases value : state.idempotentForeignAccess <;>
      simp [IdempotentForeignAccess.recordNew,IdempotentForeignAccess.fromAccessAndRelatedness,
        AccessRelatedness.isForeign,IdempotentForeignAccess.fromForeign,IdempotentForeignAccess.isLocal,
        IdempotentForeignAccess.max,IdempotentForeignAccess.rank,value]
  · cases record

/-- The real post action, including Either materialization and precise local
or foreign callbacks, preserves the restricted retained-supporter stage. The
Action is internal DFS evidence; the public loop derives it from raw inputs. -/
theorem post (tree : BorrowTree) (initial current after : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (stack : Array Task)
    (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node)
    (removed afterRemoved : List UniIndex)
    (action : DuplicatePrefixResidualWritePost.Action tree current protections root index node maximum position removed after afterRemoved)
    (other : ∀ query, query ≠ index → after.perms.get query = current.perms.get query)
    (stage : Stage tree initial current protections root maximum (stack.push (index,true))) :
    Stage tree initial after protections root maximum stack := by
  intro witness witnessNode found exposed above supported rootPath
  obtain ⟨certified,monotone⟩ := stage witness witnessNode found exposed above supported rootPath
  by_cases same : witness = index
  · subst witness
    have nodeEq := Option.some.inj (present.symm.trans found)
    subst witnessNode
    rcases action with ⟨classified,afterEq,_⟩ | ⟨exact,recorded,next,delta,classified,record,access,afterEq,_⟩
    · change classify _ _ _ (aboveMaximum node maximum) = some .EitherAccess at classified
      rw [above] at classified
      exact False.elim ((clamp_ne_exact _ _ _).1 classified)
    · cases exact with
      | LocalAccess =>
        change classify _ _ _ (aboveMaximum node maximum) = some .LocalAccess at classified
        rw [above] at classified
        exact False.elim ((clamp_ne_exact _ _ _).2 classified)
      | ForeignAccess =>
        have recordedCache := foreign_record_cache (effective current index node) recorded record
        have cache := S05ContributorCacheOrder.perform_access_cache recorded .Write .ForeignAccess (protections.contains node.tag)
        rw [access] at cache
        simp only [LocationState.AccessResult.resultingState,recordedCache] at cache
        subst after
        have atIndex : (updated tree current index node protections recorded next delta).perms.get index = some next := by
          change (GeneralBorrowWildcardSubtreeState.write current index node recorded next).perms.get index = some next
          exact GeneralBorrowWildcardSubtreeState.write_same current index node recorded next
        refine ⟨Or.inl ?_,?_⟩
        · simp only [atIndex,Option.getD_some,decide_eq_true_eq,cache]
        · simp only [atIndex,Option.getD_some,cache]
          cases value : ((initial.perms.get index).getD node.defaultLocationState).idempotentForeignAccess <;> decide +kernel
  · have frame := other witness same
    refine ⟨post_unrelated tree current after witness witnessNode stack index (Ne.symm same) ?_ certified,?_⟩
    · rw [frame]
    · simpa only [frame] using monotone

end DuplicatePrefix.S05AboveCutoffStage
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S05AboveCutoffStage.initial,
      ``DuplicatePrefix.S05AboveCutoffStage.expand,
      ``DuplicatePrefix.S05AboveCutoffStage.pop,
      ``DuplicatePrefix.S05AboveCutoffStage.post] do
    for ax in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "unapproved axiom {ax}"
