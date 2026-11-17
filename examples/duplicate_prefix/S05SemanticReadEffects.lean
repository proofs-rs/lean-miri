import duplicate_prefix.S05LiveSubtreeCacheExposure
import duplicate_prefix.GeneralBorrowSnapshotReadDFSTransferInvariant

namespace DuplicatePrefix.S05SemanticReadEffects
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowWildcardVirtualLeaf (effective materialized)
open GeneralBorrowExposedNonleafState (updated updated_other)
open S05LiveSubtreeCacheSoundness GeneralBorrowSifaPermissionConsistency
set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local irreducible] UniValMap.insert

private def valid (permission : Permission) (held : Bool) : Bool :=
  match permission.strongestIdempotentForeignAccess held with
  | .Access _ => true | .ImpossibleProtectedReservedIM => false
private def rank (permission : Permission) (held : Bool) : Nat :=
  match permission.strongestIdempotentForeignAccess held with
  | .Access strength => strength.rank | .ImpossibleProtectedReservedIM => 0

/-- Read preserves established numeric permission idempotence and cannot
remove a physical Disabled/Frozen barrier. It may create a Frozen barrier. -/
def NumericRelated (before after : LocationState) (held : Bool) : Prop :=
  (valid before.permission held = true → valid after.permission held = true ∧
    rank before.permission held ≤ rank after.permission held) ∧
  (after.permission ≠ .Disabled ∧ after.permission ≠ .Frozen →
    before.permission ≠ .Disabled ∧ before.permission ≠ .Frozen)

/-- Disabled permissions cannot be activated by a Read. This includes skipped
and materialized states; successful recording changes neither field. -/
def Related (before after : LocationState) (held : Bool) : Prop :=
  NumericRelated before after held ∧
    (before.permission = .Disabled → after.permission = .Disabled ∧ after.accessed = before.accessed)

theorem Related.numeric {before after : LocationState} {held : Bool}
    (related : Related before after held) : NumericRelated before after held := related.1

theorem Related.barrier {before after : LocationState} {held : Bool}
    (related : Related before after held)
    (live : after.permission ≠ .Disabled ∧ after.permission ≠ .Frozen) :
    before.permission ≠ .Disabled ∧ before.permission ≠ .Frozen := related.numeric.2 live

theorem Related.disabled {before after : LocationState} {held : Bool}
    (related : Related before after held) (disabled : before.permission = .Disabled) :
    after.permission = .Disabled ∧ after.accessed = before.accessed := related.2 disabled

private theorem refl_related (state : LocationState) (held : Bool) : Related state state held := by
  exact ⟨⟨fun good => ⟨good,Nat.le_refl _⟩,fun good => good⟩,fun disabled => ⟨disabled,rfl⟩⟩
private theorem trans_related (first middle last : LocationState) (held : Bool)
    (before : Related first middle held) (after : Related middle last held) : Related first last held := by
  refine ⟨⟨?_,fun live => before.barrier (after.barrier live)⟩,?_⟩
  · intro good
    obtain ⟨midGood,leMid⟩ := before.numeric.1 good
    obtain ⟨lastGood,leLast⟩ := after.numeric.1 midGood
    exact ⟨lastGood,Nat.le_trans leMid leLast⟩
  · intro disabled
    obtain ⟨middleDisabled,middleAccessed⟩ := before.disabled disabled
    obtain ⟨lastDisabled,lastAccessed⟩ := after.disabled middleDisabled
    exact ⟨lastDisabled,lastAccessed.trans middleAccessed⟩

private theorem read_related (state : LocationState) (held : Bool) (related : AccessRelatedness) :
    Related state (state.performAccess .Read related held).resultingState held := by
  unfold Related NumericRelated
  rcases state with ⟨permission,accessed,cache⟩
  cases permission with
  | ReservedFrz conflicted =>
    cases conflicted <;> cases accessed <;> cases cache <;> cases held <;> cases related <;> decide +kernel
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
    cases accessed <;> cases cache <;> cases held <;> cases related <;> decide +kernel

private theorem record_permission (state recorded : LocationState) (kind : AccessKind) (related : AccessRelatedness)
    (record : state.recordNewAccess kind related = .Recorded recorded) : recorded.permission = state.permission := by
  unfold LocationState.recordNewAccess at record
  split at record
  · cases record;rfl
  · cases record

private theorem record_accessed (state recorded : LocationState) (kind : AccessKind) (related : AccessRelatedness)
    (record : state.recordNewAccess kind related = .Recorded recorded) : recorded.accessed = state.accessed := by
  unfold LocationState.recordNewAccess at record
  split at record
  · cases record;rfl
  · cases record

/-- Transport any established raw cache bound through the exact Read effect.
The cached value is arbitrary; this lemma does not order descendant caches. -/
theorem transport (before after : LocationState) (held : Bool) (cached : IdempotentForeignAccess)
    (related : Related before after held)
    (bound : Consistent {before with idempotentForeignAccess := cached} held) :
    Consistent {after with idempotentForeignAccess := cached} held := by
  obtain ⟨oldStrength,oldTable,oldBound⟩ := bound
  have good : valid before.permission held = true := by simp only [valid,oldTable]
  obtain ⟨newGood,monotone⟩ := related.numeric.1 good
  cases table : after.permission.strongestIdempotentForeignAccess held with
  | ImpossibleProtectedReservedIM => simp only [valid,table,Bool.false_eq_true] at newGood
  | Access newStrength =>
    refine ⟨newStrength,table,?_⟩
    simp only [rank,oldTable,table] at monotone
    exact Nat.le_trans oldBound monotone

/-- Pointwise relation includes unexposed nodes and latent future Write
contributors; the old exposed-only support-mask model does not supply it. -/
def Effects (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags) : Prop :=
  ∀ index node,tree.nodes.get index = some node →
    Related (effective initial index node) (effective current index node) (protections.contains node.tag)

theorem initial (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) :
    Effects tree location location protections := by
  intro index node present
  exact refl_related _ _

theorem materialize (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (effects : Effects tree initial current protections) (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node) :
    Effects tree initial (materialized current index node) protections := by
  intro query queryNode found
  rw [GeneralBorrowExposedVirtualSchedule.materialized_effective tree current index node present query queryNode found]
  exact effects query queryNode found

/-- Consumes the actual Read callback's intermediate source equations; its
whole-DFS consumer derives them. Every unrelated node is physically framed. -/
theorem update (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (effects : Effects tree initial current protections) (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node) (recorded next : LocationState) (delta : PermTransition)
    (related : AccessRelatedness)
    (record : (effective current index node).recordNewAccess .Read related = .Recorded recorded)
    (access : recorded.performAccess .Read related (protections.contains node.tag) = .Success next delta) :
    Effects tree initial (updated tree current index node protections recorded next delta) protections := by
  intro query queryNode found
  by_cases same : query = index
  · subst query
    have nodeEq := Option.some.inj (present.symm.trans found)
    subst queryNode
    have step := read_related recorded (protections.contains node.tag) related
    rw [access] at step
    simp only [LocationState.AccessResult.resultingState] at step
    have permission := record_permission _ _ _ _ record
    have accessed := record_accessed _ _ _ _ record
    have step' : Related (effective current index node) next (protections.contains node.tag) := by
      simpa only [Related,NumericRelated,permission,accessed] using step
    have all := trans_related _ _ _ _ (effects index node present) step'
    simpa only [effective,updated,GeneralBorrowWildcardSubtreeState.write_same,Option.getD_some] using all
  · simpa only [effective,updated_other tree current index query node protections recorded next delta same] using effects query queryNode found

/-- The exact pointwise Read effect makes every final live cone already live
initially. This is the barrier lemma needed for semantic cache preservation. -/
theorem live_backward (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (effects : Effects tree initial current protections) (query witness : UniIndex)
    (live : LiveCone tree current query witness) : LiveCone tree initial query witness := by
  intro middle node present queryWalk witnessWalk
  exact (effects middle node present).barrier (live middle node present queryWalk witnessWalk)

end DuplicatePrefix.S05SemanticReadEffects
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S05SemanticReadEffects.initial,
      ``DuplicatePrefix.S05SemanticReadEffects.materialize,
      ``DuplicatePrefix.S05SemanticReadEffects.update,
      ``DuplicatePrefix.S05SemanticReadEffects.live_backward,
      ``DuplicatePrefix.S05SemanticReadEffects.transport] do
    for ax in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "unapproved axiom {ax}"
