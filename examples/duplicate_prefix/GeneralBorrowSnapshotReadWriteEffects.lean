import duplicate_prefix.DuplicatePrefixResidualReadWriteEffects
import duplicate_prefix.GeneralBorrowSnapshotReadDFSRuntimeData
namespace DuplicatePrefix.GeneralBorrowSnapshotReadWriteEffects
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization
open DuplicatePrefixResidualCountModel
open GeneralBorrowWildcardVirtualLeaf (effective materialized)
open GeneralBorrowExposedNonleafState (updated)
open GeneralBorrowSnapshotReadState (wildcard)
open DuplicatePrefixResidualReadWriteEffects (Origin)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- A derived Write contribution model, carried during actual Read visitation.
The list and its legality are proof output, never caller assumptions. -/
def Effects (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (maximum : Option BorTag) : Prop :=
  ∃ removed, Removal tree initial protections maximum .Write removed ∧
    Matches tree initial current protections .Write removed ∧ Origin tree initial current protections

theorem initial (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (maximum : Option BorTag) : Effects tree location location protections maximum := by
  refine ⟨[],empty_removal tree location protections maximum .Write,?_,
    DuplicatePrefixResidualReadWriteEffects.origin_initial tree location protections⟩
  intro index node present exposed
  simp [levels]

theorem exact_inputs (state : LocationState) (held : Bool) (exact : AccessRelatedness)
    (scalar : Scalar state .Read held (some (wildcard exact)))
    (recurse : DuplicatePrefixCallbackVisitAuthorization.entrySkip state .Read (some (wildcard exact)) = false) :
    GeneralBorrowProtectedReadCompatible.Compatible state exact held ∧ GeneralBorrowEvents.Scheduled state .Read exact := by
  have skipped : skip state .Read exact = false := by cases exact <;> exact recurse
  have compatible : GeneralBorrowProtectedReadCompatible.Compatible state exact held := by
    cases exact <;> exact scalar.2.resolve_left (by simp [skipped])
  refine ⟨compatible,GeneralBorrowEvents.recurse_scheduled _ _ _ ?_⟩
  cases equality : state.skipIfKnownNoop .Read exact with
  | Recurse => rfl
  | SkipSelfAndChildren =>
    have yes := (skip_source _ _ _).mpr equality
    simp [skipped] at yes

/-- The actual action returned by the general Read post-step carries a legal
Write mask. Record/transition equations here are intermediate outputs of that
post-step; public callback endpoints below take no operation-success premise. -/
theorem post (tree : BorrowTree) (initial current after : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag) (support : UniIndex → Prop)
    (effects : Effects tree initial current protections maximum)
    (snapshot : Snapshot tree current protections root rootPosition maximum .Read support)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree current protections)
    (short : tree.nodes.size < 65536)
    (index : UniIndex) (node : TreeNode) (included : support index) (present : tree.nodes.get index = some node)
    (recurse : DuplicatePrefixCallbackVisitAuthorization.entrySkip (effective current index node) .Read
      (relation current root index node maximum .Read rootPosition) = false)
    (action : (relation current root index node maximum .Read rootPosition = some .EitherAccess ∧ after = materialized current index node) ∨
       ∃ exact recorded next delta,
         relation current root index node maximum .Read rootPosition = some (wildcard exact) ∧
         (effective current index node).recordNewAccess .Read exact = .Recorded recorded ∧
         recorded.performAccess .Read exact (protections.contains node.tag) = .Success next delta ∧
         after = updated tree current index node protections recorded next delta) :
    Effects tree initial after protections maximum := by
  obtain ⟨removed,legal,matching,origin⟩ := effects
  rcases action with ⟨classified,same⟩ | ⟨exact,recorded,next,delta,classified,record,actual,same⟩
  · subst after
    exact ⟨removed,legal,
      DuplicatePrefixResidualReadWriteEffects.materialized_matches tree initial current protections removed matching index node present,
      DuplicatePrefixResidualReadWriteEffects.materialized_origin tree initial current protections origin index node present⟩
  · subst after
    have scalar := snapshot.scalar index node included present
    rw [classified] at scalar recurse
    obtain ⟨compatible,scheduled⟩ := exact_inputs _ _ exact scalar recurse
    have exactQuery : exactRelation (wildcard exact) = some exact := by cases exact <;> rfl
    obtain ⟨recorded',next',delta',record',actual',good,legal',matching',coherent',other,origin'⟩ :=
      DuplicatePrefixResidualReadWriteEffects.step_origin tree initial current protections root index node maximum rootPosition
        removed legal matching origin coherent short depth present (wildcard exact) exact classified exactQuery compatible scheduled
    have sameRecord := record.symm.trans record'
    injection sameRecord with equalRecord
    subst recorded'
    have sameAccess := actual.symm.trans actual'
    injection sameAccess with equalNext equalDelta
    subst next'
    subst delta'
    exact ⟨_,legal',matching',origin'⟩
end DuplicatePrefix.GeneralBorrowSnapshotReadWriteEffects
