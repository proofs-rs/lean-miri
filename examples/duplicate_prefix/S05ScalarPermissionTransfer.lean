import duplicate_prefix.CandidateStableCallOwnership
import duplicate_prefix.S05ZeroCellCurrentCorrelation

/-! Fixed-protector scalar permission inclusion only. These claims exclude
recording, SIFA bounds, caches, residual masks, protector changes and tree
correspondence. They do not adopt the candidate interpretation as validity. -/
namespace DuplicatePrefix.S05ScalarPermissionTransfer
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

def Includes (raw selected : LocationState) (held : Bool) : Prop :=
  raw.possible = true ∧ selected.possible = true ∧
    ∀ kind relation, Allows selected held kind relation → Allows raw held kind relation

/-- A successful scalar transition only removes admissible permission-table
queries at the same fixed protector bit. -/
theorem precise_step_shrinks (selected next : LocationState) (held : Bool)
    (kind : AccessKind) (relation : AccessRelatedness) (transition : PermTransition)
    (possible : selected.possible = true)
    (step : selected.performAccess kind relation held = .Success next transition) :
    next.possible = true ∧
      ∀ queryKind queryRelation, Allows next held queryKind queryRelation →
        Allows selected held queryKind queryRelation := by
  rcases selected with ⟨permission,accessed,sifa⟩
  cases permission <;> try (rename_i conflicted; cases conflicted)
  all_goals cases accessed <;> cases sifa <;> cases held <;> cases kind <;> cases relation
  all_goals simp [LocationState.possible,Permission.isUnique] at possible
  all_goals cbv at step
  all_goals cases step
  all_goals
    constructor
    · rfl
    · intro queryKind queryRelation allowed
      cases queryKind <;> cases queryRelation <;>
        simp_all [Allows,GeneralBorrowProtectedReadCompatible.Compatible,
          GeneralBorrowExposedConditionalWritePermissions.Compatible,
          LocationState.possible,Permission.isUnique]

/-- An Either/no-op raw scalar step preserves inclusion when its selected
precise alternative makes an exact successful step. -/
theorem raw_noop (raw selected next : LocationState) (held : Bool)
    (kind : AccessKind) (relation : AccessRelatedness) (transition : PermTransition)
    (initial : Includes raw selected held)
    (step : selected.performAccess kind relation held = .Success next transition) :
    Includes raw next held := by
  obtain ⟨possible,shrinks⟩ := precise_step_shrinks selected next held kind relation transition initial.2.1 step
  exact ⟨initial.1,possible,fun queryKind queryRelation allowed =>
    initial.2.2 queryKind queryRelation (shrinks queryKind queryRelation allowed)⟩

/- The A row of the existing generated AsMut default Read. The precise
side retains the original1 attachment chosen before all generated events.
These aliases are actual replay endpoints, not new scalar fixture states. -/
namespace DefaultReadA
open S05ZeroCellTypedGeneratedPrefix
set_option cbv.maxSteps 1000000
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail
def rawBefore := S05ZeroCellCurrentCorrelation.state
  S05ZeroCellActualCallAsMutReturn.PureTree.tree ⟨1,by decide⟩
def rawAfter := S05ZeroCellCurrentCorrelation.state
  S05ZeroCellActualCallAsMutReturn.PureTree.defaultRead.tree ⟨1,by decide⟩
def selectedBefore := S05ZeroCellCurrentCorrelation.state
  S05ZeroCellCurrentCorrelation.Precise.lenReleased.tree ⟨1,by decide⟩
def selectedAfter := S05ZeroCellCurrentCorrelation.state
  S05ZeroCellCurrentCorrelation.Precise.defaultRead.tree ⟨1,by decide⟩
def held := S05ZeroCellActualCallAsMutReturn.PureTree.tracker.global.protectedTags.contains (tag 2)

theorem raw_either :
    let location := ((S05ZeroCellActualCallAsMutReturn.PureTree.tree.locations.entries[0]?).map (·.data)).getD default
    location.exposedCache.accessRelatedness (ix 1) (ix 1) .Read true false = some .EitherAccess := by cbv

theorem initial : Includes rawBefore selectedBefore held := by
  have same : rawBefore = selectedBefore := by cbv
  have possible : rawBefore.possible = true := by cbv
  rw [←same]
  exact ⟨possible,possible,fun _ _ allowed => allowed⟩

theorem scalar_step : selectedBefore.performAccess .Read .ForeignAccess held =
    .Success selectedAfter ⟨.Cell,.Cell⟩ := by cbv
theorem raw_retained : rawAfter = rawBefore := by cbv

/-- Consume the generic scalar theorem on the matched existing replay row.
The scalar ForeignRead is a no-op: this does not assert that the visitor calls
performAccess after its own skip check, or prove correspondence for other rows. -/
theorem endpoint_inclusion : Includes rawAfter selectedAfter held := by
  rw [raw_retained]
  exact raw_noop rawBefore selectedBefore selectedAfter held .Read .ForeignAccess
    ⟨.Cell,.Cell⟩ initial scalar_step
end DefaultReadA

/- Four-way Allows inclusion does not distinguish Cell from a reservation
when unprotected. Their synchronized foreign Write successors do differ.
This is a scalar abstraction counterexample, not an ordinary-input history. -/
namespace SynchronizedCounterexample
def raw : LocationState := ⟨.ReservedFrz false,false,.None⟩
def selected : LocationState := ⟨.Cell,false,.None⟩
def rawNext : LocationState := ⟨.Disabled,false,.None⟩

theorem initial : Includes raw selected false := by
  refine ⟨rfl,rfl,?_⟩
  intro kind relation allowed
  cases kind <;> cases relation <;>
    simp_all [Allows,raw,selected,GeneralBorrowProtectedReadCompatible.Compatible,
      GeneralBorrowExposedConditionalWritePermissions.Compatible,LocationState.possible,Permission.isUnique]

theorem raw_step : raw.performAccess .Write .ForeignAccess false =
    .Success rawNext ⟨.ReservedFrz false,.Disabled⟩ := rfl
theorem selected_step : selected.performAccess .Write .ForeignAccess false =
    .Success selected ⟨.Cell,.Cell⟩ := rfl

theorem representation_consistent :
    GeneralBorrowSifaPermissionConsistency.Consistent raw false ∧
    GeneralBorrowSifaPermissionConsistency.Consistent selected false := by
  exact ⟨⟨.Read,rfl,by decide⟩,⟨.Write,rfl,by decide⟩⟩

theorem successor_not_included : ¬ Includes rawNext selected false := by
  intro inclusion
  have allowed : Allows selected false .Read .LocalAccess := by
    simp [Allows,selected,GeneralBorrowProtectedReadCompatible.Compatible,LocationState.possible,Permission.isUnique]
  have forbidden := inclusion.2.2 .Read .LocalAccess allowed
  simp [Allows,rawNext,GeneralBorrowProtectedReadCompatible.Compatible] at forbidden
end SynchronizedCounterexample

end DuplicatePrefix.S05ScalarPermissionTransfer

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05ScalarPermissionTransfer." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved scalar transfer dependency {dependency}"
