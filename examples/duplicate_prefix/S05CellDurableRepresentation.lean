import duplicate_prefix.S05ScalarPermissionTransfer

/-! A necessary scalar representation distinction for unprotected Cell.
Exact one/two-step witnesses refute durability of the weaker Allows inclusion;
no ordinary-input predicate or sufficient representation preorder is adopted. -/
namespace DuplicatePrefix.S05CellDurableRepresentation
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership S05ScalarPermissionTransfer
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option cbv.maxSteps 1000000
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

private theorem disabled_not_cell (rawAccessed selectedAccessed : Bool)
    (rawSifa selectedSifa : IdempotentForeignAccess) :
    ¬ Includes ⟨.Disabled,rawAccessed,rawSifa⟩ ⟨.Cell,selectedAccessed,selectedSifa⟩ false := by
  intro inclusion
  have selectedRead : Allows ⟨.Cell,selectedAccessed,selectedSifa⟩ false .Read .LocalAccess := by
    simp [Allows,GeneralBorrowProtectedReadCompatible.Compatible,LocationState.possible,Permission.isUnique]
  have rawRead := inclusion.2.2 .Read .LocalAccess selectedRead
  simp [Allows,GeneralBorrowProtectedReadCompatible.Compatible] at rawRead

/-- Every non-Cell representation of an initially included unprotected Cell
has an exact synchronized bad sequence: ForeignWrite alone, or LocalWrite
followed by ForeignWrite for ReservedIM. All operations succeed. -/
theorem noncell_bad_sequence (raw selected : LocationState)
    (cell : selected.permission = .Cell) (initial : Includes raw selected false)
    (different : raw.permission ≠ .Cell) :
    (∃ rawNext selectedNext rawDelta selectedDelta,
      raw.performAccess .Write .ForeignAccess false = .Success rawNext rawDelta ∧
      selected.performAccess .Write .ForeignAccess false = .Success selectedNext selectedDelta ∧
      ¬ Includes rawNext selectedNext false) ∨
    (∃ rawMid selectedMid rawNext selectedNext rawDelta₁ selectedDelta₁ rawDelta₂ selectedDelta₂,
      raw.performAccess .Write .LocalAccess false = .Success rawMid rawDelta₁ ∧
      selected.performAccess .Write .LocalAccess false = .Success selectedMid selectedDelta₁ ∧
      rawMid.performAccess .Write .ForeignAccess false = .Success rawNext rawDelta₂ ∧
      selectedMid.performAccess .Write .ForeignAccess false = .Success selectedNext selectedDelta₂ ∧
      ¬ Includes rawNext selectedNext false) := by
  rcases raw with ⟨rawPermission,rawAccessed,rawSifa⟩
  rcases selected with ⟨selectedPermission,selectedAccessed,selectedSifa⟩
  change selectedPermission = .Cell at cell
  subst selectedPermission
  have selectedWrite : Allows ⟨.Cell,selectedAccessed,selectedSifa⟩ false .Write .LocalAccess := by
    simp [Allows,GeneralBorrowExposedConditionalWritePermissions.Compatible,LocationState.possible,Permission.isUnique]
  have rawWrite := initial.2.2 .Write .LocalAccess selectedWrite
  cases rawPermission with
  | Cell => exact False.elim (different rfl)
  | Frozen | Disabled =>
    simp [Allows,GeneralBorrowExposedConditionalWritePermissions.Compatible] at rawWrite
  | ReservedFrz conflicted =>
    refine .inl ⟨⟨.Disabled,rawAccessed,rawSifa⟩,⟨.Cell,selectedAccessed,selectedSifa⟩,
      ⟨.ReservedFrz conflicted,.Disabled⟩,⟨.Cell,.Cell⟩,?_,?_,disabled_not_cell _ _ _ _⟩
    · cases rawAccessed <;> cases conflicted <;> rfl
    · cases selectedAccessed <;> rfl
  | Unique =>
    refine .inl ⟨⟨.Disabled,rawAccessed,rawSifa⟩,⟨.Cell,selectedAccessed,selectedSifa⟩,
      ⟨.Unique,.Disabled⟩,⟨.Cell,.Cell⟩,?_,?_,disabled_not_cell _ _ _ _⟩
    · cases rawAccessed <;> rfl
    · cases selectedAccessed <;> rfl
  | ReservedIM =>
    refine .inr ⟨⟨.Unique,true,rawSifa⟩,⟨.Cell,true,selectedSifa⟩,
      ⟨.Disabled,true,rawSifa⟩,⟨.Cell,true,selectedSifa⟩,
      ⟨.ReservedIM,.Unique⟩,⟨.Cell,.Cell⟩,⟨.Unique,.Disabled⟩,⟨.Cell,.Cell⟩,
      ?_,?_,rfl,rfl,disabled_not_cell _ _ _ _⟩
    · cases rawAccessed <;> rfl
    · cases selectedAccessed <;> rfl

/-- A metatheorem about relations claiming these bounded synchronized
preservations. Operation equations are transition witnesses, not validity
conditions imposed on ordinary callers. -/
theorem durable_cell_necessary (raw selected : LocationState)
    (cell : selected.permission = .Cell) (initial : Includes raw selected false)
    (one : ∀ rawNext selectedNext rawDelta selectedDelta,
      raw.performAccess .Write .ForeignAccess false = .Success rawNext rawDelta →
      selected.performAccess .Write .ForeignAccess false = .Success selectedNext selectedDelta →
      Includes rawNext selectedNext false)
    (two : ∀ rawMid selectedMid rawNext selectedNext rawDelta₁ selectedDelta₁ rawDelta₂ selectedDelta₂,
      raw.performAccess .Write .LocalAccess false = .Success rawMid rawDelta₁ →
      selected.performAccess .Write .LocalAccess false = .Success selectedMid selectedDelta₁ →
      rawMid.performAccess .Write .ForeignAccess false = .Success rawNext rawDelta₂ →
      selectedMid.performAccess .Write .ForeignAccess false = .Success selectedNext selectedDelta₂ →
      Includes rawNext selectedNext false) : raw.permission = .Cell := by
  by_cases same : raw.permission = .Cell
  · exact same
  · rcases noncell_bad_sequence raw selected cell initial same with badOne | badTwo
    · obtain ⟨rawNext,selectedNext,rawDelta,selectedDelta,rawStep,selectedStep,failed⟩ := badOne
      exact False.elim (failed (one rawNext selectedNext rawDelta selectedDelta rawStep selectedStep))
    · obtain ⟨rawMid,selectedMid,rawNext,selectedNext,rawDelta₁,selectedDelta₁,rawDelta₂,selectedDelta₂,
        rawStep₁,selectedStep₁,rawStep₂,selectedStep₂,failed⟩ := badTwo
      exact False.elim (failed (two rawMid selectedMid rawNext selectedNext rawDelta₁ selectedDelta₁
        rawDelta₂ selectedDelta₂ rawStep₁ selectedStep₁ rawStep₂ selectedStep₂))

/-- Every scalar outcome, including retained error states, preserves the
Cell/non-Cell distinction. This does not cover newChild or materialization. -/
theorem perform_access_cell_iff (state : LocationState) (kind : AccessKind)
    (relation : AccessRelatedness) (held : Bool) :
    (state.performAccess kind relation held).resultingState.permission = .Cell ↔
      state.permission = .Cell := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission <;> try (rename_i conflicted; cases conflicted)
  all_goals cases accessed <;> cases kind <;> cases relation <;> cases held
  all_goals cbv <;> simp

/-- Immediate use on the existing matched A replay: the raw Either row is
retained, while the selected scalar ForeignRead has its exact recorded
endpoint. No skipped scalar invocation is asserted. -/
theorem default_read_a_cell_agreement :
    DefaultReadA.rawAfter.permission = .Cell ↔ DefaultReadA.selectedAfter.permission = .Cell := by
  have before : DefaultReadA.rawBefore = DefaultReadA.selectedBefore := by cbv
  have selected := perform_access_cell_iff DefaultReadA.selectedBefore .Read .ForeignAccess DefaultReadA.held
  rw [DefaultReadA.scalar_step] at selected
  rw [DefaultReadA.raw_retained,before]
  exact selected.symm

private def endpointCellCheck (i : Fin 11) : Bool := decide
  ((S05ZeroCellCurrentCorrelation.state S05ZeroCellCurrentCorrelation.precise i).permission = .Cell →
    (S05ZeroCellCurrentCorrelation.state S05ZeroCellCurrentCorrelation.raw i).permission = .Cell)

private theorem endpoint_cell_checks : ((List.finRange 11).all endpointCellCheck) = true := by cbv

/-- The existing generated eleven-node current-row certificate satisfies
this necessary Cell distinction. It does not establish sufficient or durable
representation of all permissions or ordinary-input coverage. -/
theorem endpoint_cell_agreement (i : Fin 11)
    (cell : (S05ZeroCellCurrentCorrelation.state S05ZeroCellCurrentCorrelation.precise i).permission = .Cell) :
    (S05ZeroCellCurrentCorrelation.state S05ZeroCellCurrentCorrelation.raw i).permission = .Cell := by
  have checked := List.all_eq_true.mp endpoint_cell_checks i (List.mem_finRange i)
  exact (of_decide_eq_true checked) cell

end DuplicatePrefix.S05CellDurableRepresentation

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05CellDurableRepresentation." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved durable Cell dependency {dependency}"
