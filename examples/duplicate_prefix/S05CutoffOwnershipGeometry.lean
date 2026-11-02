import duplicate_prefix.S05NoCutoffOwnershipBridge
import duplicate_prefix.DuplicatePrefixResidualWriteSkip

namespace DuplicatePrefix.S05CutoffOwnershipGeometry
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality GeneralBorrowExposureAncestorFold GeneralBorrowExposedNonleafPrimaryPath
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization GeneralBorrowWildcardParentTagOrder
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- A real cutoff-eligible exposed Write supporter at the physical primary
root. This is initial provenance/permission data, not a callback success. -/
def CutoffWitness (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (_root : UniIndex) (position : Nat) (maximum : Option BorTag) (support : UniIndex → Prop) : Prop :=
  position = 0 → ∃ witness node,support witness ∧ tree.nodes.get witness = some node ∧
    Supports location protections witness node maximum .Write

private theorem filter_strict {α : Type} (rows : List α) (first second : α → Bool)
    (included : ∀ row ∈ rows,first row = true → second row = true)
    (gap : ∃ row ∈ rows,second row = true ∧ first row = false) :
    (rows.filter first).length < (rows.filter second).length := by
  have equal : (rows.filter second).filter first = rows.filter first := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro row member
    cases original : first row with
    | false => simp [original]
    | true => simp [original,included row member original]
  rw [←equal]
  apply List.length_filter_lt_length_iff_exists.mpr
  obtain ⟨row,member,right,left⟩ := gap
  exact ⟨row,List.mem_filter.mpr ⟨member,right⟩,by simp only [left,Bool.false_eq_true,not_false_eq_true]⟩

/-- A retained eligible supporter outside a query's ancestor cone makes its
residual count strictly smaller than the root's, for every legal mask. -/
theorem residual_strict (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (root query witness : UniIndex)
    (witnessNode : TreeNode) (present : tree.nodes.get witness = some witnessNode)
    (maximum : Option BorTag) (kind : AccessKind) (removed : List UniIndex)
    (legal : Removal tree location protections maximum kind removed)
    (eligible : Supports location protections witness witnessNode maximum kind)
    (rootPath : Path tree root witness) (outside : query ∉ walk tree.nodes (tree.nodes.size+1) witness)
    (covers : Covers tree.nodes root query) :
    residualCount tree location protections kind removed query < residualCount tree location protections kind removed root := by
  have retained := GeneralBorrowResidualPrimaryWitness.witness_retained tree location protections maximum kind removed legal witness witnessNode present eligible
  have support_allows (level : WildcardAccessLevel) : supports level kind = level.allows kind := by
    cases level <;> cases kind <;> rfl
  have supported : supports (effective location protections witness witnessNode) kind = true := by
    rw [support_allows]
    exact eligible.2.1
  unfold residualCount
  rw [List.filter_filter,List.filter_filter]
  apply filter_strict
  · intro row member qualified
    simp only [Bool.and_eq_true,contributes,List.contains_iff_mem] at qualified ⊢
    exact ⟨qualified.1,qualified.2.1,covers row member qualified.2.2⟩
  · refine ⟨(witness,witnessNode),(GeneralBorrowFreshReuseProtection.entries_get tree.nodes witness witnessNode).mpr present,?_,?_⟩
    · simp only [contributes,eligible.1,supported,Bool.true_and]
      simp [retained,rootPath.walk depth]
    · simp [contributes,eligible.1,supported,List.contains_iff_mem,outside]

private theorem write_allows (level : WildcardAccessLevel) (kind : AccessKind)
    (write : level.allows .Write = true) : level.allows kind = true := by
  cases level <;> cases kind <;> simp_all [WildcardAccessLevel.allows]

/-- The same raw Write witness supports both access kinds at the cutoff. -/
theorem witness_kind (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (support : UniIndex → Prop)
    (witness : CutoffWitness tree location protections root position maximum support) (kind : AccessKind) :
    position = 0 → ∃ index node,support index ∧ tree.nodes.get index = some node ∧
      Supports location protections index node maximum kind := by
  intro primary
  obtain ⟨index,node,inside,present,exposed,write,cutoff⟩ := witness primary
  exact ⟨index,node,inside,present,exposed,write_allows _ kind write,cutoff⟩

/-- Every legal mask has positive total support, using a real retained witness
at the physical primary and the interpreter's virtual alternative elsewhere. -/
theorem total_positive (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag)
    (rights : S05NoCutoffOwnershipBridge.Ownership tree location protections root position)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (witness : CutoffWitness tree location protections root position maximum rights.area.contains)
    (kind : AccessKind) (removed : List UniIndex) (legal : Removal tree location protections maximum kind removed) :
    0 < residualCount tree location protections kind removed root + if position != 0 then 1 else 0 := by
  by_cases primary : position = 0
  · obtain ⟨index,node,inside,present,eligible⟩ := witness_kind tree location protections root position maximum rights.area.contains witness kind primary
    have path := GeneralBorrowWildcardControlWitness.path_of_covers tree depth root index node present (rights.covers index inside)
    have positive := GeneralBorrowResidualPrimaryWitness.positive tree location protections depth maximum kind removed legal root index node present eligible path
    simpa only [primary,bne_self_eq_false,Bool.false_eq_true,ite_false,Nat.add_zero] using positive
  · simp only [show (position != 0) = true by simp [primary],ite_true]
    omega

private theorem clamped_gap (rootCount localCount : Nat) (virtual : Bool)
    (gap : localCount < rootCount + if virtual then 1 else 0) :
    classify rootCount localCount virtual true = some .ForeignAccess := by
  cases virtual <;> by_cases rootZero : rootCount = 0 <;> by_cases same : rootCount = localCount <;>
    by_cases plusSame : rootCount+1 = localCount <;> by_cases localZero : localCount = 0 <;>
    simp_all [classify] <;> omega

/-- Cutoff-eligible primary ownership and parent-tag order rule out clamped
absent relations without using Authorization itself. This is the geometric
half of the concrete residual-pair bridge. -/
theorem clamped_foreign (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag)
    (rights : S05NoCutoffOwnershipBridge.Ownership tree location protections root position)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (witness : CutoffWitness tree location protections root position maximum rights.area.contains)
    (query : UniIndex) (node : TreeNode) (inside : rights.area.contains query) (present : tree.nodes.get query = some node)
    (above : aboveMaximum node maximum = true)
    (kind : AccessKind) (removed : List UniIndex) (legal : Removal tree location protections maximum kind removed) :
    residualRelation tree location protections root query node maximum kind position removed = some .ForeignAccess := by
  have bound : residualCount tree location protections kind removed query ≤ residualCount tree location protections kind removed root := by
    rw [DuplicatePrefixResidualCountModel.count_as_cardinality,DuplicatePrefixResidualCountModel.count_as_cardinality]
    exact cardinality_dominates _ _ _ _ kind (rights.covers query inside)
  have gap : residualCount tree location protections kind removed query <
      residualCount tree location protections kind removed root + if position != 0 then 1 else 0 := by
    by_cases primary : position = 0
    · obtain ⟨index,witnessNode,included,found,eligible⟩ := witness_kind tree location protections root position maximum rights.area.contains witness kind primary
      have path := GeneralBorrowWildcardControlWitness.path_of_covers tree depth root index witnessNode found (rights.covers index included)
      have outside : query ∉ walk tree.nodes (tree.nodes.size+1) index := by
        intro walked
        have localPath := GeneralBorrowWildcardControlWitness.path_of_walk tree depth query index witnessNode found _ walked
        have notAbove := path_not_above tree order location protections maximum kind query index node witnessNode present found localPath eligible
        rw [above] at notAbove
        cases notAbove
      have strict := residual_strict tree location protections depth root query index witnessNode found maximum kind removed legal eligible path outside (rights.covers query inside)
      simpa only [primary,bne_self_eq_false,Bool.false_eq_true,ite_false,Nat.add_zero] using strict
    · simp only [show (position != 0) = true by simp [primary],ite_true]
      omega
  simpa only [residualRelation,above] using clamped_gap _ _ _ gap

end DuplicatePrefix.S05CutoffOwnershipGeometry
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S05CutoffOwnershipGeometry.residual_strict,
      ``DuplicatePrefix.S05CutoffOwnershipGeometry.witness_kind,
      ``DuplicatePrefix.S05CutoffOwnershipGeometry.total_positive,
      ``DuplicatePrefix.S05CutoffOwnershipGeometry.clamped_foreign] do
    for ax in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "unapproved axiom {ax}"
