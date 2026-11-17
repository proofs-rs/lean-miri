import duplicate_prefix.DuplicatePrefixResidualCountModel
import duplicate_prefix.DuplicatePrefixResidualWriteQueries
namespace DuplicatePrefix.DuplicatePrefixResidualWriteSkip
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization
open DuplicatePrefixResidualCountModel
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem classify_virtual (rootCount localCount : Nat) (onlyForeign : Bool) (bounded : localCount ≤ rootCount) :
    classify rootCount localCount true onlyForeign =
      some (if onlyForeign || localCount == 0 then .ForeignAccess else .EitherAccess) := by
  have nonzero : rootCount + 1 ≠ 0 := by omega
  have different : rootCount + 1 ≠ localCount := by omega
  cases onlyForeign <;> by_cases zero : localCount = 0 <;> simp [classify,nonzero,different,zero]

/-- Virtual classification retains an exact Foreign query under a decrease
of local support, provided both local counts are dominated by their roots. -/
theorem virtual_foreign_persists (beforeRoot beforeLocal afterRoot afterLocal : Nat) (onlyForeign : Bool)
    (beforeBound : beforeLocal ≤ beforeRoot) (afterBound : afterLocal ≤ afterRoot)
    (localDecrease : afterLocal ≤ beforeLocal)
    (foreign : classify beforeRoot beforeLocal true onlyForeign = some .ForeignAccess) :
    classify afterRoot afterLocal true onlyForeign = some .ForeignAccess := by
  rw [classify_virtual _ _ _ beforeBound] at foreign
  rw [classify_virtual _ _ _ afterBound]
  cases onlyForeign with
  | true => simp
  | false =>
    have zero : beforeLocal = 0 := by
      by_cases zero : beforeLocal = 0
      · exact zero
      · simp [zero] at foreign
    have afterZero : afterLocal = 0 := by omega
    simp [afterZero]

theorem residual_le_initial (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (removed : List UniIndex) (query : UniIndex) :
    residualCount tree initial protections .Write removed query ≤
      GeneralBorrowExposureCardinality.cardinality tree.nodes
        (GeneralBorrowExposureCardinality.effective initial protections) query .Write := by
  exact List.length_filter_le _ _

theorem residual_dominates (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (removed : List UniIndex) (root index : UniIndex)
    (covers : GeneralBorrowExposureCardinality.Covers tree.nodes root index) :
    residualCount tree initial protections .Write removed index ≤
      residualCount tree initial protections .Write removed root := by
  rw [count_as_cardinality,count_as_cardinality]
  exact GeneralBorrowExposureCardinality.cardinality_dominates _ _ _ _ .Write covers

/-- Foreign initial queries at a virtual root remain Foreign under any legal
removal mask. Root dominance follows the actual ancestor coverage relation. -/
theorem virtual_source_foreign_persists (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (root index : UniIndex) (node : TreeNode) (maximum : Option BorTag) (rootPosition : Nat)
    (removed : List UniIndex) (matching : Matches tree initial current protections .Write removed)
    (initialCoherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (currentCoherent : GeneralBorrowExposureCardinality.LocationCoherent tree current protections)
    (short : tree.nodes.size < 65536) (virtual : rootPosition ≠ 0)
    (covers : GeneralBorrowExposureCardinality.Covers tree.nodes root index)
    (foreign : relation initial root index node maximum .Write rootPosition = some .ForeignAccess) :
    relation current root index node maximum .Write rootPosition = some .ForeignAccess := by
  rw [relation_matches tree initial current protections .Write removed matching currentCoherent short root index node maximum rootPosition]
  rw [←initial_relation tree initial protections root index node maximum .Write rootPosition initialCoherent short] at foreign
  have bounded := GeneralBorrowExposureCardinality.cardinality_dominates tree.nodes
    (GeneralBorrowExposureCardinality.effective initial protections) root index .Write covers
  have currentBound := residual_dominates tree initial protections removed root index covers
  have decrease := residual_le_initial tree initial protections removed index
  simp only [residualRelation,residual_empty,show (rootPosition != 0) = true by simp [virtual]] at foreign ⊢
  exact virtual_foreign_persists _ _ _ _ _ bounded currentBound decrease foreign

/-- Entry skipping can only occur on an exact Foreign classification. -/
theorem entry_skip_foreign (state : LocationState) (query : Option WildcardAccessRelatedness)
    (skipped : DuplicatePrefixCallbackVisitAuthorization.entrySkip state .Write query = true) :
    query = some .ForeignAccess := by
  cases query with
  | none => simp [DuplicatePrefixCallbackVisitAuthorization.entrySkip] at skipped
  | some related =>
    cases related <;> simp_all [DuplicatePrefixCallbackVisitAuthorization.entrySkip,skip,AccessRelatedness.isForeign]

/-- Virtual roots permit all maximum filters. With no maximum, legal Write
removal is empty and the whole query is unchanged. Physical root with a
maximum is intentionally outside this theorem: clamping can turn Foreign
into none after removing only outside contributors. -/
theorem entry_skip_persists (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (root index : UniIndex) (node : TreeNode) (maximum : Option BorTag) (rootPosition : Nat) (support : UniIndex → Prop)
    (authorization : Authorization tree initial protections root rootPosition maximum .Write support)
    (removed : List UniIndex) (legal : Removal tree initial protections maximum .Write removed)
    (matching : Matches tree initial current protections .Write removed)
    (initialCoherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (currentCoherent : GeneralBorrowExposureCardinality.LocationCoherent tree current protections)
    (short : tree.nodes.size < 65536) (inside : support index)
    (unvisited : current.perms.get index = initial.perms.get index)
    (scope : rootPosition ≠ 0 ∨ maximum = none)
    (skipped : DuplicatePrefixCallbackVisitAuthorization.entrySkip
      ((initial.perms.get index).getD node.defaultLocationState) .Write
      (relation initial root index node maximum .Write rootPosition) = true) :
    DuplicatePrefixCallbackVisitAuthorization.entrySkip
      ((current.perms.get index).getD node.defaultLocationState) .Write
      (relation current root index node maximum .Write rootPosition) = true := by
  rw [unvisited]
  rcases scope with virtual | noMaximum
  · have foreign := entry_skip_foreign _ _ skipped
    have afterForeign := virtual_source_foreign_persists tree initial current protections root index node maximum rootPosition removed
      matching initialCoherent currentCoherent short virtual (authorization.covers index inside) foreign
    rw [afterForeign]
    simpa only [foreign] using skipped
  · subst maximum
    have empty := no_maximum_removal_empty tree initial protections .Write removed legal
    subst removed
    rw [relation_matches tree initial current protections .Write [] matching currentCoherent short root index node none rootPosition,
      initial_relation tree initial protections root index node none .Write rootPosition initialCoherent short]
    exact skipped

/-- Consequently a current active entry was also active initially, in exactly
the scope of entry_skip_persists. This supports storing one initial skip bit
instead of a before-removal snapshot at each active ancestor. -/
theorem initially_not_skipped (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (root index : UniIndex) (node : TreeNode) (maximum : Option BorTag) (rootPosition : Nat) (support : UniIndex → Prop)
    (authorization : Authorization tree initial protections root rootPosition maximum .Write support)
    (removed : List UniIndex) (legal : Removal tree initial protections maximum .Write removed)
    (matching : Matches tree initial current protections .Write removed)
    (initialCoherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (currentCoherent : GeneralBorrowExposureCardinality.LocationCoherent tree current protections)
    (short : tree.nodes.size < 65536) (inside : support index)
    (unvisited : current.perms.get index = initial.perms.get index)
    (scope : rootPosition ≠ 0 ∨ maximum = none)
    (active : DuplicatePrefixCallbackVisitAuthorization.entrySkip
      ((current.perms.get index).getD node.defaultLocationState) .Write
      (relation current root index node maximum .Write rootPosition) = false) :
    DuplicatePrefixCallbackVisitAuthorization.entrySkip
      ((initial.perms.get index).getD node.defaultLocationState) .Write
      (relation initial root index node maximum .Write rootPosition) = false := by
  cases initialSkip : DuplicatePrefixCallbackVisitAuthorization.entrySkip
      ((initial.perms.get index).getD node.defaultLocationState) .Write
      (relation initial root index node maximum .Write rootPosition) with
  | false => rfl
  | true =>
    have impossible := entry_skip_persists tree initial current protections root index node maximum rootPosition support
      authorization removed legal matching initialCoherent currentCoherent short inside unvisited scope initialSkip
    rw [active] at impossible
    cases impossible
/-- At exit, a stored initial non-skip bit suffices. The query-pair contract
is instantiated at ([],removed), eliminating any ghost entry-removal map.
The earlier entry_skip_persists scope is needed only to obtain that bit. -/
theorem exit_from_initial (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (root index : UniIndex) (node : TreeNode) (maximum : Option BorTag) (rootPosition : Nat) (support : UniIndex → Prop)
    (authorization : Authorization tree initial protections root rootPosition maximum .Write support)
    (removed : List UniIndex) (legal : Removal tree initial protections maximum .Write removed)
    (matching : Matches tree initial current protections .Write removed)
    (initialCoherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (currentCoherent : GeneralBorrowExposureCardinality.LocationCoherent tree current protections)
    (short : tree.nodes.size < 65536) (inside : support index) (present : tree.nodes.get index = some node)
    (unvisited : current.perms.get index = initial.perms.get index)
    (initialActive : DuplicatePrefixCallbackVisitAuthorization.entrySkip
      ((initial.perms.get index).getD node.defaultLocationState) .Write
      (relation initial root index node maximum .Write rootPosition) = false) :
    ∃ related, relation current root index node maximum .Write rootPosition = some related ∧
      (related = .EitherAccess ∨ ∃ exact recorded next delta,
        exactRelation related = some exact ∧
        ((current.perms.get index).getD node.defaultLocationState).recordNewAccess .Write exact = .Recorded recorded ∧
        recorded.performAccess .Write exact (protections.contains node.tag) = .Success next delta) := by
  have initialMatches : Matches tree initial initial protections .Write [] := by
    intro query queryNode found exposed
    simp [levels]
  exact DuplicatePrefixResidualWriteQueries.exit_transition tree initial initial current protections root index node maximum rootPosition support
    authorization [] removed (empty_removal tree initial protections maximum .Write) legal
    (by intro query member; cases member) initialMatches matching initialCoherent currentCoherent short inside present rfl unvisited initialActive
end DuplicatePrefix.DuplicatePrefixResidualWriteSkip
