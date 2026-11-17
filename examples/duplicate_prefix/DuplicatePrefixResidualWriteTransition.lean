import duplicate_prefix.DuplicatePrefixResidualSupportSnapshotBridge
import duplicate_prefix.GeneralBorrowExposedConditionalWritePermissions
namespace DuplicatePrefix.DuplicatePrefixResidualWriteTransition
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization
open GeneralBorrowExposedConditionalWritePermissions
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Only Unique and freezable-reservation Write contributions can be lost by
an actual foreign Write. This local transition lemma assumes its exact scalar
result; the visit theorem below derives that result from compatibility. -/
theorem foreign_loss (state next : LocationState) (held : Bool) (delta : PermTransition)
    (initial : Compatible state .ForeignAccess held)
    (actual : state.performAccess .Write .ForeignAccess held = .Success next delta)
    (before : support state held = true) (after : support next held = false) :
    losesWriteWhenForeign state.permission = true := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | Unique => rfl
  | ReservedFrz conflicted => rfl
  | Frozen | Disabled =>
    simp [support, GeneralBorrowExposureCardinality.supports, Permission.strongestAllowedLocalAccess,
      GeneralBorrowExposureAncestorFold.supportsWrite] at before
  | Cell | ReservedIM =>
    cases accessed <;> cases sifa <;> cases held <;>
      simp [Compatible, LocationState.possible, Permission.isUnique] at initial
    all_goals
      change LocationState.AccessResult.Success _ _ = .Success next delta at actual
      cases actual
      simp [support, GeneralBorrowExposureCardinality.supports, Permission.strongestAllowedLocalAccess,
        GeneralBorrowExposureAncestorFold.supportsWrite] at after

/-- The genuine scheduled record/Write branch does not gain Write support.
Any loss is foreign and has exactly the removable permission classes. -/
theorem visit (state : LocationState) (related : AccessRelatedness) (held : Bool)
    (initial : Compatible state related held)
    (scheduled : GeneralBorrowEvents.Scheduled state .Write related) :
    ∃ recorded next delta, state.recordNewAccess .Write related = .Recorded recorded ∧
      recorded.performAccess .Write related held = .Success next delta ∧ Compatible next related held ∧
      (support state held = false → support next held = false) ∧
      (support state held = true → support next held = false →
        related = .ForeignAccess ∧ losesWriteWhenForeign state.permission = true) := by
  obtain ⟨recorded,next,delta,record,actual,good,localSupport,noGain⟩ :=
    GeneralBorrowExposedConditionalWritePermissions.visit state related held initial scheduled
  refine ⟨recorded,next,delta,record,actual,good,noGain,?_⟩
  intro before after
  cases related with
  | LocalAccess => rw [localSupport rfl, before] at after; cases after
  | ForeignAccess =>
    refine ⟨rfl,?_⟩
    have recordedEq : recorded = {state with idempotentForeignAccess :=
        (IdempotentForeignAccess.recordNew state.idempotentForeignAccess
          (IdempotentForeignAccess.fromAccessAndRelatedness .Write .ForeignAccess))} := by
      simpa [LocationState.recordNewAccess, GeneralBorrowEvents.scheduled_recurse _ _ _ scheduled] using record.symm
    subst recorded
    exact foreign_loss {state with idempotentForeignAccess :=
      (IdempotentForeignAccess.recordNew state.idempotentForeignAccess
        (IdempotentForeignAccess.fromAccessAndRelatedness .Write .ForeignAccess))}
      next held delta initial actual before after

/-- A positive local contributor cannot be classified exact foreign without
the above-maximum filter, for either real or virtual selected roots. -/
theorem classify_foreign_above (rootCount localCount : Nat) (virtual onlyForeign : Bool)
    (positive : 0 < localCount)
    (foreign : classify rootCount localCount virtual onlyForeign = some .ForeignAccess) : onlyForeign = true := by
  cases onlyForeign with
  | true => rfl
  | false =>
    have nonzero : localCount ≠ 0 := by omega
    by_cases zero : rootCount + (if virtual then 1 else 0) = 0
    · simp [classify, zero] at foreign
    · by_cases equal : rootCount + (if virtual then 1 else 0) = localCount
      · simp [classify, equal] at foreign
      · simp [classify, equal, nonzero] at foreign

/-- Actual coherent finite counters make every exposed supporter a positive
self contributor. Thus an exact foreign Write of such a node is above maximum. -/
theorem source_foreign_above (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root index : UniIndex) (node : TreeNode) (maximum : Option BorTag) (rootPosition : Nat)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (short : tree.nodes.size < 65536) (present : tree.nodes.get index = some node)
    (exposed : node.isExposed = true)
    (supported : GeneralBorrowExposureCardinality.supports (GeneralBorrowExposureCardinality.effective location protections index node) .Write = true)
    (foreign : relation location root index node maximum .Write rootPosition = some .ForeignAccess) :
    aboveMaximum node maximum = true := by
  have positive := GeneralBorrowExposureCardinality.exposed_self location.exposedCache tree.nodes
    (GeneralBorrowExposureCardinality.effective location protections) coherent short index node present exposed .Write supported
  exact classify_foreign_above _ _ _ _ positive foreign
/-- Exact source-compatible Write visitation of an exposed node cannot gain
support, and every lost contribution satisfies the finite residual model's
removal predicate. Source counters are required coherent and below their
explicit finite-width budget. No successful visit is a premise. -/
theorem visit_removable (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root index : UniIndex) (node : TreeNode) (maximum : Option BorTag) (rootPosition : Nat)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (short : tree.nodes.size < 65536) (present : tree.nodes.get index = some node)
    (exposed : node.isExposed = true) (query : WildcardAccessRelatedness) (related : AccessRelatedness)
    (source : relation location root index node maximum .Write rootPosition = some query)
    (exactQuery : exactRelation query = some related)
    (initial : Compatible ((location.perms.get index).getD node.defaultLocationState) related (protections.contains node.tag))
    (scheduled : GeneralBorrowEvents.Scheduled ((location.perms.get index).getD node.defaultLocationState) .Write related) :
    let state := (location.perms.get index).getD node.defaultLocationState
    let held := protections.contains node.tag
    ∃ recorded next delta, state.recordNewAccess .Write related = .Recorded recorded ∧
      recorded.performAccess .Write related held = .Success next delta ∧ Compatible next related held ∧
      (support state held = false → support next held = false) ∧
      (support state held = true → support next held = false →
        removable location protections maximum .Write index node = true) := by
  dsimp only
  obtain ⟨recorded,next,delta,record,actual,good,noGain,loss⟩ := visit _ related _ initial scheduled
  refine ⟨recorded,next,delta,record,actual,good,noGain,?_⟩
  intro before after
  obtain ⟨foreign,permission⟩ := loss before after
  have queryForeign : query = .ForeignAccess := by cases query <;> simp_all [exactRelation]
  subst query
  have above := source_foreign_above tree location protections root index node maximum rootPosition
    coherent short present exposed before source
  change node.isExposed && aboveMaximum node maximum &&
    support ((location.perms.get index).getD node.defaultLocationState) (protections.contains node.tag) &&
    losesWriteWhenForeign ((location.perms.get index).getD node.defaultLocationState).permission = true
  simp [exposed,above,before,permission]
end DuplicatePrefix.DuplicatePrefixResidualWriteTransition
