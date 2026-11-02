import duplicate_prefix.DuplicatePrefixResidualWriteTransition
import duplicate_prefix.GeneralBorrowExposedConditionalReadPermissions
namespace DuplicatePrefix.DuplicatePrefixResidualReadWriteSupport
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization
open GeneralBorrowProtectedReadCompatible (Compatible)
open GeneralBorrowExposedConditionalWritePermissions (support)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- An exact compatible Read cannot create a Write contribution. A lost Write
contribution must be foreign and have Unique/freezable-reservation permission.
The actual scalar transition is a conclusion. -/
theorem transition (state : LocationState) (related : AccessRelatedness) (held : Bool)
    (initial : Compatible state related held) :
    ∃ next delta, state.performAccess .Read related held = .Success next delta ∧
      Compatible next related held ∧
      (support state held = false → support next held = false) ∧
      (support state held = true → support next held = false →
        related = .ForeignAccess ∧ losesWriteWhenForeign state.permission = true) := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflicted =>
    cases conflicted <;> cases accessed <;> cases sifa <;> cases related <;> cases held <;>
      simp [Compatible,LocationState.possible,Permission.isUnique] at initial <;>
      (refine ⟨_,_,rfl,?_,?_,?_⟩; all_goals simp [Compatible,LocationState.possible,Permission.isUnique,AccessRelatedness.isForeign,
        support,GeneralBorrowExposureCardinality.supports,Permission.strongestAllowedLocalAccess,
        GeneralBorrowExposureAncestorFold.supportsWrite,losesWriteWhenForeign])
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
    cases accessed <;> cases sifa <;> cases related <;> cases held <;>
      simp [Compatible,LocationState.possible,Permission.isUnique] at initial <;>
      (refine ⟨_,_,rfl,?_,?_,?_⟩; all_goals simp [Compatible,LocationState.possible,Permission.isUnique,AccessRelatedness.isForeign,
        support,GeneralBorrowExposureCardinality.supports,Permission.strongestAllowedLocalAccess,
        GeneralBorrowExposureAncestorFold.supportsWrite,losesWriteWhenForeign])

/-- Scheduled record/Read uses the same real source pipeline and has the same
Write-contribution monotonicity. No successful operation is assumed. -/
theorem visit (state : LocationState) (related : AccessRelatedness) (held : Bool)
    (initial : Compatible state related held)
    (scheduled : GeneralBorrowEvents.Scheduled state .Read related) :
    ∃ recorded next delta, state.recordNewAccess .Read related = .Recorded recorded ∧
      recorded.performAccess .Read related held = .Success next delta ∧ Compatible next related held ∧
      (support state held = false → support next held = false) ∧
      (support state held = true → support next held = false →
        related = .ForeignAccess ∧ losesWriteWhenForeign state.permission = true) := by
  let recorded := {state with idempotentForeignAccess := (IdempotentForeignAccess.recordNew state.idempotentForeignAccess
    (IdempotentForeignAccess.fromAccessAndRelatedness .Read related))}
  have good : Compatible recorded related held := initial
  obtain ⟨next,delta,actual,compatible,noGain,loss⟩ := transition recorded related held good
  refine ⟨recorded,next,delta,?_,actual,compatible,noGain,loss⟩
  simp only [LocationState.recordNewAccess,GeneralBorrowEvents.scheduled_recurse state .Read related scheduled,
    beq_self_eq_true,↓reduceIte]
  rfl

/-- A Write contributor is also a Read contributor, for every permission and
protector state; the Read classifier must therefore use positive Read counts. -/
theorem write_support_read (state : LocationState) (held : Bool)
    (write : support state held = true) :
    GeneralBorrowExposureCardinality.supports (state.permission.strongestAllowedLocalAccess held) .Read = true := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflicted => cases conflicted <;> cases held <;> simp_all [support,
      GeneralBorrowExposureCardinality.supports,Permission.strongestAllowedLocalAccess,
      GeneralBorrowExposureAncestorFold.supportsWrite,GeneralBorrowExposureAncestorFold.supportsRead]
  | Cell | ReservedIM | Unique | Frozen | Disabled => cases held <;> simp_all [support,
      GeneralBorrowExposureCardinality.supports,Permission.strongestAllowedLocalAccess,
      GeneralBorrowExposureAncestorFold.supportsWrite,GeneralBorrowExposureAncestorFold.supportsRead]

/-- Exact foreign READ classification of an exposed Write supporter forces the
source tag cutoff. Uses coherent READ counters, rather than a Write query. -/
theorem source_read_foreign_above (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root index : UniIndex) (node : TreeNode) (maximum : Option BorTag) (rootPosition : Nat)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (short : tree.nodes.size < 65536) (present : tree.nodes.get index = some node)
    (exposed : node.isExposed = true)
    (supported : support ((location.perms.get index).getD node.defaultLocationState) (protections.contains node.tag) = true)
    (foreign : relation location root index node maximum .Read rootPosition = some .ForeignAccess) :
    aboveMaximum node maximum = true := by
  have readSupport := write_support_read _ _ supported
  have positive := GeneralBorrowExposureCardinality.exposed_self location.exposedCache tree.nodes
    (GeneralBorrowExposureCardinality.effective location protections) coherent short index node present exposed .Read readSupport
  exact DuplicatePrefixResidualWriteTransition.classify_foreign_above _ _ _ _ positive foreign

/-- Read-side source visitation can remove Write support only within the raw
Write residual model's permitted set. The actual record/Read result is derived. -/
theorem visit_removable (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root index : UniIndex) (node : TreeNode) (maximum : Option BorTag) (rootPosition : Nat)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (short : tree.nodes.size < 65536) (present : tree.nodes.get index = some node)
    (exposed : node.isExposed = true) (query : WildcardAccessRelatedness) (related : AccessRelatedness)
    (source : relation location root index node maximum .Read rootPosition = some query)
    (exactQuery : exactRelation query = some related)
    (initial : Compatible ((location.perms.get index).getD node.defaultLocationState) related (protections.contains node.tag))
    (scheduled : GeneralBorrowEvents.Scheduled ((location.perms.get index).getD node.defaultLocationState) .Read related) :
    let state := (location.perms.get index).getD node.defaultLocationState
    let held := protections.contains node.tag
    ∃ recorded next delta, state.recordNewAccess .Read related = .Recorded recorded ∧
      recorded.performAccess .Read related held = .Success next delta ∧ Compatible next related held ∧
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
  have above := source_read_foreign_above tree location protections root index node maximum rootPosition
    coherent short present exposed before source
  change node.isExposed && aboveMaximum node maximum &&
    support ((location.perms.get index).getD node.defaultLocationState) (protections.contains node.tag) &&
    losesWriteWhenForeign ((location.perms.get index).getD node.defaultLocationState).permission = true
  simp [exposed,above,before,permission]
end DuplicatePrefix.DuplicatePrefixResidualReadWriteSupport
