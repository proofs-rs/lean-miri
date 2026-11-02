import duplicate_prefix.GeneralBorrowSnapshotReadDFS
import duplicate_prefix.DuplicatePrefixResidualInitialSnapshot
namespace DuplicatePrefix.GeneralBorrowSnapshotVirtualReadAccess
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization
open GeneralBorrowExposedNonleafState (ReadFrame)
open GeneralBorrowWildcardPrimaryReadWitness (PointwiseReadFrame)
open GeneralBorrowSnapshotReadDFSPlan
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Virtual roots need no real exposed supporter: the source adds the virtual
foreign possibility and does not test the final seen bit. -/
def plan (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag) (virtual : rootPosition ≠ 0) :
    WitnessPlan tree initial protections root rootPosition maximum := {
  pending := fun _ _ => True
  initial := True.intro
  finish := fun _ _ => .inl (by simp [virtual])
  pop := by intros; trivial
  expand := by intros; trivial
  post := by intros; trivial }

/-- The actual virtual-root Read visitor completes for arbitrary finite forest
shape, protected/exposed permissions and tag cutoff, from the full raw snapshot.
Read support/count frames and genuine exposure-cache coherence survive. No
zero/nonzero permission profile, ForeignOwned, leaf, no-cutoff or operation-
success assumption is used. This is one real callback, not a whole function. -/
theorem access (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag) (virtual : rootPosition ≠ 0)
    (support : GeneralBorrowWildcardControlStack.Support tree root)
    (snapshot : Snapshot tree initial protections root rootPosition maximum .Read support.contains)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree initial protections).topology)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections) :
    let result := tree.performWildcardAccessAt initial root maximum .Read protections true
    result.status = .Completed ∧ ReadFrame initial result.location ∧
    Snapshot tree result.location protections root rootPosition maximum .Read support.contains ∧
    PointwiseReadFrame tree protections initial result.location ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections := by
  let weights := GeneralBorrowWildcardForestWeights.of_forest tree initial protections forest
  have actual := GeneralBorrowSnapshotReadDFS.access_plan tree initial protections root rootPosition maximum
    weights (GeneralBorrowWildcardForestWeights.bounded tree initial protections forest root) support snapshot depth coherent
    (plan tree initial protections root rootPosition maximum virtual)
  have virtualEq : (rootPosition != 0) = true := by simp [virtual]
  simpa only [virtualEq] using actual

/-- S01's data-only residual authorization directly supplies this real Read
callback; the source snapshot and graph support are internally constructed. -/
theorem of_authorization (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag) (virtual : rootPosition ≠ 0)
    (support : UniIndex → Prop)
    (authorization : DuplicatePrefixResidualSupportAuthorization.Authorization tree initial protections root rootPosition maximum .Read support)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree initial protections).topology)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (short : tree.nodes.size < 65536) :
    let result := tree.performWildcardAccessAt initial root maximum .Read protections true
    result.status = .Completed ∧ ReadFrame initial result.location ∧
    Snapshot tree result.location protections root rootPosition maximum .Read support ∧
    PointwiseReadFrame tree protections initial result.location ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections :=
  access tree initial protections root rootPosition maximum virtual
    (GeneralBorrowWildcardControlStack.Support.of_authorization tree initial protections root rootPosition maximum .Read support authorization)
    (DuplicatePrefixResidualInitialSnapshot.snapshot tree initial protections root rootPosition maximum .Read support authorization coherent short)
    depth forest coherent

/-- Actual virtual visitor also frames every optional slot outside its raw support. -/
theorem access_frame (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag) (virtual : rootPosition ≠ 0)
    (support : GeneralBorrowWildcardControlStack.Support tree root)
    (snapshot : Snapshot tree initial protections root rootPosition maximum .Read support.contains)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree initial protections).topology)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections) :
    let result := tree.performWildcardAccessAt initial root maximum .Read protections true
    result.status = .Completed ∧ ReadFrame initial result.location ∧
    Snapshot tree result.location protections root rootPosition maximum .Read support.contains ∧
    PointwiseReadFrame tree protections initial result.location ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
    (∀ query, ¬support.contains query → result.location.perms.get query = initial.perms.get query) := by
  let weights := GeneralBorrowWildcardForestWeights.of_forest tree initial protections forest
  have actual := GeneralBorrowSnapshotReadDFS.access_plan_frame tree initial protections root rootPosition maximum
    weights (GeneralBorrowWildcardForestWeights.bounded tree initial protections forest root) support snapshot depth coherent
    (plan tree initial protections root rootPosition maximum virtual)
  have virtualEq : (rootPosition != 0) = true := by simp [virtual]
  simpa only [virtualEq] using actual

/-- S01 residual authorization supplies actual outside-support framing. -/
theorem of_authorization_frame (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag) (virtual : rootPosition ≠ 0)
    (support : UniIndex → Prop)
    (authorization : DuplicatePrefixResidualSupportAuthorization.Authorization tree initial protections root rootPosition maximum .Read support)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree initial protections).topology)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (short : tree.nodes.size < 65536) :
    let result := tree.performWildcardAccessAt initial root maximum .Read protections true
    result.status = .Completed ∧ ReadFrame initial result.location ∧
    Snapshot tree result.location protections root rootPosition maximum .Read support ∧
    PointwiseReadFrame tree protections initial result.location ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
    (∀ query, ¬support query → result.location.perms.get query = initial.perms.get query) :=
  access_frame tree initial protections root rootPosition maximum virtual
    (GeneralBorrowWildcardControlStack.Support.of_authorization tree initial protections root rootPosition maximum .Read support authorization)
    (DuplicatePrefixResidualInitialSnapshot.snapshot tree initial protections root rootPosition maximum .Read support authorization coherent short)
    depth forest coherent


/-- Runtime SIFA, possible states and every vacant optional slot survive the actual visitor. -/
theorem access_runtime (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag) (virtual : rootPosition ≠ 0)
    (support : GeneralBorrowWildcardControlStack.Support tree root)
    (snapshot : Snapshot tree initial protections root rootPosition maximum .Read support.contains)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree initial protections).topology)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial) :
    let result := tree.performWildcardAccessAt initial root maximum .Read protections true
    result.status = .Completed ∧ ReadFrame initial result.location ∧
    Snapshot tree result.location protections root rootPosition maximum .Read support.contains ∧
    PointwiseReadFrame tree protections initial result.location ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
    (∀ query, ¬support.contains query → result.location.perms.get query = initial.perms.get query) ∧
    GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
    (∀ query, tree.nodes.get query = none → result.location.perms.get query = initial.perms.get query) := by
  let weights := GeneralBorrowWildcardForestWeights.of_forest tree initial protections forest
  have actual := GeneralBorrowSnapshotReadDFS.access_plan_runtime tree initial protections root rootPosition maximum
    weights (GeneralBorrowWildcardForestWeights.bounded tree initial protections forest root) support snapshot depth coherent
    (plan tree initial protections root rootPosition maximum virtual) profile possible
  have virtualEq : (rootPosition != 0) = true := by simp [virtual]
  simpa only [virtualEq] using actual


theorem of_authorization_runtime (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag) (virtual : rootPosition ≠ 0)
    (support : UniIndex → Prop)
    (authorization : DuplicatePrefixResidualSupportAuthorization.Authorization tree initial protections root rootPosition maximum .Read support)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree initial protections).topology)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (short : tree.nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial) :
    let result := tree.performWildcardAccessAt initial root maximum .Read protections true
    result.status = .Completed ∧ ReadFrame initial result.location ∧
    Snapshot tree result.location protections root rootPosition maximum .Read support ∧
    PointwiseReadFrame tree protections initial result.location ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
    (∀ query, ¬support query → result.location.perms.get query = initial.perms.get query) ∧
    GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
    (∀ query, tree.nodes.get query = none → result.location.perms.get query = initial.perms.get query) :=
  access_runtime tree initial protections root rootPosition maximum virtual
    (GeneralBorrowWildcardControlStack.Support.of_authorization tree initial protections root rootPosition maximum .Read support authorization)
    (DuplicatePrefixResidualInitialSnapshot.snapshot tree initial protections root rootPosition maximum .Read support authorization coherent short)
    depth forest coherent profile possible


/-- Actual Read completion also constructs a legal Write contribution-removal
model and preserves the permission origin of every surviving Write supporter. -/
theorem access_effects (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag) (virtual : rootPosition ≠ 0)
    (support : GeneralBorrowWildcardControlStack.Support tree root)
    (snapshot : Snapshot tree initial protections root rootPosition maximum .Read support.contains)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree initial protections).topology)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial)
    (short : tree.nodes.size < 65536) :
    let result := tree.performWildcardAccessAt initial root maximum .Read protections true
    result.status = .Completed ∧ ReadFrame initial result.location ∧
    Snapshot tree result.location protections root rootPosition maximum .Read support.contains ∧
    PointwiseReadFrame tree protections initial result.location ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
    (∀ query, ¬support.contains query → result.location.perms.get query = initial.perms.get query) ∧
    GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
    (∀ query, tree.nodes.get query = none → result.location.perms.get query = initial.perms.get query) ∧
    GeneralBorrowSnapshotReadWriteEffects.Effects tree initial result.location protections maximum := by
  let weights := GeneralBorrowWildcardForestWeights.of_forest tree initial protections forest
  have actual := GeneralBorrowSnapshotReadDFS.access_plan_effects tree initial protections root rootPosition maximum
    weights (GeneralBorrowWildcardForestWeights.bounded tree initial protections forest root) support snapshot depth coherent
    (plan tree initial protections root rootPosition maximum virtual) profile possible short
  have virtualEq : (rootPosition != 0) = true := by simp [virtual]
  simpa only [virtualEq] using actual



theorem of_authorization_effects (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag) (virtual : rootPosition ≠ 0)
    (support : UniIndex → Prop)
    (authorization : DuplicatePrefixResidualSupportAuthorization.Authorization tree initial protections root rootPosition maximum .Read support)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree initial protections).topology)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (short : tree.nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial) :
    let result := tree.performWildcardAccessAt initial root maximum .Read protections true
    result.status = .Completed ∧ ReadFrame initial result.location ∧
    Snapshot tree result.location protections root rootPosition maximum .Read support ∧
    PointwiseReadFrame tree protections initial result.location ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
    (∀ query, ¬support query → result.location.perms.get query = initial.perms.get query) ∧
    GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
    (∀ query, tree.nodes.get query = none → result.location.perms.get query = initial.perms.get query) ∧
    GeneralBorrowSnapshotReadWriteEffects.Effects tree initial result.location protections maximum :=
  access_effects tree initial protections root rootPosition maximum virtual
    (GeneralBorrowWildcardControlStack.Support.of_authorization tree initial protections root rootPosition maximum .Read support authorization)
    (DuplicatePrefixResidualInitialSnapshot.snapshot tree initial protections root rootPosition maximum .Read support authorization coherent short)
    depth forest coherent profile possible short


/-- Actual Read also transports the global finite Write scalar authorization
table, initialized by reflexivity; no initial Write authorization is assumed. -/
theorem access_transfer (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag) (virtual : rootPosition ≠ 0)
    (support : GeneralBorrowWildcardControlStack.Support tree root)
    (snapshot : Snapshot tree initial protections root rootPosition maximum .Read support.contains)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree initial protections).topology)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial)
    (short : tree.nodes.size < 65536) :
    let result := tree.performWildcardAccessAt initial root maximum .Read protections true
    result.status = .Completed ∧ ReadFrame initial result.location ∧
    Snapshot tree result.location protections root rootPosition maximum .Read support.contains ∧
    PointwiseReadFrame tree protections initial result.location ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
    (∀ query, ¬support.contains query → result.location.perms.get query = initial.perms.get query) ∧
    GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
    (∀ query, tree.nodes.get query = none → result.location.perms.get query = initial.perms.get query) ∧
    GeneralBorrowSnapshotReadWriteEffects.Effects tree initial result.location protections maximum ∧
    GeneralBorrowSnapshotReadTransfer.Global tree initial result.location protections root rootPosition maximum support.contains := by
  let weights := GeneralBorrowWildcardForestWeights.of_forest tree initial protections forest
  have actual := GeneralBorrowSnapshotReadDFS.access_plan_transfer tree initial protections root rootPosition maximum
    weights (GeneralBorrowWildcardForestWeights.bounded tree initial protections forest root) support snapshot depth coherent
    (plan tree initial protections root rootPosition maximum virtual) profile possible short
  have virtualEq : (rootPosition != 0) = true := by simp [virtual]
  simpa only [virtualEq] using actual




theorem of_authorization_transfer (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag) (virtual : rootPosition ≠ 0)
    (support : UniIndex → Prop)
    (authorization : DuplicatePrefixResidualSupportAuthorization.Authorization tree initial protections root rootPosition maximum .Read support)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree initial protections).topology)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (short : tree.nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial) :
    let result := tree.performWildcardAccessAt initial root maximum .Read protections true
    result.status = .Completed ∧ ReadFrame initial result.location ∧
    Snapshot tree result.location protections root rootPosition maximum .Read support ∧
    PointwiseReadFrame tree protections initial result.location ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
    (∀ query, ¬support query → result.location.perms.get query = initial.perms.get query) ∧
    GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
    (∀ query, tree.nodes.get query = none → result.location.perms.get query = initial.perms.get query) ∧
    GeneralBorrowSnapshotReadWriteEffects.Effects tree initial result.location protections maximum ∧
    GeneralBorrowSnapshotReadTransfer.Global tree initial result.location protections root rootPosition maximum support :=
  access_transfer tree initial protections root rootPosition maximum virtual
    (GeneralBorrowWildcardControlStack.Support.of_authorization tree initial protections root rootPosition maximum .Read support authorization)
    (DuplicatePrefixResidualInitialSnapshot.snapshot tree initial protections root rootPosition maximum .Read support authorization coherent short)
    depth forest coherent profile possible short

end DuplicatePrefix.GeneralBorrowSnapshotVirtualReadAccess
