import duplicate_prefix.S05CompletedAncestryReadQueries
import duplicate_prefix.CompletedBorrowPhysicalSource

/-! Initial wildcard Read queries with the ACTUAL absent maximum, at EVERY
physical root. One exposed chosen origin and one completed ancestry determine
all scalar demands. No concrete-source root skip or cutoff is substituted.
This remains a sufficient current model, not ordinary-input admission. -/
namespace DuplicatePrefix.S05WildcardCompletedReadQueries
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowExposedNonleafPrimaryPath
open GeneralBorrowWildcardParentTagOrder GeneralBorrowExposureCardinality
open DuplicatePrefixResidualSupportAuthorization DuplicatePrefixCallbackAuthorization
open OrdinaryBorrowAuthority
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 65536

/-- Wildcard pointer binding names one actual exposed grant, not a source
chosen separately for each byte or root. -/
theorem binds_exposed (allocation : Allocation Provenance BorrowTree) (pointer : PointerInstance)
    (binding : PointerBinds allocation pointer) (wildcard : pointer.value.provenance = .wildcard) :
    ∃ node, allocation.extra.nodes.get pointer.grant = some node ∧ node.isExposed = true := by
  obtain ⟨node,present,mapped,bound⟩ := binding
  exact ⟨node,present,by simpa only [wildcard] using bound⟩

private theorem local_support (state : LocationState) (held : Bool)
    (right : LocalWrite state held) :
    (state.permission.strongestAllowedLocalAccess held).allows .Read = true := by
  cases permission : state.permission with
  | ReservedFrz conflicted =>
    cases conflicted <;> cases held <;>
      simp_all [LocalWrite,Permission.strongestAllowedLocalAccess,WildcardAccessLevel.allows]
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
    cases held <;> simp_all [LocalWrite,Permission.strongestAllowedLocalAccess,WildcardAccessLevel.allows]

/-- The chosen physical component uses the actually exposed chosen grant;
other components use the completion's exposed attachment origin. -/
theorem origin_root (tree : BorrowTree) (completion : Completion)
    (initial : LocationTree) (protections : ProtectedTags)
    (complete : Completes tree completion) (order : ParentTagOrder tree)
    (rootPosition selectedPosition : Nat) (root selectedRoot source query : UniIndex)
    (node selectedNode sourceNode : TreeNode)
    (rootSlot : tree.roots[rootPosition]? = some root)
    (selectedSlot : tree.roots[selectedPosition]? = some selectedRoot)
    (selectedPresent : tree.nodes.get selectedRoot = some selectedNode)
    (sourcePresent : tree.nodes.get source = some sourceNode) (exposed : sourceNode.isExposed = true)
    (selectedPath : Path tree selectedRoot source) (queryPath : Path tree root query)
    (present : tree.nodes.get query = some node)
    (localRights : ∀ index found, tree.nodes.get index = some found →
      Below completion index source → LocalWrite (RawState initial index found) (protections.contains found.tag))
    (below : Below completion query source) :
    ∃ witness witnessNode, tree.nodes.get witness = some witnessNode ∧
      Supports initial protections witness witnessNode none .Read ∧
      Path tree query witness ∧ Below completion witness source := by
  by_cases same : root = selectedRoot
  · subst root
    obtain ⟨actual,found,parentless⟩ := complete.2.2.2.1 selectedPosition selectedRoot selectedSlot
    have nodeEq : actual = selectedNode := Option.some.inj (found.symm.trans selectedPresent)
    subst actual
    have path := CompletedBorrowPhysicalSource.same_root_ancestor complete selectedPresent parentless present queryPath selectedPath below
    exact ⟨source,sourceNode,sourcePresent,⟨exposed,local_support _ _ (localRights source sourceNode sourcePresent (.refl source)),by simp⟩,
      path,.refl source⟩
  · obtain ⟨witness,witnessNode,found,eligible,path,ancestor⟩ :=
      S05CompletedAncestryReadQueries.origin_root tree completion initial protections complete order
        rootPosition selectedPosition root selectedRoot source query node selectedNode rootSlot selectedSlot
        selectedPresent same selectedPath queryPath present (fun index found present _ below => localRights index found present below) below
    exact ⟨witness,witnessNode,found,⟨eligible.1,eligible.2.1,by simp⟩,path,ancestor⟩

theorem query_shape (tree : BorrowTree) (completion : Completion)
    (initial : LocationTree) (protections : ProtectedTags)
    (complete : Completes tree completion)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (rootPosition selectedPosition : Nat) (root selectedRoot source query : UniIndex)
    (node selectedNode sourceNode : TreeNode)
    (rootSlot : tree.roots[rootPosition]? = some root)
    (selectedSlot : tree.roots[selectedPosition]? = some selectedRoot)
    (selectedPresent : tree.nodes.get selectedRoot = some selectedNode)
    (sourcePresent : tree.nodes.get source = some sourceNode) (exposed : sourceNode.isExposed = true)
    (selectedPath : Path tree selectedRoot source) (queryPath : Path tree root query)
    (present : tree.nodes.get query = some node)
    (localRights : ∀ index found, tree.nodes.get index = some found →
      Below completion index source → LocalWrite (RawState initial index found) (protections.contains found.tag)) :
    let classification := residualRelation tree initial protections root query node none .Read rootPosition []
    (Below completion query source → classification = some .LocalAccess ∨ classification = some .EitherAccess) ∧
      (¬Below completion query source → classification = some .ForeignAccess ∨ classification = some .EitherAccess) := by
  dsimp only
  have covered := GeneralBorrowSharedAuthorizationGeometry.covers_of_path tree depth root query queryPath
  have eligibleOrigin := origin_root tree completion initial protections complete order rootPosition selectedPosition
    root selectedRoot source query node selectedNode sourceNode rootSlot selectedSlot selectedPresent sourcePresent exposed selectedPath queryPath present localRights
  obtain ⟨rootNode,rootPresent,_⟩ := complete.2.2.2.1 rootPosition root rootSlot
  have primary : rootPosition = 0 → ∃ witness witnessNode,
      tree.nodes.get witness = some witnessNode ∧
      Supports initial protections witness witnessNode none .Read ∧
      Path tree root witness ∧ Below completion witness source := by
    intro zero
    exact origin_root tree completion initial protections complete order rootPosition selectedPosition
      root selectedRoot source root rootNode selectedNode sourceNode rootSlot selectedSlot selectedPresent sourcePresent exposed selectedPath
      (.refl root rootNode rootPresent) rootPresent localRights
      (CompletedBorrowAncestry.root_zero_below complete (by simpa only [zero] using rootSlot) selectedSlot selectedPath)
  have positive : 0 < residualCount tree initial protections .Read [] root +
      if rootPosition != 0 then 1 else 0 := by
    by_cases zero : rootPosition = 0
    · obtain ⟨witness,witnessNode,lookup,eligible,path,_⟩ := primary zero
      have positive := GeneralBorrowResidualPrimaryWitness.positive tree initial protections depth
        none .Read [] (empty_removal _ _ _ _ _) root witness witnessNode lookup eligible path
      simpa [zero] using positive
    · simp only [show (rootPosition != 0) = true by simp [zero],ite_true]
      omega
  have nonzero : ((residualCount tree initial protections .Read [] root +
      if rootPosition != 0 then 1 else 0) == 0) = false := by
    apply Bool.eq_false_iff.mpr
    intro equal
    exact (Nat.ne_of_gt positive) (beq_iff_eq.mp equal)
  constructor
  · intro below
    obtain ⟨witness,witnessNode,lookup,eligible,path,_⟩ := eligibleOrigin below
    have localPositive := GeneralBorrowResidualPrimaryWitness.positive tree initial protections depth
      none .Read [] (empty_removal _ _ _ _ _) query witness witnessNode lookup eligible path
    have localNonzero : (residualCount tree initial protections .Read [] query == 0) = false := by simp [Nat.ne_of_gt localPositive]
    have unclamped := path_not_above tree order initial protections none .Read
      query witness node witnessNode present lookup path eligible
    by_cases equal : residualCount tree initial protections .Read [] root +
        (if rootPosition != 0 then 1 else 0) = residualCount tree initial protections .Read [] query
    · have equalBool : ((residualCount tree initial protections .Read [] root +
          if rootPosition != 0 then 1 else 0) == residualCount tree initial protections .Read [] query) = true := beq_iff_eq.mpr equal
      simp only [residualRelation,unclamped,classify,nonzero,equalBool,Bool.false_eq_true,↓reduceIte]
      simp
    · have equalBool : ((residualCount tree initial protections .Read [] root +
          if rootPosition != 0 then 1 else 0) == residualCount tree initial protections .Read [] query) = false := by
        apply Bool.eq_false_iff.mpr
        intro same
        exact equal (beq_iff_eq.mp same)
      simp only [residualRelation,unclamped,classify,nonzero,localNonzero,equalBool,Bool.false_eq_true,↓reduceIte]
      simp
  · intro below
    have unequal : residualCount tree initial protections .Read [] root +
        (if rootPosition != 0 then 1 else 0) ≠ residualCount tree initial protections .Read [] query := by
      intro equal
      by_cases zero : rootPosition = 0
      · obtain ⟨witness,witnessNode,lookup,eligible,path,witnessBelow⟩ := primary zero
        have outside : query ∉ GeneralBorrowExposureAncestorFold.walk tree.nodes (tree.nodes.size+1) witness := by
          intro member
          have physical := S05RawGrantAuthorizationClosure.path_of_walk tree depth _ query witness witnessNode lookup member
          exact below (CompletedBorrowAncestry.below_trans (CompletedBorrowAncestry.physical_below complete physical) witnessBelow)
        have strict := S05CutoffOwnershipGeometry.residual_strict tree initial protections depth root query witness
          witnessNode lookup none .Read [] (empty_removal _ _ _ _ _) eligible path outside covered
        simp only [zero,bne_self_eq_false,Bool.false_eq_true,ite_false,Nat.add_zero] at equal
        omega
      · have bounded : residualCount tree initial protections .Read [] query ≤ residualCount tree initial protections .Read [] root := by
          rw [residual_empty,residual_empty]
          exact GeneralBorrowExposureCardinality.cardinality_dominates _ _ _ _ .Read covered
        have virtual : (rootPosition != 0) = true := by simp [zero]
        simp only [virtual,ite_true] at equal
        omega
    have unequalBool : ((residualCount tree initial protections .Read [] root +
        if rootPosition != 0 then 1 else 0) == residualCount tree initial protections .Read [] query) = false := by
      apply Bool.eq_false_iff.mpr
      intro same
      exact unequal (beq_iff_eq.mp same)
    simp only [residualRelation,classify,nonzero,unequalBool,Bool.false_eq_true,↓reduceIte]
    cases aboveMaximum node none <;>
      cases zero : (residualCount tree initial protections .Read [] query == 0) <;>
      simp only [Bool.false_eq_true,↓reduceIte]
    all_goals simp

section Access
variable (tree : BorrowTree) (completion : Completion) (initial : LocationTree) (protections : ProtectedTags)
variable (complete : Completes tree completion)
variable (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
variable (rootPosition selectedPosition : Nat) (root selectedRoot source : UniIndex) (selectedNode sourceNode : TreeNode)
variable (rootSlot : tree.roots[rootPosition]? = some root)
variable (selectedSlot : tree.roots[selectedPosition]? = some selectedRoot)
variable (selectedPresent : tree.nodes.get selectedRoot = some selectedNode)
variable (sourcePresent : tree.nodes.get source = some sourceNode) (exposed : sourceNode.isExposed = true)
variable (selectedPath : Path tree selectedRoot source)
variable (localRights : ∀ index node, tree.nodes.get index = some node →
  Below completion index source → LocalWrite (RawState initial index node) (protections.contains node.tag))
variable (foreignRights : ∀ index node, tree.nodes.get index = some node →
  ¬Below completion index source → ForeignWrite (RawState initial index node) (protections.contains node.tag))

include complete depth order rootSlot selectedSlot selectedPresent sourcePresent exposed selectedPath localRights foreignRights in
/-- Exact same-query Read authorization, with the actual absent cutoff. -/
theorem authorized_root (query : UniIndex) (node : TreeNode) (path : Path tree root query)
    (present : tree.nodes.get query = some node) :
    let classification := residualRelation tree initial protections root query node none .Read rootPosition []
    DuplicatePrefixCallbackVisitAuthorization.Authorized (RawState initial query node) .Read
      (protections.contains node.tag) classification classification := by
  dsimp only
  apply (DuplicatePrefixResidualInitialSnapshot.same_query_iff _ _ _ _).mpr
  have shape := query_shape tree completion initial protections complete depth order rootPosition selectedPosition
    root selectedRoot source query node selectedNode sourceNode rootSlot selectedSlot selectedPresent sourcePresent exposed
    selectedPath path present localRights
  by_cases below : Below completion query source
  · have raw := localRights query node present below
    rcases shape.1 below with localQuery | eitherQuery
    · rw [localQuery]
      exact ⟨raw.1,Or.inr (OrdinaryBorrowAuthorityBridge.local_scalar _ _ raw .Read)⟩
    · rw [eitherQuery]
      exact raw.1
  · have raw := foreignRights query node present below
    rcases shape.2 below with foreignQuery | eitherQuery
    · rw [foreignQuery]
      exact ⟨raw.1,Or.inr (S05CompletedAncestryReadQueries.foreign_read _ _ raw)⟩
    · rw [eitherQuery]
      exact raw.1

include complete depth order rootSlot selectedSlot selectedPresent sourcePresent exposed selectedPath localRights foreignRights in
/-- Read-mask geometry is derived for all physical roots, including the chosen
source's own component. No root is skipped and no callback result is assumed. -/
theorem authorization_root : Authorization tree initial protections root rootPosition none .Read (Path tree root) := by
  let area := S05CompletedAncestryReadQueries.support tree completion complete rootPosition root rootSlot
  refine ⟨area.rooted,area.present,area.children,?_,?_,?_,?_⟩
  · intro query path
    exact GeneralBorrowSharedAuthorizationGeometry.covers_of_path tree depth root query path
  · intro query node path present
    by_cases below : Below completion query source
    · exact (localRights query node present below).1
    · exact (foreignRights query node present below).1
  · intro before after legalBefore legalAfter _ query node path present _
    have beforeEmpty := read_removal_empty tree initial protections none before legalBefore
    have afterEmpty := read_removal_empty tree initial protections none after legalAfter
    subst before
    subst after
    exact authorized_root tree completion initial protections complete depth order rootPosition selectedPosition
      root selectedRoot source selectedNode sourceNode rootSlot selectedSlot selectedPresent sourcePresent exposed
      selectedPath localRights foreignRights query node path present
  · intro zero
    obtain ⟨rootNode,rootPresent,_⟩ := complete.2.2.2.1 rootPosition root rootSlot
    have below := CompletedBorrowAncestry.root_zero_below complete
      (by simpa only [zero] using rootSlot) selectedSlot selectedPath
    obtain ⟨witness,node,present,eligible,path,_⟩ := origin_root tree completion initial protections complete order
      rootPosition selectedPosition root selectedRoot source root rootNode selectedNode sourceNode rootSlot selectedSlot
      selectedPresent sourcePresent exposed selectedPath (.refl root rootNode rootPresent) rootPresent localRights below
    exact ⟨witness,node,path,present,eligible⟩

include complete depth order rootSlot selectedSlot selectedPresent sourcePresent exposed selectedPath localRights foreignRights in
/-- The actual production wildcard Read DFS at any current physical root
completes with maximum NONE. This is one callback, not the whole root scan. -/
theorem access_root_information
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (coherent : LocationCoherent tree initial protections) (short : tree.nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial) :
    let result := tree.performWildcardAccessAt initial root none .Read protections (rootPosition != 0)
    result.status = .Completed ∧
      GeneralBorrowExposedNonleafState.ReadFrame initial result.location ∧
      LocationCoherent tree result.location protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
      S05SemanticReadEffects.Effects tree initial result.location protections ∧
      (∀ query, ¬Path tree root query → result.location.perms.get query = initial.perms.get query) ∧
      GeneralBorrowWildcardPrimaryReadWitness.PointwiseReadFrame tree protections initial result.location ∧
      GeneralBorrowSnapshotReadTransfer.Global tree initial result.location protections root rootPosition none (Path tree root) := by
  have auth := authorization_root tree completion initial protections complete depth order rootPosition selectedPosition
    root selectedRoot source selectedNode sourceNode rootSlot selectedSlot selectedPresent sourcePresent exposed
    selectedPath localRights foreignRights
  let area := S05CompletedAncestryReadQueries.support tree completion complete rootPosition root rootSlot
  have snapshot := DuplicatePrefixResidualInitialSnapshot.snapshot tree initial protections root rootPosition
    none .Read (Path tree root) auth coherent short
  obtain ⟨forest⟩ := formed.forest initial protections
  have graph := GeneralBorrowExposedScopedReciprocal.of_forest tree initial protections forest depth
  have plans : Nonempty (GeneralBorrowSnapshotReadDFSPlan.WitnessPlan tree initial protections root rootPosition none) := by
    by_cases zero : rootPosition = 0
    · subst rootPosition
      exact GeneralBorrowSnapshotOrderedPrimaryReadPlan.of_authorization tree initial protections root
        none (Path tree root) order depth graph coherent short auth
    · exact ⟨GeneralBorrowSnapshotVirtualReadAccess.plan tree initial protections root rootPosition none zero⟩
  obtain ⟨plan⟩ := plans
  let weights := GeneralBorrowWildcardForestWeights.of_forest tree initial protections forest
  have bound := GeneralBorrowWildcardForestWeights.bounded tree initial protections forest root
  obtain ⟨done,frame,_,pointwise,afterCoherent,outside,runtime,_,transfer,effects⟩ :=
    S05SemanticReadDFS.access true false tree initial protections root rootPosition none
      weights bound area snapshot depth coherent plan (fun _ => ⟨profile,possible⟩) (by simp)
  exact ⟨done,frame,afterCoherent,(runtime rfl).1,(runtime rfl).2,effects,outside,pointwise,transfer⟩
end Access

end DuplicatePrefix.S05WildcardCompletedReadQueries

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05WildcardCompletedReadQueries." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved wildcard completed Read dependency {dependency}"
