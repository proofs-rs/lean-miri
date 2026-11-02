import duplicate_prefix.S05ReadRawAuthorityEndpoint
import duplicate_prefix.S05CompletedAncestryAuthorization
import duplicate_prefix.S05CutoffOwnershipGeometry
import duplicate_prefix.S05SemanticReadDFS
import duplicate_prefix.GeneralBorrowSnapshotOrderedPrimaryReadPlan
import duplicate_prefix.GeneralBorrowSnapshotVirtualReadAccess

/-! Read-only callback authority from the unadopted completed-ancestry model.
The selected physical source fixes the cutoff. This is a sufficient component
theorem, not ordinary-input coverage or formation of the completion model. -/
namespace DuplicatePrefix.S05CompletedAncestryReadQueries
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowExposedNonleafPrimaryPath
open GeneralBorrowWildcardParentTagOrder GeneralBorrowExposureCardinality
open DuplicatePrefixResidualSupportAuthorization DuplicatePrefixCallbackAuthorization
open OrdinaryBorrowAuthority
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 65536

theorem foreign_read (state : LocationState) (held : Bool)
    (right : ForeignWrite state held) :
    DuplicatePrefixScalarAuthorization.Compatible state .Read .ForeignAccess held := by
  apply OrdinaryBorrowAuthorityBridge.foreign_scalar state held right.1
  · intro active
    rcases right.2 active with cell | dormant
    · simp [cell]
    · exact dormant.1
  · intro active disabled
    rcases right.2 active with cell | dormant
    · simp [disabled] at cell
    · exact dormant.2
  · intro _
    exact right

private theorem local_support (state : LocationState) (held : Bool)
    (right : LocalWrite state held) :
    (state.permission.strongestAllowedLocalAccess held).allows .Read = true := by
  cases permission : state.permission with
  | ReservedFrz conflicted =>
    cases conflicted <;> cases held <;>
      simp_all [LocalWrite,Permission.strongestAllowedLocalAccess,WildcardAccessLevel.allows]
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
    cases held <;> simp_all [LocalWrite,Permission.strongestAllowedLocalAccess,WildcardAccessLevel.allows]

/-- The completion graph supplies a real cutoff-eligible Read origin below
each completed ancestor in a different physical root. -/
theorem origin_root (tree : BorrowTree) (completion : Completion)
    (initial : LocationTree) (protections : ProtectedTags)
    (complete : Completes tree completion) (order : ParentTagOrder tree)
    (rootPosition selectedPosition : Nat) (root selectedRoot source query : UniIndex)
    (node selectedNode : TreeNode)
    (rootSlot : tree.roots[rootPosition]? = some root)
    (selectedSlot : tree.roots[selectedPosition]? = some selectedRoot)
    (selectedPresent : tree.nodes.get selectedRoot = some selectedNode)
    (different : root ≠ selectedRoot)
    (selectedPath : Path tree selectedRoot source) (queryPath : Path tree root query)
    (present : tree.nodes.get query = some node)
    (localRights : ∀ index found, tree.nodes.get index = some found → Path tree root index →
      Below completion index source → LocalWrite
        ((initial.perms.get index).getD found.defaultLocationState) (protections.contains found.tag))
    (below : Below completion query source) :
    ∃ witness witnessNode, tree.nodes.get witness = some witnessNode ∧
      Supports initial protections witness witnessNode (some selectedNode.tag) .Read ∧
      Path tree query witness ∧ Below completion witness source := by
  obtain ⟨rootNode,rootPresent,rootParentless⟩ := complete.2.2.2.1 rootPosition root rootSlot
  obtain ⟨selected,selectedFound,selectedParentless⟩ := complete.2.2.2.1 selectedPosition selectedRoot selectedSlot
  have same : selected = selectedNode := Option.some.inj (selectedFound.symm.trans selectedPresent)
  subst selected
  obtain ⟨witness,witnessNode,witnessPresent,exposed,witnessPath,_,witnessBelow,bound⟩ :=
    CompletedBorrowAncestry.cross_root_origin complete order rootPresent rootParentless selectedPresent
      selectedParentless present different queryPath selectedPath below
  refine ⟨witness,witnessNode,witnessPresent,⟨exposed,?_,?_⟩,witnessPath,witnessBelow⟩
  · exact local_support _ _ (localRights witness witnessNode witnessPresent (CompletedBorrowAncestry.path_trans queryPath witnessPath) witnessBelow)
  · simpa only [Option.isNone_some,Option.any_some,Bool.false_or,decide_eq_true_eq] using bound

/-- Read masks are empty, so entry and postchildren queries coincide. Exact
recording safety follows from this same-query authorization in the existing
visitor; no arbitrary-entry Write claim is used. -/
theorem query_shape (tree : BorrowTree) (completion : Completion)
    (initial : LocationTree) (protections : ProtectedTags)
    (complete : Completes tree completion)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (rootPosition selectedPosition : Nat) (root selectedRoot source query : UniIndex)
    (node selectedNode : TreeNode)
    (rootSlot : tree.roots[rootPosition]? = some root)
    (selectedSlot : tree.roots[selectedPosition]? = some selectedRoot)
    (selectedPresent : tree.nodes.get selectedRoot = some selectedNode)
    (different : root ≠ selectedRoot)
    (selectedPath : Path tree selectedRoot source) (queryPath : Path tree root query)
    (present : tree.nodes.get query = some node)
    (localRights : ∀ index found, tree.nodes.get index = some found → Path tree root index →
      Below completion index source → LocalWrite
        ((initial.perms.get index).getD found.defaultLocationState) (protections.contains found.tag)) :
    let classification := residualRelation tree initial protections root query node (some selectedNode.tag) .Read rootPosition []
    (Below completion query source → classification = some .LocalAccess ∨ classification = some .EitherAccess) ∧
      (¬Below completion query source → classification = some .ForeignAccess ∨ classification = some .EitherAccess) := by
  dsimp only
  have covered := GeneralBorrowSharedAuthorizationGeometry.covers_of_path tree depth root query queryPath
  have eligibleOrigin := origin_root tree completion initial protections complete order rootPosition selectedPosition
    root selectedRoot source query node selectedNode rootSlot selectedSlot selectedPresent different selectedPath queryPath present localRights
  obtain ⟨rootNode,rootPresent,_⟩ := complete.2.2.2.1 rootPosition root rootSlot
  have primary : rootPosition = 0 → ∃ witness witnessNode,
      tree.nodes.get witness = some witnessNode ∧
      Supports initial protections witness witnessNode (some selectedNode.tag) .Read ∧
      Path tree root witness ∧ Below completion witness source := by
    intro zero
    exact origin_root tree completion initial protections complete order rootPosition selectedPosition
      root selectedRoot source root rootNode selectedNode rootSlot selectedSlot selectedPresent different selectedPath
      (.refl root rootNode rootPresent) rootPresent localRights
      (CompletedBorrowAncestry.root_zero_below complete (by simpa only [zero] using rootSlot) selectedSlot selectedPath)
  have positive : 0 < residualCount tree initial protections .Read [] root +
      if rootPosition != 0 then 1 else 0 := by
    by_cases zero : rootPosition = 0
    · obtain ⟨witness,witnessNode,lookup,eligible,path,_⟩ := primary zero
      have positive := GeneralBorrowResidualPrimaryWitness.positive tree initial protections depth
        (some selectedNode.tag) .Read [] (empty_removal _ _ _ _ _) root witness witnessNode lookup eligible path
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
      (some selectedNode.tag) .Read [] (empty_removal _ _ _ _ _) query witness witnessNode lookup eligible path
    have localNonzero : (residualCount tree initial protections .Read [] query == 0) = false := by simp [Nat.ne_of_gt localPositive]
    have unclamped := path_not_above tree order initial protections (some selectedNode.tag) .Read
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
          witnessNode lookup (some selectedNode.tag) .Read [] (empty_removal _ _ _ _ _) eligible path outside covered
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
    cases aboveMaximum node (some selectedNode.tag) <;>
      cases zero : (residualCount tree initial protections .Read [] query == 0) <;>
      simp only [Bool.false_eq_true,↓reduceIte]
    all_goals simp

/-- Read same-query authorization from completed source classification. -/
theorem authorized_root (tree : BorrowTree) (completion : Completion)
    (initial : LocationTree) (protections : ProtectedTags)
    (complete : Completes tree completion)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (rootPosition selectedPosition : Nat) (root selectedRoot source query : UniIndex)
    (node selectedNode : TreeNode)
    (rootSlot : tree.roots[rootPosition]? = some root)
    (selectedSlot : tree.roots[selectedPosition]? = some selectedRoot)
    (selectedPresent : tree.nodes.get selectedRoot = some selectedNode)
    (different : root ≠ selectedRoot)
    (selectedPath : Path tree selectedRoot source) (queryPath : Path tree root query)
    (present : tree.nodes.get query = some node)
    (localRights : ∀ index found, tree.nodes.get index = some found → Path tree root index →
      Below completion index source → LocalWrite
        ((initial.perms.get index).getD found.defaultLocationState) (protections.contains found.tag))
    (foreignRights : ∀ index found, tree.nodes.get index = some found → Path tree root index →
      ¬ Below completion index source → ForeignWrite
        ((initial.perms.get index).getD found.defaultLocationState) (protections.contains found.tag)) :
    let classification := residualRelation tree initial protections root query node (some selectedNode.tag) .Read rootPosition []
    DuplicatePrefixCallbackVisitAuthorization.Authorized
      ((initial.perms.get query).getD node.defaultLocationState) .Read (protections.contains node.tag) classification classification := by
  dsimp only
  apply (DuplicatePrefixResidualInitialSnapshot.same_query_iff _ _ _ _).mpr
  have shape := query_shape tree completion initial protections complete depth order rootPosition selectedPosition
    root selectedRoot source query node selectedNode rootSlot selectedSlot selectedPresent different selectedPath
    queryPath present localRights
  by_cases below : Below completion query source
  · have raw := localRights query node present queryPath below
    rcases shape.1 below with localQuery | eitherQuery
    · rw [localQuery]
      exact ⟨raw.1,Or.inr (OrdinaryBorrowAuthorityBridge.local_scalar _ _ raw .Read)⟩
    · rw [eitherQuery]
      exact raw.1
  · have raw := foreignRights query node present queryPath below
    rcases shape.2 below with foreignQuery | eitherQuery
    · rw [foreignQuery]
      exact ⟨raw.1,Or.inr (foreign_read _ _ raw)⟩
    · rw [eitherQuery]
      exact raw.1

/-- Compatibility wrapper for the original global scalar-table API. -/
theorem origin (tree : BorrowTree) (completion : Completion)
    (initial : LocationTree) (protections : ProtectedTags)
    (complete : Completes tree completion) (order : ParentTagOrder tree)
    (rootPosition selectedPosition : Nat) (root selectedRoot source query : UniIndex)
    (node selectedNode : TreeNode)
    (rootSlot : tree.roots[rootPosition]? = some root)
    (selectedSlot : tree.roots[selectedPosition]? = some selectedRoot)
    (selectedPresent : tree.nodes.get selectedRoot = some selectedNode)
    (different : root ≠ selectedRoot)
    (selectedPath : Path tree selectedRoot source) (queryPath : Path tree root query)
    (present : tree.nodes.get query = some node)
    (localRights : ∀ index found, tree.nodes.get index = some found →
      Below completion index source → LocalWrite
        ((initial.perms.get index).getD found.defaultLocationState) (protections.contains found.tag))
    (below : Below completion query source) :
    ∃ witness witnessNode, tree.nodes.get witness = some witnessNode ∧
      Supports initial protections witness witnessNode (some selectedNode.tag) .Read ∧
      Path tree query witness ∧ Below completion witness source := by
  exact origin_root tree completion initial protections complete order rootPosition selectedPosition
    root selectedRoot source query node selectedNode rootSlot selectedSlot selectedPresent different
    selectedPath queryPath present (fun index found present _ below => localRights index found present below) below

/-- Compatibility wrapper for the original global scalar-table API. -/
theorem authorized (tree : BorrowTree) (completion : Completion)
    (initial : LocationTree) (protections : ProtectedTags)
    (complete : Completes tree completion)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (rootPosition selectedPosition : Nat) (root selectedRoot source query : UniIndex)
    (node selectedNode : TreeNode)
    (rootSlot : tree.roots[rootPosition]? = some root)
    (selectedSlot : tree.roots[selectedPosition]? = some selectedRoot)
    (selectedPresent : tree.nodes.get selectedRoot = some selectedNode)
    (different : root ≠ selectedRoot)
    (selectedPath : Path tree selectedRoot source) (queryPath : Path tree root query)
    (present : tree.nodes.get query = some node)
    (localRights : ∀ index found, tree.nodes.get index = some found →
      Below completion index source → LocalWrite
        ((initial.perms.get index).getD found.defaultLocationState) (protections.contains found.tag))
    (foreignRights : ∀ index found, tree.nodes.get index = some found →
      ¬ Below completion index source → ForeignWrite
        ((initial.perms.get index).getD found.defaultLocationState) (protections.contains found.tag)) :
    let classification := residualRelation tree initial protections root query node (some selectedNode.tag) .Read rootPosition []
    DuplicatePrefixCallbackVisitAuthorization.Authorized
      ((initial.perms.get query).getD node.defaultLocationState) .Read (protections.contains node.tag) classification classification := by
  exact authorized_root tree completion initial protections complete depth order rootPosition selectedPosition
    root selectedRoot source query node selectedNode rootSlot selectedSlot selectedPresent different
    selectedPath queryPath present (fun index found present _ below => localRights index found present below)
    (fun index found present _ outside => foreignRights index found present outside)

section Callback
variable (tree : BorrowTree) (completion : Completion) (initial : LocationTree) (protections : ProtectedTags)
variable (complete : Completes tree completion)
variable (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
variable (rootPosition selectedPosition : Nat) (root selectedRoot source : UniIndex) (selectedNode : TreeNode)
variable (rootSlot : tree.roots[rootPosition]? = some root)
variable (selectedSlot : tree.roots[selectedPosition]? = some selectedRoot)
variable (selectedPresent : tree.nodes.get selectedRoot = some selectedNode)
variable (different : root ≠ selectedRoot) (selectedPath : Path tree selectedRoot source)
variable (localRights : ∀ index found, tree.nodes.get index = some found → Path tree root index →
  Below completion index source → LocalWrite
    ((initial.perms.get index).getD found.defaultLocationState) (protections.contains found.tag))
variable (foreignRights : ∀ index found, tree.nodes.get index = some found → Path tree root index →
  ¬ Below completion index source → ForeignWrite
    ((initial.perms.get index).getD found.defaultLocationState) (protections.contains found.tag))

include complete rootSlot in
/-- Canonical physical descendant support has no permission fields. -/
def support : GeneralBorrowWildcardControlStack.Support tree root where
  contains := Path tree root
  rooted := by
    obtain ⟨node,present,_⟩ := complete.2.2.2.1 rootPosition root rootSlot
    exact .refl root node present
  present := fun _ path => path.present
  children := by
    intro index node path present child member
    obtain ⟨childNode,childPresent,edge⟩ := (complete.2.2.2.2.1 index node present).2.1 child |>.mp member
    exact .step path childNode childPresent edge

include complete depth order rootSlot selectedSlot selectedPresent different selectedPath localRights foreignRights in
/-- Completed source-relative raw tables supply a Read-only residual contract.
Both Read masks reduce to the actual empty mask; no legacy Row is required. -/
theorem authorization_root :
    Authorization tree initial protections root rootPosition (some selectedNode.tag) .Read (Path tree root) := by
  let area := support tree completion complete rootPosition root rootSlot
  refine ⟨area.rooted,area.present,area.children,?_,?_,?_,?_⟩
  · intro query path
    exact GeneralBorrowSharedAuthorizationGeometry.covers_of_path tree depth root query path
  · intro query node path present
    by_cases below : Below completion query source
    · exact (localRights query node present path below).1
    · exact (foreignRights query node present path below).1
  · intro before after legalBefore legalAfter _ query node path present _
    have beforeEmpty := read_removal_empty tree initial protections (some selectedNode.tag) before legalBefore
    have afterEmpty := read_removal_empty tree initial protections (some selectedNode.tag) after legalAfter
    subst before
    subst after
    exact authorized_root tree completion initial protections complete depth order rootPosition selectedPosition
      root selectedRoot source query node selectedNode rootSlot selectedSlot selectedPresent different selectedPath
      path present localRights foreignRights
  · intro zero
    obtain ⟨rootNode,rootPresent,_⟩ := complete.2.2.2.1 rootPosition root rootSlot
    have below := CompletedBorrowAncestry.root_zero_below complete
      (by simpa only [zero] using rootSlot) selectedSlot selectedPath
    obtain ⟨witness,node,present,eligible,path,_⟩ := origin_root tree completion initial protections complete order
      rootPosition selectedPosition root selectedRoot source root rootNode selectedNode rootSlot selectedSlot
      selectedPresent different selectedPath (.refl root rootNode rootPresent) rootPresent localRights below
    exact ⟨witness,node,path,present,eligible⟩

include complete depth order rootSlot selectedSlot selectedPresent different selectedPath localRights foreignRights in
/-- The actual production Read callback completes from independent current
source-relative authority and runtime data. Recording and child-first count
stability are discharged by the existing Read DFS, not by Write authorization.
This callback is the Read phase used by concrete FnEntry and reborrows. -/
theorem access_root_information
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (coherent : LocationCoherent tree initial protections) (short : tree.nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial) :
    let result := tree.performWildcardAccessAt initial root (some selectedNode.tag) .Read protections (rootPosition != 0)
    result.status = .Completed ∧
      GeneralBorrowExposedNonleafState.ReadFrame initial result.location ∧
      LocationCoherent tree result.location protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
      S05SemanticReadEffects.Effects tree initial result.location protections ∧
      (∀ query, ¬Path tree root query → result.location.perms.get query = initial.perms.get query) ∧
      GeneralBorrowWildcardPrimaryReadWitness.PointwiseReadFrame tree protections initial result.location ∧
      GeneralBorrowSnapshotReadTransfer.Global tree initial result.location protections root rootPosition
        (some selectedNode.tag) (Path tree root) := by
  have auth := authorization_root tree completion initial protections complete depth order rootPosition selectedPosition
    root selectedRoot source selectedNode rootSlot selectedSlot selectedPresent different selectedPath localRights foreignRights
  let area := support tree completion complete rootPosition root rootSlot
  have snapshot := DuplicatePrefixResidualInitialSnapshot.snapshot tree initial protections root rootPosition
    (some selectedNode.tag) .Read (Path tree root) auth coherent short
  obtain ⟨forest⟩ := formed.forest initial protections
  have graph := GeneralBorrowExposedScopedReciprocal.of_forest tree initial protections forest depth
  have plans : Nonempty (GeneralBorrowSnapshotReadDFSPlan.WitnessPlan tree initial protections root rootPosition (some selectedNode.tag)) := by
    by_cases zero : rootPosition = 0
    · subst rootPosition
      exact GeneralBorrowSnapshotOrderedPrimaryReadPlan.of_authorization tree initial protections root
        (some selectedNode.tag) (Path tree root) order depth graph coherent short auth
    · exact ⟨GeneralBorrowSnapshotVirtualReadAccess.plan tree initial protections root rootPosition (some selectedNode.tag) zero⟩
  obtain ⟨plan⟩ := plans
  let weights := GeneralBorrowWildcardForestWeights.of_forest tree initial protections forest
  have bound := GeneralBorrowWildcardForestWeights.bounded tree initial protections forest root
  obtain ⟨done,frame,_,pointwise,afterCoherent,outside,runtime,_,transfer,effects⟩ :=
    S05SemanticReadDFS.access true false tree initial protections root rootPosition (some selectedNode.tag)
      weights bound area snapshot depth coherent plan (fun _ => ⟨profile,possible⟩) (by simp)
  exact ⟨done,frame,afterCoherent,(runtime rfl).1,(runtime rfl).2,effects,outside,pointwise,transfer⟩

include complete depth order rootSlot selectedSlot selectedPresent different selectedPath localRights foreignRights in
/-- Compatibility projection of the production Read endpoint information. -/
theorem access_root_framed
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (coherent : LocationCoherent tree initial protections) (short : tree.nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial) :
    let result := tree.performWildcardAccessAt initial root (some selectedNode.tag) .Read protections (rootPosition != 0)
    result.status = .Completed ∧
      GeneralBorrowExposedNonleafState.ReadFrame initial result.location ∧
      LocationCoherent tree result.location protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
      S05SemanticReadEffects.Effects tree initial result.location protections ∧
      (∀ query, ¬Path tree root query → result.location.perms.get query = initial.perms.get query) := by
  obtain ⟨done,frame,cache,sifa,gp,effects,outside,_,_⟩ :=
    access_root_information tree completion initial protections complete depth order rootPosition selectedPosition
      root selectedRoot source selectedNode rootSlot selectedSlot selectedPresent different selectedPath
      localRights foreignRights formed coherent short profile possible
  exact ⟨done,frame,cache,sifa,gp,effects,outside⟩

include complete depth order rootSlot selectedSlot selectedPresent different selectedPath localRights foreignRights in
/-- The production callback Read preserves its root-local mutable authority.
No final permissions or successful callback are supplied by the caller. -/
theorem access_root_preserves
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (coherent : LocationCoherent tree initial protections) (short : tree.nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial) :
    let result := tree.performWildcardAccessAt initial root (some selectedNode.tag) .Read protections (rootPosition != 0)
    result.status = .Completed ∧
      GeneralBorrowExposedNonleafState.ReadFrame initial result.location ∧
      LocationCoherent tree result.location protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
      S05SemanticReadEffects.Effects tree initial result.location protections ∧
      (∀ query, ¬Path tree root query → result.location.perms.get query = initial.perms.get query) ∧
      (∀ index found, tree.nodes.get index = some found → Path tree root index →
        Below completion index source → LocalWrite
          ((result.location.perms.get index).getD found.defaultLocationState) (protections.contains found.tag)) ∧
      (∀ index found, tree.nodes.get index = some found → Path tree root index →
        ¬Below completion index source → ForeignWrite
          ((result.location.perms.get index).getD found.defaultLocationState) (protections.contains found.tag)) := by
  obtain ⟨done,frame,cache,sifa,gp,effects,outside,pointwise,transfer⟩ :=
    access_root_information tree completion initial protections complete depth order rootPosition selectedPosition
      root selectedRoot source selectedNode rootSlot selectedSlot selectedPresent different selectedPath
      localRights foreignRights formed coherent short profile possible
  refine ⟨done,frame,cache,sifa,gp,effects,outside,?_,?_⟩
  · intro index node present path below
    have shape := query_shape tree completion initial protections complete depth order rootPosition selectedPosition
      root selectedRoot source index node selectedNode rootSlot selectedSlot selectedPresent different selectedPath
      path present localRights
    dsimp only at shape
    rw [initial_relation tree initial protections root index node (some selectedNode.tag) .Read rootPosition coherent short] at shape
    apply S05ReadRawAuthorityEndpoint.local_right _ _ _
      (relation initial root index node (some selectedNode.tag) .Read rootPosition)
      (localRights index node present path below)
    · rcases shape.1 below with classified | classified <;> simp [classified]
    · exact transfer index node path present
  · intro index node present path below
    have shape := query_shape tree completion initial protections complete depth order rootPosition selectedPosition
      root selectedRoot source index node selectedNode rootSlot selectedSlot selectedPresent different selectedPath
      path present localRights
    dsimp only at shape
    rw [initial_relation tree initial protections root index node (some selectedNode.tag) .Read rootPosition coherent short] at shape
    apply S05ReadRawAuthorityEndpoint.foreign_right _ _ _
      (relation initial root index node (some selectedNode.tag) .Read rootPosition)
      (foreignRights index node present path below)
    · rcases shape.2 below with classified | classified <;> simp [classified]
    · exact transfer index node path present
    · exact effects index node present
    · exact pointwise index node present
    · exact profile.present index node present
    · exact gp index node present

include complete depth order rootSlot selectedSlot selectedPresent different selectedPath localRights foreignRights in
/-- Original root-local result API, projected from the framed production visitor. -/
theorem access_root
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (coherent : LocationCoherent tree initial protections) (short : tree.nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial) :
    let result := tree.performWildcardAccessAt initial root (some selectedNode.tag) .Read protections (rootPosition != 0)
    result.status = .Completed ∧
      GeneralBorrowExposedNonleafState.ReadFrame initial result.location ∧
      LocationCoherent tree result.location protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
      S05SemanticReadEffects.Effects tree initial result.location protections := by
  have actual := access_root_framed tree completion initial protections complete depth order rootPosition selectedPosition
    root selectedRoot source selectedNode rootSlot selectedSlot selectedPresent different selectedPath
    localRights foreignRights formed coherent short profile possible
  obtain ⟨done,frame,cache,sifa,gp,effects,_⟩ := actual
  exact ⟨done,frame,cache,sifa,gp,effects⟩

variable (globalLocal : ∀ index found, tree.nodes.get index = some found →
  Below completion index source → LocalWrite
    ((initial.perms.get index).getD found.defaultLocationState) (protections.contains found.tag))
variable (globalForeign : ∀ index found, tree.nodes.get index = some found →
  ¬ Below completion index source → ForeignWrite
    ((initial.perms.get index).getD found.defaultLocationState) (protections.contains found.tag))
include complete depth order rootSlot selectedSlot selectedPresent different selectedPath globalLocal globalForeign in
/-- Compatibility wrapper for the original global scalar-table API. -/
theorem authorization :
    Authorization tree initial protections root rootPosition (some selectedNode.tag) .Read (Path tree root) := by
  exact authorization_root tree completion initial protections complete depth order rootPosition selectedPosition
    root selectedRoot source selectedNode rootSlot selectedSlot selectedPresent different selectedPath
    (fun index found present _ below => globalLocal index found present below)
    (fun index found present _ outside => globalForeign index found present outside)

include complete depth order rootSlot selectedSlot selectedPresent different selectedPath globalLocal globalForeign in
theorem access
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (coherent : LocationCoherent tree initial protections) (short : tree.nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial) :
    let result := tree.performWildcardAccessAt initial root (some selectedNode.tag) .Read protections (rootPosition != 0)
    result.status = .Completed ∧
      GeneralBorrowExposedNonleafState.ReadFrame initial result.location ∧
      LocationCoherent tree result.location protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
      S05SemanticReadEffects.Effects tree initial result.location protections := by
  exact access_root tree completion initial protections complete depth order rootPosition selectedPosition
    root selectedRoot source selectedNode rootSlot selectedSlot selectedPresent different selectedPath
    (fun index found present _ below => globalLocal index found present below)
    (fun index found present _ outside => globalForeign index found present outside)
    formed coherent short profile possible
end Callback

end DuplicatePrefix.S05CompletedAncestryReadQueries

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05CompletedAncestryReadQueries." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved Read-query dependency {dependency}"
