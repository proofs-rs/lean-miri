import duplicate_prefix.CurrentCallResourceNormalization
import duplicate_prefix.S05CurrentReadProtectorRelease
import duplicate_prefix.CurrentCallEmptyEntryRootLoop
import duplicate_prefix.GeneralBorrowReadCapabilityFrames

namespace DuplicatePrefix.CurrentCallLenReadCapability
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowExposedNonleafPrimaryPath OrdinaryBorrowAuthority
open GeneralBorrowWildcardParentTagOrder GeneralBorrowExposureCardinality GeneralBorrowProjection
open DuplicatePrefixResidualSupportAuthorization DuplicatePrefixCallbackAuthorization
open GeneralRangeMapOrigins GeneralRangeMapState BorrowRangeAccess
open CurrentCallResourceNormalization S05CompletedAncestryReadQueries
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

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
    (model : ParentInterpretation tree completion)
    (_order : ParentTagOrder tree)
    (rootPosition selectedPosition : Nat) (root selectedRoot source query : UniIndex)
    (node selectedNode : TreeNode)
    (_primaryBelow : ∀ root,tree.roots[0]?=some root → Below completion root source)
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
  obtain ⟨rootNode,rootPresent,rootParentless⟩ := model.graph.rootNodes root (Array.mem_toList_iff.mpr (Array.mem_of_getElem? rootSlot))
  obtain ⟨selected,selectedFound,selectedParentless⟩ := model.graph.rootNodes selectedRoot (Array.mem_toList_iff.mpr (Array.mem_of_getElem? selectedSlot))
  have same : selected = selectedNode := Option.some.inj (selectedFound.symm.trans selectedPresent)
  subst selected
  obtain ⟨witness,witnessNode,witnessPresent,exposed,witnessPath,_,witnessBelow,bound⟩ :=
    model.cross_root_origin rootPresent rootParentless selectedPresent
      selectedParentless present different queryPath selectedPath below
  refine ⟨witness,witnessNode,witnessPresent,⟨exposed,?_,?_⟩,witnessPath,witnessBelow⟩
  · exact local_support _ _ (localRights witness witnessNode witnessPresent (CompletedBorrowAncestry.path_trans queryPath witnessPath) witnessBelow)
  · simpa only [Option.isNone_some,Option.any_some,Bool.false_or,decide_eq_true_eq] using bound

/-- Read masks are empty, so entry and postchildren queries coincide. Exact
recording safety follows from this same-query authorization in the existing
visitor; no arbitrary-entry Write claim is used. -/
theorem query_shape (tree : BorrowTree) (completion : Completion)
    (initial : LocationTree) (protections : ProtectedTags)
    (model : ParentInterpretation tree completion)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (rootPosition selectedPosition : Nat) (root selectedRoot source query : UniIndex)
    (node selectedNode : TreeNode)
    (primaryBelow : ∀ root,tree.roots[0]?=some root → Below completion root source)
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
  have eligibleOrigin := origin_root tree completion initial protections model order rootPosition selectedPosition
    root selectedRoot source query node selectedNode primaryBelow rootSlot selectedSlot selectedPresent different selectedPath queryPath present localRights
  obtain ⟨rootNode,rootPresent,_⟩ := model.graph.rootNodes root (Array.mem_toList_iff.mpr (Array.mem_of_getElem? rootSlot))
  have primary : rootPosition = 0 → ∃ witness witnessNode,
      tree.nodes.get witness = some witnessNode ∧
      Supports initial protections witness witnessNode (some selectedNode.tag) .Read ∧
      Path tree root witness ∧ Below completion witness source := by
    intro zero
    exact origin_root tree completion initial protections model order rootPosition selectedPosition
      root selectedRoot source root rootNode selectedNode primaryBelow rootSlot selectedSlot selectedPresent different selectedPath
      (.refl root rootNode rootPresent) rootPresent localRights
      (primaryBelow root (by simpa only [zero] using rootSlot))
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
          exact below (CompletedBorrowAncestry.below_trans (model.physical_below physical) witnessBelow)
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
    (model : ParentInterpretation tree completion)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (rootPosition selectedPosition : Nat) (root selectedRoot source query : UniIndex)
    (node selectedNode : TreeNode)
    (primaryBelow : ∀ root,tree.roots[0]?=some root → Below completion root source)
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
  have shape := query_shape tree completion initial protections model depth order rootPosition selectedPosition
    root selectedRoot source query node selectedNode primaryBelow rootSlot selectedSlot selectedPresent different selectedPath
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


section Callback
variable (tree : BorrowTree) (completion : Completion) (initial : LocationTree) (protections : ProtectedTags)
variable (model : ParentInterpretation tree completion)
variable (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
variable (rootPosition selectedPosition : Nat) (root selectedRoot source : UniIndex) (selectedNode : TreeNode)
variable (primaryBelow : ∀ root,tree.roots[0]?=some root → Below completion root source)
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

include model rootSlot in
/-- Canonical physical descendant support has no permission fields. -/
def support : GeneralBorrowWildcardControlStack.Support tree root where
  contains := Path tree root
  rooted := by
    obtain ⟨node,present,_⟩ := model.graph.rootNodes root (Array.mem_toList_iff.mpr (Array.mem_of_getElem? rootSlot))
    exact .refl root node present
  present := fun _ path => path.present
  children := by
    intro index node path present child member
    obtain ⟨forest⟩ := model.graph.forest default {}
    obtain ⟨childNode,childPresent,edge⟩ := GeneralBorrowGcDfsOriginalEdges.children tree default {} forest model.graph.children index node present child member
    exact .step path childNode childPresent edge

include model primaryBelow depth order rootSlot selectedSlot selectedPresent different selectedPath localRights foreignRights in
/-- Completed source-relative raw tables supply a Read-only residual contract.
Both Read masks reduce to the actual empty mask; no legacy Row is required. -/
theorem authorization_root :
    Authorization tree initial protections root rootPosition (some selectedNode.tag) .Read (Path tree root) := by
  let area := support tree completion model rootPosition root rootSlot
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
    exact authorized_root tree completion initial protections model depth order rootPosition selectedPosition
      root selectedRoot source query node selectedNode primaryBelow rootSlot selectedSlot selectedPresent different selectedPath
      path present localRights foreignRights
  · intro zero
    obtain ⟨rootNode,rootPresent,_⟩ := model.graph.rootNodes root (Array.mem_toList_iff.mpr (Array.mem_of_getElem? rootSlot))
    have below := primaryBelow root (by simpa only [zero] using rootSlot)
    obtain ⟨witness,node,present,eligible,path,_⟩ := origin_root tree completion initial protections model order
      rootPosition selectedPosition root selectedRoot source root rootNode selectedNode primaryBelow rootSlot selectedSlot
      selectedPresent different selectedPath (.refl root rootNode rootPresent) rootPresent localRights below
    exact ⟨witness,node,path,present,eligible⟩

include model primaryBelow depth order rootSlot selectedSlot selectedPresent different selectedPath localRights foreignRights in
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
  have auth := authorization_root tree completion initial protections model depth order rootPosition selectedPosition
    root selectedRoot source selectedNode primaryBelow rootSlot selectedSlot selectedPresent different selectedPath localRights foreignRights
  let area := support tree completion model rootPosition root rootSlot
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

include model primaryBelow depth order rootSlot selectedSlot selectedPresent different selectedPath localRights foreignRights in
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
    access_root_information tree completion initial protections model depth order rootPosition selectedPosition
      root selectedRoot source selectedNode primaryBelow rootSlot selectedSlot selectedPresent different selectedPath
      localRights foreignRights formed coherent short profile possible
  refine ⟨done,frame,cache,sifa,gp,effects,outside,?_,?_⟩
  · intro index node present path below
    have shape := query_shape tree completion initial protections model depth order rootPosition selectedPosition
      root selectedRoot source index node selectedNode primaryBelow rootSlot selectedSlot selectedPresent different selectedPath
      path present localRights
    dsimp only at shape
    rw [initial_relation tree initial protections root index node (some selectedNode.tag) .Read rootPosition coherent short] at shape
    apply S05ReadRawAuthorityEndpoint.local_right _ _ _
      (relation initial root index node (some selectedNode.tag) .Read rootPosition)
      (localRights index node present path below)
    · rcases shape.1 below with classified | classified <;> simp [classified]
    · exact transfer index node path present
  · intro index node present path below
    have shape := query_shape tree completion initial protections model depth order rootPosition selectedPosition
      root selectedRoot source index node selectedNode primaryBelow rootSlot selectedSlot selectedPresent different selectedPath
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


end Callback

private theorem row_access (tree : BorrowTree) (completion : Completion) (initial : LocationTree) (protections : ProtectedTags)
    (model : ParentInterpretation tree completion) (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (distinct : tree.roots.toList.Nodup)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (selectedPosition : Nat) (selected source : UniIndex) (selectedNode : TreeNode)
    (primaryBelow : ∀ root,tree.roots[0]?=some root → Below completion root source)
    (selectedSlot : tree.roots[selectedPosition]? = some selected)
    (selectedPresent : tree.nodes.get selected = some selectedNode) (sourcePath : Path tree selected source)
    (reader : UniIndex) (readerPath : Path tree selected reader)
    (normalRights : ∀ index node, tree.nodes.get index = some node → Path tree selected index →
      DuplicatePrefixScalarAuthorization.Compatible
        ((initial.perms.get index).getD node.defaultLocationState) .Read
        (GeneralBorrowAnchor.relation (source_normal_projection tree initial protections) reader.toNat index.toNat)
        (protections.contains node.tag))
    (localRights : ∀ (position : Nat) (root : UniIndex), tree.roots[position]? = some root → root ≠ selected →
      ∀ index node, tree.nodes.get index = some node → Path tree root index → Below completion index source →
        LocalWrite ((initial.perms.get index).getD node.defaultLocationState) (protections.contains node.tag))
    (foreignRights : ∀ (position : Nat) (root : UniIndex), tree.roots[position]? = some root → root ≠ selected →
      ∀ index node, tree.nodes.get index = some node → Path tree root index → ¬Below completion index source →
        ForeignWrite ((initial.perms.get index).getD node.defaultLocationState) (protections.contains node.tag))
    (coherent : LocationCoherent tree initial protections)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial)
    (short : tree.nodes.size < 65536) (mode : ChildrenVisitMode) (range : ByteRange) :
    let result := source_tree_access_at tree initial (some reader) .Read protections mode range
    source_access_status result = none ∧
      LocationCoherent tree (source_access_location result) protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree (source_access_location result) protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree (source_access_location result) ∧
      (∀ index node, tree.nodes.get index = some node → Path tree selected index →
        (source_access_location result).perms.get index =
          (tree.performNormalAccessAt initial reader .Read protections mode).location.perms.get index) ∧
      (∀ (position : Nat) (root : UniIndex), tree.roots[position]? = some root → root ≠ selected →
        ∀ index node, tree.nodes.get index = some node → Path tree root index → Below completion index source →
          LocalWrite (((source_access_location result).perms.get index).getD node.defaultLocationState) (protections.contains node.tag)) ∧
      (∀ (position : Nat) (root : UniIndex), tree.roots[position]? = some root → root ≠ selected →
        ∀ index node, tree.nodes.get index = some node → Path tree root index → ¬Below completion index source →
          ForeignWrite (((source_access_location result).perms.get index).getD node.defaultLocationState) (protections.contains node.tag)) := by
  have fits : tree.nodes.data.size ≤ 4294967296 := by
    have size : tree.nodes.data.size = tree.nodes.size := rfl
    rw [size];omega
  obtain ⟨actual,found,parentless⟩ := model.graph.rootNodes selected (Array.mem_toList_iff.mpr (Array.mem_of_getElem? selectedSlot))
  have same : actual = selectedNode := Option.some.inj (found.symm.trans selectedPresent)
  subst actual
  obtain ⟨normal⟩ := GeneralBorrowPhysicalNormalCapability.of_physical_component tree initial protections
    formed fits selected reader selectedNode selectedPresent parentless readerPath .Read normalRights
  obtain ⟨readerNode,readerPresent⟩ := readerPath.present
  have rootPath := S05CompletedAncestryNormal.root_path tree initial protections formed selected reader selectedNode
    selectedPresent parentless readerPath
  have normalDone := GeneralBorrowReadCapabilityNormal.access tree initial protections formed reader readerNode
    readerPresent normal coherent profile possible short mode
  have frame : ∀ (position : Nat) (root : UniIndex), tree.roots[position]? = some root → root ≠ selected →
      ∀ index node, tree.nodes.get index = some node → Path tree root index →
        (tree.performNormalAccessAt initial reader .Read protections mode).location.perms.get index = initial.perms.get index := by
    intro position root slot different index node present path
    have data := Array.getElem?_eq_some_iff.mp slot
    have member : root ∈ tree.roots.toList := by
      rw [←data.2];exact Array.mem_toList_iff.mpr (Array.getElem_mem data.1)
    exact (GeneralBorrowNormalOtherRootFrame.access_kind tree initial protections formed reader selected root readerNode
      readerPresent .Read normal rootPath member (Ne.symm different) coherent mode).2.2.2 index node present path
  let Rights := fun location : LocationTree =>
    (∀ (position : Nat) (root : UniIndex),tree.roots[position]?=some root → root≠selected →
      ∀ index node,tree.nodes.get index=some node → Path tree root index →
        (Below completion index source → LocalWrite ((location.perms.get index).getD node.defaultLocationState) (protections.contains node.tag)) ∧
        (¬Below completion index source → ForeignWrite ((location.perms.get index).getD node.defaultLocationState) (protections.contains node.tag)))
  have currentRights : Rights (tree.performNormalAccessAt initial reader .Read protections mode).location := by
    intro position root slot different index node present path
    rw [frame position root slot different index node present path]
    exact ⟨localRights position root slot different index node present path,foreignRights position root slot different index node present path⟩
  have final := CurrentCallEmptyEntryRootLoop.roots tree initial protections formed distinct selectedPosition selected selectedSlot
    Rights (some selectedNode.tag) .Read (fun position root rootAt different current rights cache sifa gp _ => by
      obtain ⟨done,_,afterCache,afterSifa,afterPossible,_,outside,localRight,foreignRight⟩ :=
        access_root_preserves tree completion current protections model depth order position selectedPosition root selected source selectedNode
          primaryBelow rootAt selectedSlot selectedPresent different sourcePath
          (fun index node present path below => (rights position root rootAt different index node present path).1 below)
          (fun index node present path below => (rights position root rootAt different index node present path).2 below)
          formed cache short sifa gp
      refine ⟨done,afterCache,afterSifa,afterPossible,outside,?_⟩
      intro otherPosition other otherAt otherDifferent index node present path
      by_cases same : other=root
      · subst other
        exact ⟨localRight index node present path,foreignRight index node present path⟩
      · have notCurrent : ¬Path tree root index := by
          intro currentPath
          obtain ⟨rootNode,rootPresent,rootNone⟩ := formed.rootNodes root (Array.mem_toList_iff.mpr (Array.mem_of_getElem? rootAt))
          obtain ⟨otherNode,otherPresent,otherNone⟩ := formed.rootNodes other (Array.mem_toList_iff.mpr (Array.mem_of_getElem? otherAt))
          exact same (CompletedBorrowAncestry.physical_roots_unique rootPresent rootNone otherPresent otherNone currentPath path).symm
        rw [outside index notCurrent]
        exact rights otherPosition other otherAt otherDifferent index node present path)
    (if mode == .SkipChildrenOfAccessed then source_min_exposed tree reader else none) mode range
    (tree.performNormalAccessAt initial reader .Read protections mode).location currentRights
    normalDone.2.2.1 normalDone.2.2.2.1 normalDone.2.2.2.2.1 frame
  have path : ((source_normal_projection tree initial protections).topology.ancestorPath reader.toNat).getLast! = selected.toNat := by
    rw [List.getLast!_eq_getLast?_getD,rootPath];rfl
  have rootEq : (tree.performNormalAccessAt initial reader .Read protections mode).access.root = selected.toNat :=
    (GeneralBorrowStorage.events_root _ _ .Read (source_normal_projection tree initial protections)).trans path
  dsimp only
  simp_tree_helpers
  simp only [normalDone.1,normalDone.2.1,rootEq,GeneralBorrowProjection.index_self,Option.bind_some,selectedPresent,Option.map_some]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  refine ⟨final.1,final.2.1,final.2.2.1,final.2.2.2.1,final.2.2.2.2.1,?_,?_⟩
  · intro position root slot different index node present path below
    exact (final.2.2.2.2.2 position root slot different index node present path).1 below
  · intro position root slot different index node present path below
    exact (final.2.2.2.2.2 position root slot different index node present path).2 below


private theorem capability_selected (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree) (root reader : UniIndex)
    (readerPath : GeneralBorrowExposedNonleafPrimaryPath.Path tree root reader)
    (normal : DuplicatePrefixNormalKind.Capability tree location protections reader .Read) :
    ∀ index node, tree.nodes.get index = some node → GeneralBorrowExposedNonleafPrimaryPath.Path tree root index →
      DuplicatePrefixScalarAuthorization.Compatible (CandidateStableCallOwnership.RawState location index node) .Read
        (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) reader.toNat index.toNat)
        (protections.contains node.tag) := by
  obtain ⟨forest⟩ := formed.forest location protections
  have projected := GeneralBorrowPhysicalRootPath.projection_desc tree location protections root reader readerPath
  have rootInside := GeneralBorrowNormalComponentNormalization.contains_ancestor _ reader.toNat normal.component
    root.toNat reader.toNat projected normal.component.anchor
  intro index node present path
  have projected := GeneralBorrowPhysicalRootPath.projection_desc tree location protections root index path
  have supported := GeneralBorrowNormalComponentNormalization.contains_descendant _ forest reader.toNat normal.component
    root.toNat index.toNat projected rootInside
  obtain ⟨state,stored,compatible⟩ := normal.permissions index.toNat supported
    (GeneralBorrowNodeUpdate.lookup_valid tree.nodes index node present)
  have actualState := projection_state tree location protections index.toNat index node (index_self index) rfl present
  have equal : state = CandidateStableCallOwnership.RawState location index node := Option.some.inj (stored.symm.trans actualState)
  subst state
  rw [GeneralBorrowNormalPermissionMetadata.held tree location protections index node present] at compatible
  exact compatible


/-- Actual ranged concrete Read for a Frozen reader, with mutable source rights ONLY in other physical roots. -/
theorem access (tree : BorrowTree) (completion : Completion) (protections : ProtectedTags)
    (model : ParentInterpretation tree completion) (distinct : tree.roots.toList.Nodup)
    (selectedPosition : Nat) (selected source reader : UniIndex) (selectedNode readerNode : TreeNode)
    (primaryBelow : ∀ root,tree.roots[0]?=some root → Below completion root source)
    (selectedSlot : tree.roots[selectedPosition]? = some selected)
    (selectedPresent : tree.nodes.get selected = some selectedNode) (sourcePath : Path tree selected source)
    (readerPresent : tree.nodes.get reader = some readerNode) (readerPath : Path tree selected reader)
    (offset len : Size) (lower upper : UInt64)
    (owned : OwnedOn (S05CurrentReadProtectorRelease.Authority tree completion protections selected source reader)
      lower upper tree.locations)
    (well : tree.locations.WellFormed)
    (runtime : Every (fun location => LocationCoherent tree location protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location) tree.locations)
    (bounds : offset.bytes.toNat + len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (requestLower : lower.toNat ≤ offset.bytes.toNat)
    (requestUpper : (offset.bytes + len.bytes).toNat ≤ upper.toNat)
    (short : tree.nodes.size < 65536) (mode : ChildrenVisitMode) :
    GeneralBorrowConcreteRangeInvariant.Contract tree
      (S05CurrentReadProtectorRelease.Authority tree completion protections selected source reader)
      (fun location => LocationCoherent tree location protections ∧
        GeneralBorrowLocationSifaConsistency.Profile tree location protections ∧
        GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location)
      (fun before after => before = after ∨
        ∀ index node, tree.nodes.get index = some node → Path tree selected index →
          after.perms.get index =
            (tree.performNormalAccessAt before reader .Read protections mode).location.perms.get index)
      lower upper (tree.performBorrowAccessRange (.concrete readerNode.tag) offset len .Read protections mode) := by
  let formed := model.graph
  let depth := Classical.choice formed.depth
  let order := model.order
  have mapped : tree.indexOfTag readerNode.tag=some reader := formed.allocator.nodeTags reader readerNode readerPresent
  apply GeneralBorrowConcreteRangeEntry.access tree protections readerNode.tag reader mapped offset len .Read mode
    _ _ _ _ (fun _ initial => initial) (fun _ => Or.inl rfl) _
    lower upper owned well runtime bounds requestLower requestUpper
  intro location authority representation range
  obtain ⟨normal⟩ := authority.2.1
  have rights := capability_selected tree location protections formed selected reader readerPath normal
  have normalDone := GeneralBorrowReadCapabilityNormal.access tree location protections formed reader readerNode
    readerPresent normal representation.1 representation.2.1 representation.2.2 short mode
  have row := row_access tree completion location protections model formed distinct depth order
    selectedPosition selected source selectedNode primaryBelow selectedSlot selectedPresent sourcePath reader readerPath rights
    (fun position root slot different index node present path below =>
      (authority.2.2 position root slot different index node present path).1 below)
    (fun position root slot different index node present path outside =>
      (authority.2.2 position root slot different index node present path).2 outside)
    representation.1 representation.2.1 authority.1 short mode range
  obtain ⟨afterNormal,componentEq⟩ := normalDone.2.2.2.2.2
  have afterRights := capability_selected tree _ protections formed selected reader readerPath afterNormal
  obtain ⟨actual,found,parentless⟩ := model.graph.rootNodes selected (Array.mem_toList_iff.mpr (Array.mem_of_getElem? selectedSlot))
  have same : actual = selectedNode := Option.some.inj (found.symm.trans selectedPresent)
  subst actual
  have fits : tree.nodes.data.size ≤ 4294967296 := by change tree.nodes.size ≤ _;omega
  have cap := GeneralBorrowPhysicalNormalCapability.of_physical_component tree
    (source_access_location (source_tree_access_at tree location (some reader) .Read protections mode range))
    protections formed fits selected reader selectedNode selectedPresent parentless readerPath .Read (by
      intro index node present path
      have right := afterRights index node present path
      unfold CandidateStableCallOwnership.RawState at right
      rw [←row.2.2.2.2.1 index node present path] at right
      exact right)
  refine ⟨row.1,⟨row.2.2.2.1,cap,?_⟩,⟨row.2.1,row.2.2.1,row.2.2.2.1⟩,Or.inr row.2.2.2.2.1⟩
  intro position root slot different index node present path
  exact ⟨row.2.2.2.2.2.1 position root slot different index node present path,
    row.2.2.2.2.2.2 position root slot different index node present path⟩

end
end DuplicatePrefix.CurrentCallLenReadCapability
open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallLenReadCapability" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual len reader dependency {dependency}"
