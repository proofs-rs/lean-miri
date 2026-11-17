import duplicate_prefix.CurrentCallResourceAccess
import duplicate_prefix.S05CompletedAncestryReadQueries
import duplicate_prefix.S05WildcardCompletedRead

/-! Candidate resource normalization consumed by the actual associated Read.
One fixed issued grant and optional parent interpretation are retained; no
Ordinary adoption or constructor/copy/GC adequacy is asserted. -/
namespace DuplicatePrefix.CurrentCallResourceRead
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.DataStructures
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources OrdinaryBorrowAuthority
open CurrentCallResourceNormalization CurrentCallResourceAccess GeneralBorrowExposedNonleafPrimaryPath
open GeneralBorrowExposureCardinality DuplicatePrefixResidualSupportAuthorization
open DuplicatePrefixCallbackAuthorization GeneralBorrowProjection GeneralBorrowForest
open GeneralRangeMapOrigins GeneralRangeMapState
open GeneralBorrowConcreteRowCutoffAccess (State scan)
open DuplicatePrefix.BorrowRangeAccess
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 65536
noncomputable section

private theorem normal_read (tree : BorrowTree) (completion : Completion) (initial : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree) (distinct : tree.roots.toList.Nodup)
    (selectedPosition : Nat) (selected source : UniIndex) (selectedNode sourceNode : TreeNode)
    (selectedSlot : tree.roots[selectedPosition]? = some selected)
    (selectedPresent : tree.nodes.get selected = some selectedNode) (sourcePresent : tree.nodes.get source = some sourceNode)
    (sourcePath : Path tree selected source)
    (normal : DuplicatePrefixBorrowAuthorization.Normal tree initial protections source)
    (authority : S05CompletedAncestryReadMutable.Authority tree completion protections source initial)
    (classification : ∀ index node, tree.nodes.get index = some node → Path tree selected index →
      (Below completion index source ↔ Path tree index source))
    (coherent : LocationCoherent tree initial protections)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial)
    (callback : ∀ (position : Nat) (root : UniIndex), tree.roots[position]? = some root → root ≠ selected →
      ∀ current : LocationTree, S05CompletedAncestryReadMutable.Authority tree completion protections source current →
      LocationCoherent tree current protections →
      GeneralBorrowLocationSifaConsistency.Profile tree current protections →
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree current →
      (∀ index node,tree.nodes.get index = some node → Path tree root index → current.perms.get index = initial.perms.get index) →
      let result := tree.performWildcardAccessAt current root (some selectedNode.tag) .Read protections (position != 0)
      result.status = .Completed ∧ LocationCoherent tree result.location protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
      (∀ query,¬Path tree root query → result.location.perms.get query = current.perms.get query) ∧
      S05CompletedAncestryReadMutable.Authority tree completion protections source result.location)
    (mode : ChildrenVisitMode) (range : ByteRange) :
    let result := source_tree_access_at tree initial (some source) .Read protections mode range
    source_access_status result = none ∧ LocationCoherent tree (source_access_location result) protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree (source_access_location result) protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree (source_access_location result) ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree (source_access_location result) protections source) ∧
      S05CompletedAncestryReadMutable.Authority tree completion protections source (source_access_location result) := by
  obtain ⟨depth⟩ := formed.depth
  obtain ⟨forest⟩ := formed.forest initial protections
  obtain ⟨actual,actualAt,parentless⟩ := formed.rootNodes selected (Array.mem_toList_iff.mpr (Array.mem_of_getElem? selectedSlot))
  have actualEq : actual = selectedNode := Option.some.inj (actualAt.symm.trans selectedPresent)
  subst actual
  have rootPath := S05CompletedAncestryNormal.root_path tree initial protections formed selected source selectedNode selectedPresent parentless sourcePath
  have normalDone := DuplicatePrefixNormalKind.access tree initial protections source .Read mode
    (DuplicatePrefixNormalKind.of_normal tree initial protections source normal .Read) formed sourceNode sourcePresent coherent
  have fits : tree.nodes.data.size ≤ 4294967296 := formed.fits
  have owned : GeneralBorrowCompatibleScopedNormal.Owned (source_normal_projection tree initial protections) source.toNat .Read normal.component := by
    intro index inside valid
    have sizes : (source_normal_projection tree initial protections).topology.nodes.size = tree.nodes.data.size := by
      unfold_general_projection;unfold_general_topology;simp only [Array.size_map]
    exact normal.permissions .Read index inside (by rw [←sizes];exact valid)
  have afterProfile := (GeneralBorrowCompatibleLocationSifaConsistency.normal tree initial protections source .Read mode
    fits depth formed.children sourceNode sourcePresent forest normal.component owned profile).2.2
  have afterPossible := GeneralBorrowCompatibleNormalPossible.normal tree initial protections source .Read mode fits forest
    (GeneralBorrowExposedScopedNormalMetadata.valid_aligned tree initial protections source sourceNode sourcePresent).1 normal possible
  have frame : ∀ (position : Nat) (root : UniIndex),tree.roots[position]? = some root → root ≠ selected →
      ∀ index node,tree.nodes.get index = some node → Path tree root index →
      (tree.performNormalAccessAt initial source .Read protections mode).location.perms.get index = initial.perms.get index := by
    intro position root rootAt different index node present path
    have member := Array.mem_toList_iff.mpr (Array.mem_of_getElem? rootAt)
    exact (GeneralBorrowNormalOtherRootFrame.access tree initial protections formed source selected root sourceNode sourcePresent normal rootPath member
      (Ne.symm different) .Read coherent mode).2.2.2 index node present path
  have currentNormal := DuplicatePrefixNormalAuthorizationPreservation.normal_preserves tree initial protections source .Read mode fits forest
    (GeneralBorrowExposedScopedNormalMetadata.valid_aligned tree initial protections source sourceNode sourcePresent).1 normal
  obtain ⟨currentNormal⟩ := currentNormal
  have currentAuthority : S05CompletedAncestryReadMutable.Authority tree completion protections source
      (tree.performNormalAccessAt initial source .Read protections mode).location := by
    have selectedRights := CurrentCallEmptyEntryNormalWrite.raw_of_normal tree completion _ protections formed depth fits selected source sourcePath classification currentNormal
    intro index node present
    obtain ⟨position,root,rootNode,rootAt,rootPresent,path⟩ := CandidateCurrentWindowAuthority.root_path tree formed index node present
    by_cases same : root = selected
    · subst root
      exact selectedRights index node present path
    · unfold RawState
      rw [frame position root rootAt same index node present path]
      exact authority index node present
  have final := CurrentCallEmptyEntryRootLoop.roots tree initial protections formed distinct selectedPosition selected selectedSlot
    (fun row => Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree row protections source) ∧
      S05CompletedAncestryReadMutable.Authority tree completion protections source row) (some selectedNode.tag) .Read
    (fun position root rootAt different current retained cache sifa gp currentFrame => by
      obtain ⟨done,outCache,outProfile,outPossible,outside,outAuthority⟩ := callback position root rootAt different current retained.2 cache sifa gp currentFrame
      obtain ⟨oldNormal⟩ := retained.1
      have member := Array.mem_toList_iff.mpr (Array.mem_of_getElem? rootAt)
      obtain ⟨nextNormal,_⟩ := GeneralBorrowNormalOtherCallbackFrame.transport tree current _ protections formed
        source selected root sourceNode sourcePresent oldNormal rootPath member (Ne.symm different) (Path tree root)
        (fun _ path => path.present)
        (fun query path => GeneralBorrowSharedAuthorizationGeometry.covers_of_path tree depth root query path) outside
      exact ⟨done,outCache,outProfile,outPossible,outside,⟨⟨nextNormal⟩,outAuthority⟩⟩)
    (if mode == .SkipChildrenOfAccessed then source_min_exposed tree source else none) mode range
    (tree.performNormalAccessAt initial source .Read protections mode).location ⟨⟨currentNormal⟩,currentAuthority⟩ normalDone.2.2 afterProfile afterPossible frame
  have ending : ((source_normal_projection tree initial protections).topology.ancestorPath source.toNat).getLast! = selected.toNat := by
    rw [List.getLast!_eq_getLast?_getD,rootPath];rfl
  have rootEq : (tree.performNormalAccessAt initial source .Read protections mode).access.root = selected.toNat :=
    (GeneralBorrowStorage.events_root _ _ .Read (source_normal_projection tree initial protections)).trans ending
  dsimp only
  simp_tree_helpers
  simp only [normalDone.1,normalDone.2.1,rootEq,GeneralBorrowProjection.index_self,Option.bind_some,selectedPresent,Option.map_some]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  simpa only [GeneralBorrowConcreteRowCutoffAccess.scan,Id.run,bind,pure] using
    (show _ from ⟨final.1,final.2.1,final.2.2.1,final.2.2.2.1,final.2.2.2.2.2⟩)


variable {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode) (G : Geometry W)
    (exclusive : demandOf mode = .exclusive)
    (byte : AllocId × Nat) (inside : Window id offset length byte)
    (segment : RangeMapSegment LocationTree)
    (member : segment ∈ W.allocation.extra.locations.entries.toList)
    (lower : segment.range.start.toNat ≤ byte.2) (upper : byte.2 < segment.range.stop.toNat)

include exclusive byte inside member lower upper in
/-- Read authorization is derived from resource rights and the SAME masked
geometry; Read removal masks are proved empty by the existing mask theorem. -/
theorem authorization
    (profile : GeneralBorrowLocationSifaConsistency.Profile W.allocation.extra segment.data tracker.global.protectedTags)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible W.allocation.extra segment.data)
    (position : Nat) (root : UniIndex) (slot : W.allocation.extra.roots[position]? = some root)
    (callback : Callback W.pointer G.selectedRoot root) :
    Authorization W.allocation.extra segment.data tracker.global.protectedTags root position
      (cutoff W.pointer G.selectedNode) .Read (Path W.allocation.extra root) := by
  let tree := W.allocation.extra
  obtain ⟨depth⟩ := W.parents.graph.depth
  obtain ⟨forest⟩ := W.parents.graph.forest segment.data tracker.global.protectedTags
  have rights := row_authority W exclusive byte inside segment member lower upper profile possible
  obtain ⟨rootNode,rootAt,parentless⟩ := W.parents.graph.rootNodes root
    (Array.mem_toList_iff.mpr (Array.mem_of_getElem? slot))
  refine ⟨.refl root rootNode rootAt,(fun _ path => path.present),?_,?_,?_,?_,?_⟩
  · intro index node path present child childMember
    obtain ⟨next,nextAt,edge⟩ := GeneralBorrowGcDfsOriginalEdges.children tree segment.data tracker.global.protectedTags forest W.parents.graph.children index node present child childMember
    exact .step path next nextAt edge
  · intro query path
    exact GeneralBorrowSharedAuthorizationGeometry.covers_of_path tree depth root query path
  · intro query node path present
    by_cases below : Below W.precise.completion query W.pointer.grant
    · exact (rights query node present).1 below |>.1
    · exact (rights query node present).2 below |>.1
  · intro beforeMask afterMask legalBefore legalAfter _ query node path present _
    have beforeEmpty := read_removal_empty tree segment.data tracker.global.protectedTags (cutoff W.pointer G.selectedNode) beforeMask legalBefore
    have afterEmpty := read_removal_empty tree segment.data tracker.global.protectedTags (cutoff W.pointer G.selectedNode) afterMask legalAfter
    subst beforeMask
    subst afterMask
    apply (DuplicatePrefixResidualInitialSnapshot.same_query_iff _ _ _ _).mpr
    have shape := (G.masked byte inside segment member lower upper .Read position root slot callback
      query node present path [] (empty_removal _ _ _ _ _)).2
    by_cases below : Below W.precise.completion query W.pointer.grant
    · have raw := (rights query node present).1 below
      rcases shape.1 below with localQuery | eitherQuery
      · rw [localQuery]
        exact ⟨raw.1,Or.inr (OrdinaryBorrowAuthorityBridge.local_scalar _ _ raw .Read)⟩
      · rw [eitherQuery];exact raw.1
    · have raw := (rights query node present).2 below
      rcases shape.2 below with foreignQuery | eitherQuery
      · rw [foreignQuery]
        exact ⟨raw.1,Or.inr (S05CompletedAncestryReadQueries.foreign_read _ _ raw)⟩
      · rw [eitherQuery];exact raw.1
  · intro zero
    have atZero : W.allocation.extra.roots[0]? = some root := by simpa only [zero] using slot
    have primaryEq : root = allocationRoot := Option.some.inj (atZero.symm.trans W.issued.capability.rootSlot)
    subst root
    obtain ⟨witness,node,present,eligible,path,_⟩ := G.primarySupport byte inside segment member lower upper .Read callback
    exact ⟨witness,node,path,present,eligible⟩

include exclusive byte inside member lower upper in
/-- The actual Read DFS records SIFA/cache effects and retains full mutable
source authority on the SAME C, using the actual snapshot transfer theorem. -/
theorem read_callback
    (coherent : LocationCoherent W.allocation.extra segment.data tracker.global.protectedTags)
    (short : W.allocation.extra.nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile W.allocation.extra segment.data tracker.global.protectedTags)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible W.allocation.extra segment.data)
    (position : Nat) (root : UniIndex) (slot : W.allocation.extra.roots[position]? = some root)
    (callback : Callback W.pointer G.selectedRoot root) :
    let result := W.allocation.extra.performWildcardAccessAt segment.data root (cutoff W.pointer G.selectedNode)
      .Read tracker.global.protectedTags (position != 0)
    result.status = .Completed ∧ GeneralBorrowExposedNonleafState.ReadFrame segment.data result.location ∧
      LocationCoherent W.allocation.extra result.location tracker.global.protectedTags ∧
      GeneralBorrowLocationSifaConsistency.Profile W.allocation.extra result.location tracker.global.protectedTags ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible W.allocation.extra result.location ∧
      S05SemanticReadEffects.Effects W.allocation.extra segment.data result.location tracker.global.protectedTags ∧
      (∀ query,¬Path W.allocation.extra root query → result.location.perms.get query = segment.data.perms.get query) ∧
      S05CompletedAncestryReadMutable.Authority W.allocation.extra W.precise.completion tracker.global.protectedTags W.pointer.grant result.location := by
  let tree := W.allocation.extra
  let held := tracker.global.protectedTags
  let maximum := cutoff W.pointer G.selectedNode
  obtain ⟨depth⟩ := W.parents.graph.depth
  obtain ⟨forest⟩ := W.parents.graph.forest segment.data held
  have graph := GeneralBorrowExposedScopedReciprocal.of_forest tree segment.data held forest depth
  have auth := authorization W G exclusive byte inside segment member lower upper profile possible position root slot callback
  let area : GeneralBorrowWildcardControlStack.Support tree root := ⟨Path tree root,auth.rooted,auth.present,auth.children⟩
  have snapshot := DuplicatePrefixResidualInitialSnapshot.snapshot tree segment.data held root position maximum .Read (Path tree root) auth coherent short
  have plans : Nonempty (GeneralBorrowSnapshotReadDFSPlan.WitnessPlan tree segment.data held root position maximum) := by
    by_cases zero : position = 0
    · subst position
      exact GeneralBorrowSnapshotOrderedPrimaryReadPlan.of_authorization tree segment.data held root maximum (Path tree root)
        W.parents.order depth graph coherent short auth
    · exact ⟨GeneralBorrowSnapshotVirtualReadAccess.plan tree segment.data held root position maximum zero⟩
  obtain ⟨plan⟩ := plans
  let weights := GeneralBorrowWildcardForestWeights.of_forest tree segment.data held forest
  have bound := GeneralBorrowWildcardForestWeights.bounded tree segment.data held forest root
  obtain ⟨done,frame,_,pointwise,cache,outside,runtime,_,transfer,effects⟩ := S05SemanticReadDFS.access true false tree segment.data held root position maximum
    weights bound area snapshot depth coherent plan (fun _ => ⟨profile,possible⟩) (by simp)
  have rights := row_authority W exclusive byte inside segment member lower upper profile possible
  refine ⟨done,frame,cache,(runtime rfl).1,(runtime rfl).2,effects,outside,?_⟩
  intro index node present
  by_cases path : Path tree root index
  · have shape := (G.masked byte inside segment member lower upper .Read position root slot callback index node present path [] (empty_removal _ _ _ _ _)).2
    rw [initial_relation tree segment.data held root index node maximum .Read position coherent short] at shape
    constructor
    · intro below
      apply S05ReadRawAuthorityEndpoint.local_right _ _ _ (relation segment.data root index node maximum .Read position) ((rights index node present).1 below)
      · rcases shape.1 below with yes | yes <;> simp [yes]
      · exact transfer index node path present
    · intro notBelow
      apply S05ReadRawAuthorityEndpoint.foreign_right _ _ _ (relation segment.data root index node maximum .Read position) ((rights index node present).2 notBelow)
      · rcases shape.2 notBelow with yes | yes <;> simp [yes]
      · exact transfer index node path present
      · exact effects index node present
      · exact pointwise index node present
      · exact profile.present index node present
      · exact (runtime rfl).2 index node present
  · unfold RawState
    rw [outside index path]
    exact rights index node present

include exclusive byte inside member lower upper in
/-- Internal saved-component transport for sequential actual callbacks. -/
private theorem framed_callback
    (initialProfile : GeneralBorrowLocationSifaConsistency.Profile W.allocation.extra segment.data tracker.global.protectedTags)
    (initialPossible : GeneralBorrowSnapshotReadRuntime.GlobalPossible W.allocation.extra segment.data)
    (current : LocationTree)
    (rights : S05CompletedAncestryReadMutable.Authority W.allocation.extra W.precise.completion tracker.global.protectedTags W.pointer.grant current)
    (coherent : LocationCoherent W.allocation.extra current tracker.global.protectedTags)
    (short : W.allocation.extra.nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile W.allocation.extra current tracker.global.protectedTags)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible W.allocation.extra current)
    (position : Nat) (root : UniIndex) (slot : W.allocation.extra.roots[position]? = some root)
    (callback : Callback W.pointer G.selectedRoot root)
    (slots : ∀ index node,W.allocation.extra.nodes.get index = some node → Path W.allocation.extra root index → current.perms.get index = segment.data.perms.get index) :
    let result := W.allocation.extra.performWildcardAccessAt current root (cutoff W.pointer G.selectedNode)
      .Read tracker.global.protectedTags (position != 0)
    result.status = .Completed ∧ GeneralBorrowExposedNonleafState.ReadFrame current result.location ∧
      LocationCoherent W.allocation.extra result.location tracker.global.protectedTags ∧
      GeneralBorrowLocationSifaConsistency.Profile W.allocation.extra result.location tracker.global.protectedTags ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible W.allocation.extra result.location ∧
      S05SemanticReadEffects.Effects W.allocation.extra current result.location tracker.global.protectedTags ∧
      (∀ query,¬Path W.allocation.extra root query → result.location.perms.get query = current.perms.get query) ∧
      S05CompletedAncestryReadMutable.Authority W.allocation.extra W.precise.completion tracker.global.protectedTags W.pointer.grant result.location := by
  let tree := W.allocation.extra
  let held := tracker.global.protectedTags
  let maximum := cutoff W.pointer G.selectedNode
  obtain ⟨depth⟩ := W.parents.graph.depth
  obtain ⟨forest⟩ := W.parents.graph.forest current held
  have graph := GeneralBorrowExposedScopedReciprocal.of_forest tree current held forest depth
  have old := authorization W G exclusive byte inside segment member lower upper initialProfile initialPossible position root slot callback
  have walkSlots : ∀ index node,tree.nodes.get index = some node → root ∈ GeneralBorrowExposureAncestorFold.walk tree.nodes (tree.nodes.size+1) index → current.perms.get index = segment.data.perms.get index := by
    intro index node present walk
    exact slots index node present (GeneralBorrowWildcardControlWitness.path_of_walk tree depth root index node present _ walk)
  have auth := GeneralBorrowRootLocalAuthorization.authorization tree segment.data current held root position maximum .Read (Path tree root) old walkSlots
  let area : GeneralBorrowWildcardControlStack.Support tree root := ⟨Path tree root,auth.rooted,auth.present,auth.children⟩
  have snapshot := DuplicatePrefixResidualInitialSnapshot.snapshot tree current held root position maximum .Read (Path tree root) auth coherent short
  have plans : Nonempty (GeneralBorrowSnapshotReadDFSPlan.WitnessPlan tree current held root position maximum) := by
    by_cases zero : position = 0
    · subst position
      exact GeneralBorrowSnapshotOrderedPrimaryReadPlan.of_authorization tree current held root maximum (Path tree root)
        W.parents.order depth graph coherent short auth
    · exact ⟨GeneralBorrowSnapshotVirtualReadAccess.plan tree current held root position maximum zero⟩
  obtain ⟨plan⟩ := plans
  let weights := GeneralBorrowWildcardForestWeights.of_forest tree current held forest
  have bound := GeneralBorrowWildcardForestWeights.bounded tree current held forest root
  obtain ⟨done,frame,_,pointwise,cache,outside,runtime,_,transfer,effects⟩ := S05SemanticReadDFS.access true false tree current held root position maximum
    weights bound area snapshot depth coherent plan (fun _ => ⟨profile,possible⟩) (by simp)
  refine ⟨done,frame,cache,(runtime rfl).1,(runtime rfl).2,effects,outside,?_⟩
  intro index node present
  by_cases path : Path tree root index
  · have shape := (G.masked byte inside segment member lower upper .Read position root slot callback index node present path [] (empty_removal _ _ _ _ _)).2
    have framed := GeneralBorrowRootLocalAuthorization.relation_frame tree segment.data current held root index node position maximum .Read []
      (old.covers index path) walkSlots
    have maskEmpty : GeneralBorrowRootLocalAuthorization.componentMask tree root [] = [] := rfl
    rw [maskEmpty] at framed
    rw [←framed,initial_relation tree current held root index node maximum .Read position coherent short] at shape
    constructor
    · intro below
      apply S05ReadRawAuthorityEndpoint.local_right _ _ _ (relation current root index node maximum .Read position) ((rights index node present).1 below)
      · rcases shape.1 below with yes | yes <;> simp [yes]
      · exact transfer index node path present
    · intro notBelow
      apply S05ReadRawAuthorityEndpoint.foreign_right _ _ _ (relation current root index node maximum .Read position) ((rights index node present).2 notBelow)
      · rcases shape.2 notBelow with yes | yes <;> simp [yes]
      · exact transfer index node path present
      · exact effects index node present
      · exact pointwise index node present
      · exact profile.present index node present
      · exact (runtime rfl).2 index node present
  · unfold RawState
    rw [outside index path]
    exact rights index node present

include G exclusive byte inside member lower upper in
/-- Concrete associated Read consumes selected Normal and all callback roots
in production order, retaining the same full mutable source authority. -/
theorem concrete_read
    (concrete : ∃ suppliedId tag,W.pointer.value.provenance = .concrete suppliedId tag)
    (distinct : W.allocation.extra.roots.toList.Nodup)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent W.allocation.extra segment.data tracker.global.protectedTags)
    (short : W.allocation.extra.nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile W.allocation.extra segment.data tracker.global.protectedTags)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible W.allocation.extra segment.data)
    (visit : ChildrenVisitMode) (range : ByteRange) :
    let result := source_tree_access_at W.allocation.extra segment.data (some W.pointer.grant) .Read tracker.global.protectedTags visit range
    source_access_status result = none ∧
      GeneralBorrowExposureCardinality.LocationCoherent W.allocation.extra (source_access_location result) tracker.global.protectedTags ∧
      GeneralBorrowLocationSifaConsistency.Profile W.allocation.extra (source_access_location result) tracker.global.protectedTags ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible W.allocation.extra (source_access_location result) ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Normal W.allocation.extra (source_access_location result) tracker.global.protectedTags W.pointer.grant) ∧
      S05CompletedAncestryReadMutable.Authority W.allocation.extra W.precise.completion tracker.global.protectedTags W.pointer.grant (source_access_location result) := by
  obtain ⟨depth⟩ := W.parents.graph.depth
  obtain ⟨normal⟩ := selected_normal W G exclusive byte inside segment member lower upper profile possible
  obtain ⟨suppliedId,tag,concrete⟩ := concrete
  have cutoffEq : cutoff W.pointer G.selectedNode = some G.selectedNode.tag := by simp [cutoff,concrete]
  apply normal_read W.allocation.extra W.precise.completion segment.data tracker.global.protectedTags
    W.parents.graph distinct G.selectedPosition G.selectedRoot W.pointer.grant G.selectedNode G.sourceNode
    G.selectedSlot G.selectedAt G.sourceAt G.sourcePath normal
    (row_authority W exclusive byte inside segment member lower upper profile possible) G.normalAncestry coherent profile possible
    _ visit range
  intro position root slot different current rights cache currentProfile currentPossible slots
  have callback : Callback W.pointer G.selectedRoot root := Or.inr different
  have actual := framed_callback W G exclusive byte inside segment member lower upper profile possible current rights
    cache short currentProfile currentPossible position root slot callback slots
  rw [cutoffEq] at actual
  exact ⟨actual.1,actual.2.2.1,actual.2.2.2.1,actual.2.2.2.2.1,actual.2.2.2.2.2.2.1,actual.2.2.2.2.2.2.2⟩

private def WildGood (initial : LocationTree) (next : Nat)
    (state : S05WildcardCompletedWrite.State) : Prop :=
  state.2.1 = none ∧
  GeneralBorrowExposureCardinality.LocationCoherent W.allocation.extra state.1 tracker.global.protectedTags ∧
  GeneralBorrowLocationSifaConsistency.Profile W.allocation.extra state.1 tracker.global.protectedTags ∧
  GeneralBorrowSnapshotReadRuntime.GlobalPossible W.allocation.extra state.1 ∧
  S05CompletedAncestryReadMutable.Authority W.allocation.extra W.precise.completion tracker.global.protectedTags W.pointer.grant state.1 ∧
  (∀ position root,next ≤ position → W.allocation.extra.roots[position]? = some root →
    ∀ index node,W.allocation.extra.nodes.get index = some node → Path W.allocation.extra root index →
      state.1.perms.get index = initial.perms.get index)

include G exclusive byte inside member lower upper in
/-- The absent-maximum operation visits EVERY actual root, including the
chosen exposed grant's component. Unvisited component frames transport the
same saved-row geometry; no origin or completion is reselected in the loop. -/
theorem wildcard_read
    (wild : W.pointer.value.provenance = .wildcard)
    (distinct : W.allocation.extra.roots.toList.Nodup)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent W.allocation.extra segment.data tracker.global.protectedTags)
    (short : W.allocation.extra.nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile W.allocation.extra segment.data tracker.global.protectedTags)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible W.allocation.extra segment.data)
    (visit : ChildrenVisitMode) (range : ByteRange) :
    let result := source_tree_access_at W.allocation.extra segment.data none .Read tracker.global.protectedTags visit range
    source_access_status result = none ∧
      GeneralBorrowExposureCardinality.LocationCoherent W.allocation.extra (source_access_location result) tracker.global.protectedTags ∧
      GeneralBorrowLocationSifaConsistency.Profile W.allocation.extra (source_access_location result) tracker.global.protectedTags ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible W.allocation.extra (source_access_location result) ∧
      S05CompletedAncestryReadMutable.Authority W.allocation.extra W.precise.completion tracker.global.protectedTags W.pointer.grant (source_access_location result) := by
  let tree := W.allocation.extra
  let held := tracker.global.protectedTags
  obtain ⟨depth⟩ := W.parents.graph.depth
  have maximum : cutoff W.pointer G.selectedNode = none := by simp [cutoff,wild]
  have step : ∀ position,position < tree.roots.size → ∀ state,
      WildGood W segment.data position state →
      ∃ next,S05WildcardCompletedRead.scan tree held range position state = .yield next ∧
        WildGood W segment.data (position+1) next := by
    intro position valid state good
    rcases state with ⟨location,status,stop⟩
    have statusEq := good.1
    dsimp only at statusEq
    subst status
    by_cases stopped : stop = true
    · subst stop
      refine ⟨(location,none,true),?_,good.1,good.2.1,good.2.2.1,good.2.2.2.1,good.2.2.2.2.1,?_⟩
      · simp [S05WildcardCompletedRead.scan]
      · intro future root later slot index node present path
        exact good.2.2.2.2.2 future root (by omega) slot index node present path
    have noStop : stop = false := by cases stop <;> simp_all
    subst stop
    have slot : tree.roots[position]? = some tree.roots[position] := Array.getElem?_eq_getElem valid
    have callback : Callback W.pointer G.selectedRoot tree.roots[position] := Or.inl wild
    have observed := framed_callback W G exclusive byte inside segment member lower upper profile possible location good.2.2.2.2.1
      good.2.1 short good.2.2.1 good.2.2.2.1 position tree.roots[position] slot callback
      (good.2.2.2.2.2 position _ (Nat.le_refl _) slot)
    have actual := And.intro observed.1 (And.intro observed.2.2.1 (And.intro observed.2.2.2.1
      (And.intro observed.2.2.2.2.1 (And.intro observed.2.2.2.2.2.2.1 observed.2.2.2.2.2.2.2))))
    rw [maximum] at actual
    let result := tree.performWildcardAccessAt location tree.roots[position] none .Read held (position != 0)
    refine ⟨(result.location,none,false),?_,rfl,actual.2.1,actual.2.2.1,actual.2.2.2.1,actual.2.2.2.2.2,?_⟩
    · simp [S05WildcardCompletedRead.scan,slot,actual.1,result,tree,held]
    · intro future root later rootSlot index node present path
      have outside : ¬Path tree tree.roots[position] index := by
        intro currentPath
        obtain ⟨currentNode,currentAt,currentNone⟩ := W.parents.graph.rootNodes tree.roots[position]
          (Array.mem_toList_iff.mpr (Array.mem_of_getElem? slot))
        obtain ⟨futureNode,futureAt,futureNone⟩ := W.parents.graph.rootNodes root
          (Array.mem_toList_iff.mpr (Array.mem_of_getElem? rootSlot))
        have equal := CompletedBorrowAncestry.physical_roots_unique currentAt currentNone futureAt futureNone currentPath path
        have futureData := Array.getElem?_eq_some_iff.mp rootSlot
        have futureValid : future < tree.roots.size := futureData.1
        have positionEq : position = future := by
          apply distinct.getElem_inj.mp
          change tree.roots[position] = tree.roots[future]
          exact equal.trans futureData.2.symm
        omega
      rw [actual.2.2.2.2.1 index outside]
      exact good.2.2.2.2.2 future root (by omega) rootSlot index node present path
  have run : ∀ count start,count+start ≤ tree.roots.size → ∀ state,
      WildGood W segment.data start state →
      WildGood W segment.data (start+count)
        (forIn (List.range' start count) state (S05WildcardCompletedRead.scan tree held range) : Id S05WildcardCompletedWrite.State) := by
    intro count
    induction count with
    | zero => intro start bound state good;simpa only [List.range'_zero,List.forIn_nil,pure,Nat.add_zero] using good
    | succ count ih =>
      intro start bound state good
      rw [List.range'_succ,List.forIn_cons]
      obtain ⟨next,actual,after⟩ := step start (by omega) state good
      simp only [actual,bind]
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (start+1) (by omega) next after
  have loop := run tree.roots.size 0 (by omega) (segment.data,none,false)
    ⟨rfl,coherent,profile,possible,row_authority W exclusive byte inside segment member lower upper profile possible,(by intros;rfl)⟩
  have final := And.intro loop.1 (And.intro loop.2.1 (And.intro loop.2.2.1 (And.intro loop.2.2.2.1 loop.2.2.2.2.1)))
  dsimp only
  simp_tree_helpers
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  change (forIn (List.range' 0 tree.roots.size) (segment.data,none,false) _ : Id S05WildcardCompletedWrite.State).2.1 = none ∧ _
  suffices same : (forIn (List.range' 0 tree.roots.size) (segment.data,none,false) _ : Id S05WildcardCompletedWrite.State) =
      (forIn (List.range' 0 tree.roots.size) (segment.data,none,false) (S05WildcardCompletedRead.scan tree held range) : Id S05WildcardCompletedWrite.State) by
    rw [same];exact final
  apply GeneralBorrowVirtualRootsAdapter.forIn_congr
  intro position member state
  rcases state with ⟨location,status,stop⟩
  cases rootSlot : tree.roots[position]? with
  | none => cases visit <;> simp [S05WildcardCompletedRead.scan,rootSlot,Id.run,pure]
  | some root =>
    cases tagLookup : (tree.nodes.get root).map TreeNode.tag <;> cases visit <;> simp [S05WildcardCompletedRead.scan,rootSlot,tagLookup,Id.run,pure,tree,held]


include G exclusive in
/-- Materialized/split range rows are handled by the production range fold;
the SAME grant and parent interpretation survive every actual selected row. -/
theorem concrete_range
    (concrete : ∃ suppliedId tag,W.pointer.value.provenance = .concrete suppliedId tag)
    (distinct : W.allocation.extra.roots.toList.Nodup)
    (short : W.allocation.extra.nodes.size < 65536)
    (well : W.allocation.extra.locations.WellFormed)
    (runtime : Every (fun location => GeneralBorrowExposureCardinality.LocationCoherent W.allocation.extra location tracker.global.protectedTags ∧
      GeneralBorrowLocationSifaConsistency.Profile W.allocation.extra location tracker.global.protectedTags ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible W.allocation.extra location) W.allocation.extra.locations)
    (request len : Size) (lo hi : UInt64)
    (windowLower : offset ≤ lo.toNat) (windowUpper : hi.toNat ≤ offset+length)
    (bounds : request.bytes.toNat + len.bytes.toNat ≤ W.allocation.extra.locations.size.bytes.toNat)
    (requestLower : lo.toNat ≤ request.bytes.toNat) (requestUpper : (request.bytes+len.bytes).toNat ≤ hi.toNat)
    (visit : ChildrenVisitMode) :
    GeneralBorrowConcreteRangeInvariant.Contract W.allocation.extra
      (S05CompletedAncestryReadMutable.Authority W.allocation.extra W.precise.completion tracker.global.protectedTags W.pointer.grant)
      (fun location => GeneralBorrowExposureCardinality.LocationCoherent W.allocation.extra location tracker.global.protectedTags ∧
        GeneralBorrowLocationSifaConsistency.Profile W.allocation.extra location tracker.global.protectedTags ∧
        GeneralBorrowSnapshotReadRuntime.GlobalPossible W.allocation.extra location)
      (fun _ _ => True) lo hi
      (W.allocation.extra.performBorrowAccessRange (.concrete G.sourceNode.tag) request len .Read tracker.global.protectedTags visit) := by
  have owned : OwnedOn (SavedRow W) lo hi W.allocation.extra.locations := by
    intro position valid positive beforeUpper afterLower
    have segmentPositive := (GeneralRangeMapGeometry.facts W.allocation.extra.locations well (by omega)).2.1 position valid
    have member : W.allocation.extra.locations.entries[position] ∈ W.allocation.extra.locations.entries.toList :=
      Array.mem_toList_iff.mpr (Array.getElem_mem valid)
    by_cases earlier : lo.toNat ≤ W.allocation.extra.locations.entries[position].range.start.toNat
    · refine ⟨(id,W.allocation.extra.locations.entries[position].range.start.toNat),?_,_,member,Nat.le_refl _,segmentPositive,rfl⟩
      exact ⟨rfl,by omega,by omega⟩
    · refine ⟨(id,lo.toNat),?_,_,member,?_,afterLower,rfl⟩
      · exact ⟨rfl,windowLower,by omega⟩
      · omega
  have initial : ∀ location,SavedRow W location →
      S05CompletedAncestryReadMutable.Authority W.allocation.extra W.precise.completion tracker.global.protectedTags W.pointer.grant location := by
    intro location saved
    obtain ⟨byte,inside,segment,member,lower,upper,rfl⟩ := saved
    have valid := List.mem_iff_getElem.mp member
    obtain ⟨position,positionValid,segmentEq⟩ := valid
    have atRuntime := runtime position (by simpa using positionValid)
    have rowRuntime : GeneralBorrowExposureCardinality.LocationCoherent W.allocation.extra segment.data tracker.global.protectedTags ∧
        GeneralBorrowLocationSifaConsistency.Profile W.allocation.extra segment.data tracker.global.protectedTags ∧
        GeneralBorrowSnapshotReadRuntime.GlobalPossible W.allocation.extra segment.data := by
      simpa only [Array.getElem_toList] using (segmentEq ▸ atRuntime)
    exact row_authority W exclusive byte inside segment member lower upper rowRuntime.2.1 rowRuntime.2.2
  have mapped := W.parents.graph.allocator.nodeTags W.pointer.grant G.sourceNode G.sourceAt
  apply GeneralBorrowConcreteRangeEntry.access W.allocation.extra tracker.global.protectedTags G.sourceNode.tag W.pointer.grant mapped request len
    .Read visit (SavedRow W) _ _ (fun _ _ => True) initial (fun _ => True.intro) _ lo hi owned well runtime bounds requestLower requestUpper
  intro location saved rowRuntime range
  obtain ⟨byte,inside,segment,member,lower,upper,rfl⟩ := saved
  have actual := concrete_read W G exclusive byte inside segment member lower upper concrete distinct rowRuntime.1 short rowRuntime.2.1 rowRuntime.2.2 visit range
  exact ⟨actual.1,actual.2.2.2.2.2,⟨actual.2.1,actual.2.2.1,actual.2.2.2.1⟩,True.intro⟩

include G exclusive in
/-- Wildcard range access uses the actual absent maximum at EVERY root on
each materialized row, preserving the SAME issued grant and interpretation. -/
theorem wildcard_range
    (wild : W.pointer.value.provenance = .wildcard)
    (distinct : W.allocation.extra.roots.toList.Nodup)
    (short : W.allocation.extra.nodes.size < 65536)
    (well : W.allocation.extra.locations.WellFormed)
    (runtime : Every (fun location => GeneralBorrowExposureCardinality.LocationCoherent W.allocation.extra location tracker.global.protectedTags ∧
      GeneralBorrowLocationSifaConsistency.Profile W.allocation.extra location tracker.global.protectedTags ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible W.allocation.extra location) W.allocation.extra.locations)
    (request len : Size) (lo hi : UInt64)
    (windowLower : offset ≤ lo.toNat) (windowUpper : hi.toNat ≤ offset+length)
    (bounds : request.bytes.toNat + len.bytes.toNat ≤ W.allocation.extra.locations.size.bytes.toNat)
    (requestLower : lo.toNat ≤ request.bytes.toNat) (requestUpper : (request.bytes+len.bytes).toNat ≤ hi.toNat)
    (visit : ChildrenVisitMode) :
    GeneralBorrowConcreteRangeInvariant.Contract W.allocation.extra
      (S05CompletedAncestryReadMutable.Authority W.allocation.extra W.precise.completion tracker.global.protectedTags W.pointer.grant)
      (fun location => GeneralBorrowExposureCardinality.LocationCoherent W.allocation.extra location tracker.global.protectedTags ∧
        GeneralBorrowLocationSifaConsistency.Profile W.allocation.extra location tracker.global.protectedTags ∧
        GeneralBorrowSnapshotReadRuntime.GlobalPossible W.allocation.extra location)
      (fun _ _ => True) lo hi
      (W.allocation.extra.performBorrowAccessRange .wildcard request len .Read tracker.global.protectedTags visit) := by
  have owned : OwnedOn (SavedRow W) lo hi W.allocation.extra.locations := by
    intro position valid positive beforeUpper afterLower
    have segmentPositive := (GeneralRangeMapGeometry.facts W.allocation.extra.locations well (by omega)).2.1 position valid
    have member : W.allocation.extra.locations.entries[position] ∈ W.allocation.extra.locations.entries.toList :=
      Array.mem_toList_iff.mpr (Array.getElem_mem valid)
    by_cases earlier : lo.toNat ≤ W.allocation.extra.locations.entries[position].range.start.toNat
    · refine ⟨(id,W.allocation.extra.locations.entries[position].range.start.toNat),?_,_,member,Nat.le_refl _,segmentPositive,rfl⟩
      exact ⟨rfl,by omega,by omega⟩
    · refine ⟨(id,lo.toNat),?_,_,member,?_,afterLower,rfl⟩
      · exact ⟨rfl,windowLower,by omega⟩
      · omega
  have initial : ∀ location,SavedRow W location →
      S05CompletedAncestryReadMutable.Authority W.allocation.extra W.precise.completion tracker.global.protectedTags W.pointer.grant location := by
    intro location saved
    obtain ⟨byte,inside,segment,member,lower,upper,rfl⟩ := saved
    have valid := List.mem_iff_getElem.mp member
    obtain ⟨position,positionValid,segmentEq⟩ := valid
    have atRuntime := runtime position (by simpa using positionValid)
    have rowRuntime : GeneralBorrowExposureCardinality.LocationCoherent W.allocation.extra segment.data tracker.global.protectedTags ∧
        GeneralBorrowLocationSifaConsistency.Profile W.allocation.extra segment.data tracker.global.protectedTags ∧
        GeneralBorrowSnapshotReadRuntime.GlobalPossible W.allocation.extra segment.data := by
      simpa only [Array.getElem_toList] using (segmentEq ▸ atRuntime)
    exact row_authority W exclusive byte inside segment member lower upper rowRuntime.2.1 rowRuntime.2.2
  apply GeneralBorrowConcreteRangeEntry.access_resolved W.allocation.extra tracker.global.protectedTags .wildcard none rfl request len
    .Read visit (SavedRow W) _ _ (fun _ _ => True) initial (fun _ => True.intro) _ lo hi owned well runtime bounds requestLower requestUpper
  intro location saved rowRuntime range
  obtain ⟨byte,inside,segment,member,lower,upper,rfl⟩ := saved
  have actual := wildcard_read W G exclusive byte inside segment member lower upper wild distinct rowRuntime.1 short rowRuntime.2.1 rowRuntime.2.2 visit range
  exact ⟨actual.1,actual.2.2.2.2,⟨actual.2.1,actual.2.2.1,actual.2.2.2.1⟩,True.intro⟩

include G exclusive in
/-- One actual all-provenance Read range consumer. The concrete tag is the
input pointer's tag (proved equal to its fixed grant node), and wildcard uses
maximum NONE. No total completion or caller authorization is a premise. -/
theorem read_range
    (distinct : W.allocation.extra.roots.toList.Nodup)
    (short : W.allocation.extra.nodes.size < 65536)
    (well : W.allocation.extra.locations.WellFormed)
    (runtime : Every (fun location => GeneralBorrowExposureCardinality.LocationCoherent W.allocation.extra location tracker.global.protectedTags ∧
      GeneralBorrowLocationSifaConsistency.Profile W.allocation.extra location tracker.global.protectedTags ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible W.allocation.extra location) W.allocation.extra.locations)
    (request len : Size) (lo hi : UInt64)
    (windowLower : offset ≤ lo.toNat) (windowUpper : hi.toNat ≤ offset+length)
    (bounds : request.bytes.toNat + len.bytes.toNat ≤ W.allocation.extra.locations.size.bytes.toNat)
    (requestLower : lo.toNat ≤ request.bytes.toNat) (requestUpper : (request.bytes+len.bytes).toNat ≤ hi.toNat)
    (visit : ChildrenVisitMode) :
    GeneralBorrowConcreteRangeInvariant.Contract W.allocation.extra
      (S05CompletedAncestryReadMutable.Authority W.allocation.extra W.precise.completion tracker.global.protectedTags W.pointer.grant)
      (fun location => GeneralBorrowExposureCardinality.LocationCoherent W.allocation.extra location tracker.global.protectedTags ∧
        GeneralBorrowLocationSifaConsistency.Profile W.allocation.extra location tracker.global.protectedTags ∧
        GeneralBorrowSnapshotReadRuntime.GlobalPossible W.allocation.extra location)
      (fun _ _ => True) lo hi
      (W.allocation.extra.performBorrowAccessRange (match W.pointer.value.provenance with | .concrete _ tag => .concrete tag | .wildcard => .wildcard) request len .Read tracker.global.protectedTags visit) := by
  cases provenance : W.pointer.value.provenance with
  | wildcard =>
    simpa only [provenance] using wildcard_range W G exclusive provenance distinct short well runtime request len lo hi
      windowLower windowUpper bounds requestLower requestUpper visit
  | concrete suppliedId tag =>
    obtain ⟨node,present,mapped,bound⟩ := W.binding
    have same : node = G.sourceNode := Option.some.inj (present.symm.trans G.sourceAt)
    subst node
    rw [provenance] at bound
    have tagEq : tag = G.sourceNode.tag := bound.2
    simpa only [provenance,tagEq] using concrete_range W G exclusive ⟨suppliedId,tag,provenance⟩ distinct short well runtime
      request len lo hi windowLower windowUpper bounds requestLower requestUpper visit

include G exclusive in
/-- The actual Read tree retains its optional parent interpretation and full
runtime representation, ready for the real child constructor. This does not
assert a current-world installation or issue a new family before construction. -/
theorem read_range_runtime
    (distinct : W.allocation.extra.roots.toList.Nodup)
    (short : W.allocation.extra.nodes.size < 65536)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (request len : Size) (lo hi : UInt64)
    (windowLower : offset ≤ lo.toNat) (windowUpper : hi.toNat ≤ offset+length)
    (bounds : request.bytes.toNat + len.bytes.toNat ≤ W.allocation.extra.locations.size.bytes.toNat)
    (requestLower : lo.toNat ≤ request.bytes.toNat) (requestUpper : (request.bytes+len.bytes).toNat ≤ hi.toNat)
    (visit : ChildrenVisitMode) :
    let result := W.allocation.extra.performBorrowAccessRange
      (match W.pointer.value.provenance with | .concrete _ tag => .concrete tag | .wildcard => .wildcard)
      request len .Read tracker.global.protectedTags visit
    result.status = .Completed ∧ DuplicatePrefixBorrowContract.RuntimeFacts result.tree tracker.global ∧
      ParentInterpretation result.tree W.precise.completion ∧
      OwnedOn (S05CompletedAncestryReadMutable.Authority result.tree W.precise.completion tracker.global.protectedTags W.pointer.grant)
        lo hi result.tree.locations ∧
      result.tree.nodes = W.allocation.extra.nodes ∧ result.tree.roots = W.allocation.extra.roots ∧
      result.tree.tagMapping = W.allocation.extra.tagMapping ∧ result.tree.locations.size = W.allocation.extra.locations.size := by
  let result := W.allocation.extra.performBorrowAccessRange
    (match W.pointer.value.provenance with | .concrete _ tag => .concrete tag | .wildcard => .wildcard)
    request len .Read tracker.global.protectedTags visit
  have contract := read_range W G exclusive distinct short runtime.formed.well
    (fun cursor valid => ⟨runtime.coherent cursor valid,runtime.formed.profile cursor valid,runtime.possible cursor valid⟩)
    request len lo hi windowLower windowUpper bounds requestLower requestUpper visit
  have afterRuntime : DuplicatePrefixBorrowContract.RuntimeFacts result.tree tracker.global := by
    rw [contract.tree_eq]
    refine ⟨⟨⟨GeneralBorrowStructuralHistoryState.graph_locations W.allocation.extra _ runtime.formed.toGraphState,contract.well⟩,?_⟩,
      ?_,?_,⟨runtime.below.mapping,runtime.below.protectors⟩⟩
    · intro cursor valid
      exact ⟨(contract.runtime cursor valid).2.1.present,(contract.runtime cursor valid).2.1.vacant⟩
    · intro cursor valid
      exact (contract.runtime cursor valid).1
    · intro cursor valid
      exact (contract.runtime cursor valid).2.2
  have parents : ParentInterpretation result.tree W.precise.completion := by
    rw [contract.tree_eq]
    refine ⟨GeneralBorrowStructuralHistoryState.graph_locations W.allocation.extra _ W.parents.graph,
      W.parents.order,W.parents.dimension,W.parents.physical,W.parents.edgeLive,W.parents.primaryNone,?_⟩
    intro position root slot origin edge
    obtain ⟨earlier,originRoot,rootNode,originNode,before,rootSlot,rootAt,originAt,exposed,older,path⟩ := W.parents.virtual position root slot origin edge
    exact ⟨earlier,originRoot,rootNode,originNode,before,rootSlot,rootAt,originAt,exposed,older,
      GeneralBorrowPrimaryWitnessVisibility.path_nodes (before := {W.allocation.extra with locations := result.tree.locations}) (after := W.allocation.extra) rfl path⟩
  refine ⟨contract.completed,afterRuntime,parents,?_,contract.nodes,contract.roots,contract.tags,contract.capacity⟩
  intro cursor valid positive start stop index node present
  exact contract.rows cursor valid positive start stop index node (by rw [←contract.nodes];exact present)

end
end DuplicatePrefix.CurrentCallResourceRead

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallResourceRead.").length != 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved current resource Read dependency {dependency}"
