import duplicate_prefix.CurrentCallResourceNormalization
import duplicate_prefix.CurrentCallEmptyEntryWriteRetention
import duplicate_prefix.CurrentCallEmptyEntryNormalWrite
import duplicate_prefix.CurrentCallEmptyEntryRepairedRowFrame
import duplicate_prefix.GeneralBorrowConcreteRangeEntry
import duplicate_prefix.S05WildcardCompletedWrite

/-! Actual callback consumption of the candidate's SAME finite grant and parent
interpretation. Runtime coherence/profile/counter bounds remain execution data.
This is not Ordinary adoption or constructor/copy/GC adequacy. -/
namespace DuplicatePrefix.CurrentCallResourceAccess
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.DataStructures
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources OrdinaryBorrowAuthority
open CurrentCallResourceNormalization GeneralBorrowExposedNonleafPrimaryPath
open GeneralBorrowExposureCardinality DuplicatePrefixResidualSupportAuthorization
open DuplicatePrefixCallbackAuthorization GeneralBorrowProjection GeneralBorrowForest
open GeneralRangeMapOrigins GeneralRangeMapState
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 65536
noncomputable section

private theorem normal_of_authority (tree : BorrowTree) (completion : Completion) (initial : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (fits : tree.nodes.data.size ≤ 4294967296)
    (position : Nat) (root source : UniIndex) (rootNode : TreeNode)
    (rootSlot : tree.roots[position]? = some root) (rootPresent : tree.nodes.get root = some rootNode)
    (sourcePath : Path tree root source)
    (classification : ∀ index node, tree.nodes.get index = some node → Path tree root index →
      (Below completion index source ↔ Path tree index source))
    (localRights : ∀ index node, tree.nodes.get index = some node → Path tree root index →
      Below completion index source → LocalWrite
        ((initial.perms.get index).getD node.defaultLocationState) (protections.contains node.tag))
    (foreignRights : ∀ index node, tree.nodes.get index = some node → Path tree root index →
      ¬Below completion index source → ForeignWrite
        ((initial.perms.get index).getD node.defaultLocationState) (protections.contains node.tag)) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree initial protections source) := by
  obtain ⟨actual,found,parentless⟩ := formed.rootNodes root (Array.mem_toList_iff.mpr (Array.mem_of_getElem? rootSlot))
  have same : actual = rootNode := Option.some.inj (found.symm.trans rootPresent)
  subst actual
  obtain ⟨forest⟩ := formed.forest initial protections
  let topology := (source_normal_projection tree initial protections).topology
  have projectedPath := GeneralBorrowPhysicalRootPath.projection_desc tree initial protections root source sourcePath
  have rootValid : root.toNat < topology.nodes.size := projectedPath.valid.1
  have projectedRoot := projection_topology_node tree initial protections root.toNat root rootNode rfl rootPresent
  change (topology.nodes[root.toNat]?.getD ⟨none,[]⟩) = _ at projectedRoot
  have rootShape : topology.nodes[root.toNat] =
      ⟨rootNode.parent.map UniIndex.toNat,rootNode.children.toList.map UniIndex.toNat⟩ := by
    simpa only [Array.getElem?_eq_getElem rootValid,Option.getD_some] using projectedRoot
  have rootParentless : (topology.nodes[root.toNat]'rootValid).parent = none := by
    rw [rootShape];simp only [parentless,Option.map_none]
  let chosen := GeneralBorrowExposedScopedNormalRoot.component topology forest root.toNat source.toNat
    rootValid rootParentless projectedPath
  refine ⟨⟨chosen,?_⟩⟩
  intro kind slot inside _
  change Desc topology root.toNat slot at inside
  obtain ⟨index,node,indexEq,present,path⟩ := GeneralBorrowProjectedDescPath.desc_path tree initial protections fits
    root rootNode rootPresent slot inside
  obtain ⟨sourceNode,sourcePresent⟩ := sourcePath.present
  let state := (initial.perms.get index).getD node.defaultLocationState
  refine ⟨state,?_,?_⟩
  · rw [←indexEq]
    exact projection_state tree initial protections index.toNat index node (index_self index) rfl present
  · rw [←indexEq,GeneralBorrowNormalPermissionMetadata.held tree initial protections index node present]
    have physical := classification index node present path
    have related := GeneralBorrowProjectedDescPath.relation_local_iff tree initial protections fits depth forest
      source index sourceNode node sourcePresent present
    by_cases localPath : Path tree index source
    · rw [related.mpr localPath]
      exact OrdinaryBorrowAuthorityBridge.local_scalar state _ (localRights index node present path (physical.mpr localPath)) kind
    · have foreignRelation : GeneralBorrowAnchor.relation (source_normal_projection tree initial protections)
          source.toNat index.toNat = .ForeignAccess := by
        cases relation : GeneralBorrowAnchor.relation (source_normal_projection tree initial protections) source.toNat index.toNat with
        | LocalAccess => exact False.elim (localPath (related.mp relation))
        | ForeignAccess => rfl
      rw [foreignRelation]
      have raw := foreignRights index node present path (fun below => localPath (physical.mp below))
      obtain ⟨next,delta,success,_⟩ := S05RawAuthorityStepPreservation.foreign_step state _ kind raw
      exact (DuplicatePrefixScalarAuthorization.compatible_iff state kind .ForeignAccess _ raw.1).mpr ⟨next,delta,success⟩


variable {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode) (G : Geometry W)
    (exclusive : demandOf mode = .exclusive)
    (byte : AllocId × Nat) (inside : Window id offset length byte)
    (segment : RangeMapSegment LocationTree)
    (member : segment ∈ W.allocation.extra.locations.entries.toList)
    (lower : segment.range.start.toNat ≤ byte.2) (upper : byte.2 < segment.range.stop.toNat)

include exclusive byte inside member lower upper in
/-- Scalar rights are derived from the SAME byte embedding and realized current
permissions, rather than supplied as a second ownership interpretation. -/
theorem row_authority
    (profile : GeneralBorrowLocationSifaConsistency.Profile W.allocation.extra segment.data tracker.global.protectedTags)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible W.allocation.extra segment.data) :
    S05CompletedAncestryReadMutable.Authority W.allocation.extra W.precise.completion tracker.global.protectedTags
      W.pointer.grant segment.data := by
  have embedding := (W.window byte inside).2
  rw [exclusive] at embedding
  have resources := embedding segment member lower upper
  intro index node present
  have realized := CandidateCurrentGrantRuntime.realized _ _ (possible index node present) (profile.present index node present)
  obtain ⟨owned,guards⟩ := resources index node present
  constructor
  · intro below
    exact local_write _ _ realized (token_local _ _ (owned below))
  · intro outside
    exact foreign_write _ _ realized (no_clash_competing _ _ _ realized (fun clash => outside (guards clash)))

include exclusive byte inside member lower upper in
/-- Repaired callback clauses are derived for every legal removal mask from
normalization geometry on this actual stored row. -/
theorem authorization
    (profile : GeneralBorrowLocationSifaConsistency.Profile W.allocation.extra segment.data tracker.global.protectedTags)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible W.allocation.extra segment.data)
    (position : Nat) (root : UniIndex) (slot : W.allocation.extra.roots[position]? = some root)
    (callback : Callback W.pointer G.selectedRoot root) :
    DuplicatePrefixResidualWriteRepaired.Authorization W.allocation.extra segment.data tracker.global.protectedTags
      root position (cutoff W.pointer G.selectedNode) .Write (Path W.allocation.extra root) := by
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
  · intro beforeMask afterMask _ legal _ query node path present _
    have shape := (G.masked byte inside segment member lower upper .Write position root slot callback
      query node present path afterMask legal).2
    by_cases below : Below W.precise.completion query W.pointer.grant
    · have raw := (rights query node present).1 below
      rcases shape.1 below with localQuery | eitherQuery
      · rw [localQuery]
        apply DuplicatePrefixCallbackVisitAuthorizationRepaired.old_inclusion
        exact ⟨raw.1,Or.inr ⟨by simp [skip, AccessRelatedness.isForeign],OrdinaryBorrowAuthorityBridge.local_scalar _ _ raw .Write⟩⟩
      · rw [eitherQuery]
        exact .inl ⟨raw.1,Or.inr trivial⟩
    · have raw := (rights query node present).2 below
      rcases shape.2 below with foreignQuery | eitherQuery
      · rw [foreignQuery]
        exact S05RawForeignAuthorizationBridge.foreign_write_authorized _ _ _ (profile.present query node present) raw
      · rw [eitherQuery]
        exact .inl ⟨raw.1,Or.inr trivial⟩
  · intro zero
    have atZero : W.allocation.extra.roots[0]? = some root := by simpa only [zero] using slot
    have primaryEq : root = allocationRoot := Option.some.inj (atZero.symm.trans W.issued.capability.rootSlot)
    subst root
    obtain ⟨witness,node,present,eligible,path,_⟩ := G.primarySupport byte inside segment member lower upper .Write callback
    exact ⟨witness,node,path,present,eligible⟩

include exclusive byte inside member lower upper in
/-- Actual production DFS, with its plan, authorization, and full retained
source authority all derived internally. This is a callback, not a new caller
validity definition; selected-component Normal/range composition follows it. -/
theorem write_callback
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent W.allocation.extra segment.data tracker.global.protectedTags)
    (short : W.allocation.extra.nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile W.allocation.extra segment.data tracker.global.protectedTags)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible W.allocation.extra segment.data)
    (position : Nat) (root : UniIndex) (slot : W.allocation.extra.roots[position]? = some root)
    (callback : Callback W.pointer G.selectedRoot root) :
    let result := W.allocation.extra.performWildcardAccessAt segment.data root (cutoff W.pointer G.selectedNode)
      .Write tracker.global.protectedTags (position != 0)
    result.status = .Completed ∧
      GeneralBorrowExposureCardinality.LocationCoherent W.allocation.extra result.location tracker.global.protectedTags ∧
      GeneralBorrowLocationSifaConsistency.Profile W.allocation.extra result.location tracker.global.protectedTags ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible W.allocation.extra result.location ∧
      (∀ query,¬Path W.allocation.extra root query → result.location.perms.get query = segment.data.perms.get query) ∧
      S05CompletedAncestryReadMutable.Authority W.allocation.extra W.precise.completion tracker.global.protectedTags W.pointer.grant result.location := by
  obtain ⟨depth⟩ := W.parents.graph.depth
  apply CurrentCallEmptyEntryWriteRetention.root W.allocation.extra segment.data tracker.global.protectedTags
    W.parents.graph W.parents.order depth root position (cutoff W.pointer G.selectedNode) (Path W.allocation.extra root)
    (authorization W G exclusive byte inside segment member lower upper profile possible position root slot callback)
    coherent short profile possible W.precise.completion W.pointer.grant
  · intro removed legal query node path present
    exact (G.masked byte inside segment member lower upper .Write position root slot callback query node present path removed legal).2
  · exact row_authority W exclusive byte inside segment member lower upper profile possible

include G exclusive byte inside member lower upper in
/-- The selected physical component is justified by the same issued grant and
ordinary physical ancestry, with no exposed supporter required for root0. -/
theorem selected_normal
    (profile : GeneralBorrowLocationSifaConsistency.Profile W.allocation.extra segment.data tracker.global.protectedTags)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible W.allocation.extra segment.data) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Normal W.allocation.extra segment.data tracker.global.protectedTags W.pointer.grant) := by
  obtain ⟨depth⟩ := W.parents.graph.depth
  have rights := row_authority W exclusive byte inside segment member lower upper profile possible
  apply normal_of_authority W.allocation.extra W.precise.completion segment.data tracker.global.protectedTags
    W.parents.graph depth W.parents.graph.fits G.selectedPosition G.selectedRoot W.pointer.grant G.selectedNode
    G.selectedSlot G.selectedAt G.sourcePath G.normalAncestry
  · intro index node present _ below
    exact (rights index node present).1 below
  · intro index node present _ outside
    exact (rights index node present).2 outside

include G exclusive byte inside member lower upper in
/-- Concrete production row access: selected Normal and every other-root DFS
are consumed in their actual order. Legal-mask geometry follows each unchanged
unvisited component, while SAME full grant authority follows the real updates. -/
theorem concrete_write
    (concrete : ∃ suppliedId tag,W.pointer.value.provenance = .concrete suppliedId tag)
    (distinct : W.allocation.extra.roots.toList.Nodup)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent W.allocation.extra segment.data tracker.global.protectedTags)
    (short : W.allocation.extra.nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile W.allocation.extra segment.data tracker.global.protectedTags)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible W.allocation.extra segment.data)
    (visit : ChildrenVisitMode) (range : ByteRange) :
    let result := source_tree_access_at W.allocation.extra segment.data (some W.pointer.grant) .Write tracker.global.protectedTags visit range
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
  apply CurrentCallEmptyEntryNormalWrite.write_authority W.allocation.extra W.precise.completion segment.data tracker.global.protectedTags
    W.parents.graph distinct G.selectedPosition G.selectedRoot W.pointer.grant G.selectedNode G.sourceNode
    G.selectedSlot G.selectedAt G.sourceAt G.sourcePath normal
    (row_authority W exclusive byte inside segment member lower upper profile possible) G.normalAncestry coherent profile possible
    _ visit range
  intro position root slot different current rights cache currentProfile currentPossible slots
  have callback : Callback W.pointer G.selectedRoot root := Or.inr different
  have auth := authorization W G exclusive byte inside segment member lower upper profile possible position root slot callback
  have transported := CurrentCallEmptyEntryRepairedRowFrame.queries W.allocation.extra segment.data current tracker.global.protectedTags
    depth root position (cutoff W.pointer G.selectedNode) .Write (Path W.allocation.extra root) auth slots
    W.precise.completion W.pointer.grant (by
      intro removed legal query node path present
      exact (G.masked byte inside segment member lower upper .Write position root slot callback query node present path removed legal).2)
  have actual := CurrentCallEmptyEntryWriteRetention.root W.allocation.extra current tracker.global.protectedTags
    W.parents.graph W.parents.order depth root position (cutoff W.pointer G.selectedNode) (Path W.allocation.extra root)
    transported.1 cache short currentProfile currentPossible W.precise.completion W.pointer.grant transported.2 rights
  simpa only [cutoffEq] using actual

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
theorem wildcard_write
    (wild : W.pointer.value.provenance = .wildcard)
    (distinct : W.allocation.extra.roots.toList.Nodup)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent W.allocation.extra segment.data tracker.global.protectedTags)
    (short : W.allocation.extra.nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile W.allocation.extra segment.data tracker.global.protectedTags)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible W.allocation.extra segment.data)
    (visit : ChildrenVisitMode) (range : ByteRange) :
    let result := source_tree_access_at W.allocation.extra segment.data none .Write tracker.global.protectedTags visit range
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
      ∃ next,S05WildcardCompletedWrite.scan tree held range position state = .yield next ∧
        WildGood W segment.data (position+1) next := by
    intro position valid state good
    rcases state with ⟨location,status,stop⟩
    have statusEq := good.1
    dsimp only at statusEq
    subst status
    by_cases stopped : stop = true
    · subst stop
      refine ⟨(location,none,true),?_,good.1,good.2.1,good.2.2.1,good.2.2.2.1,good.2.2.2.2.1,?_⟩
      · simp [S05WildcardCompletedWrite.scan]
      · intro future root later slot index node present path
        exact good.2.2.2.2.2 future root (by omega) slot index node present path
    have noStop : stop = false := by cases stop <;> simp_all
    subst stop
    have slot : tree.roots[position]? = some tree.roots[position] := Array.getElem?_eq_getElem valid
    have callback : Callback W.pointer G.selectedRoot tree.roots[position] := Or.inl wild
    have old := authorization W G exclusive byte inside segment member lower upper profile possible position tree.roots[position] slot callback
    have transferred := CurrentCallEmptyEntryRepairedRowFrame.queries tree segment.data location held depth
      tree.roots[position] position (cutoff W.pointer G.selectedNode) .Write (Path tree tree.roots[position]) old
      (good.2.2.2.2.2 position _ (Nat.le_refl _) slot) W.precise.completion W.pointer.grant (by
        intro removed legal query node path present
        exact (G.masked byte inside segment member lower upper .Write position _ slot callback query node present path removed legal).2)
    have actual := CurrentCallEmptyEntryWriteRetention.root tree location held W.parents.graph W.parents.order depth
      tree.roots[position] position (cutoff W.pointer G.selectedNode) (Path tree tree.roots[position]) transferred.1
      good.2.1 short good.2.2.1 good.2.2.2.1 W.precise.completion W.pointer.grant transferred.2 good.2.2.2.2.1
    rw [maximum] at actual
    let result := tree.performWildcardAccessAt location tree.roots[position] none .Write held (position != 0)
    refine ⟨(result.location,none,false),?_,rfl,actual.2.1,actual.2.2.1,actual.2.2.2.1,actual.2.2.2.2.2,?_⟩
    · simp [S05WildcardCompletedWrite.scan,slot,actual.1,result]
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
        (forIn (List.range' start count) state (S05WildcardCompletedWrite.scan tree held range) : Id S05WildcardCompletedWrite.State) := by
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
      (forIn (List.range' 0 tree.roots.size) (segment.data,none,false) (S05WildcardCompletedWrite.scan tree held range) : Id S05WildcardCompletedWrite.State) by
    rw [same];exact final
  apply GeneralBorrowVirtualRootsAdapter.forIn_congr
  intro position member state
  rcases state with ⟨location,status,stop⟩
  cases rootSlot : tree.roots[position]? with
  | none => cases visit <;> simp [S05WildcardCompletedWrite.scan,rootSlot,Id.run,pure]
  | some root =>
    cases tagLookup : (tree.nodes.get root).map TreeNode.tag <;> cases visit <;> simp [S05WildcardCompletedWrite.scan,rootSlot,tagLookup,Id.run,pure,tree,held]

/-- An actual saved row overlapping this ONE fixed whole-window assignment.
The byte is overlap evidence; it does not select a new grant, family, or C. -/
def SavedRow (location : LocationTree) : Prop :=
  ∃ byte,Window id offset length byte ∧ ∃ segment,segment ∈ W.allocation.extra.locations.entries.toList ∧
    segment.range.start.toNat ≤ byte.2 ∧ byte.2 < segment.range.stop.toNat ∧ location = segment.data

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
      (W.allocation.extra.performBorrowAccessRange (.concrete G.sourceNode.tag) request len .Write tracker.global.protectedTags visit) := by
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
    .Write visit (SavedRow W) _ _ (fun _ _ => True) initial (fun _ => True.intro) _ lo hi owned well runtime bounds requestLower requestUpper
  intro location saved rowRuntime range
  obtain ⟨byte,inside,segment,member,lower,upper,rfl⟩ := saved
  have actual := concrete_write W G exclusive byte inside segment member lower upper concrete distinct rowRuntime.1 short rowRuntime.2.1 rowRuntime.2.2 visit range
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
      (W.allocation.extra.performBorrowAccessRange .wildcard request len .Write tracker.global.protectedTags visit) := by
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
    .Write visit (SavedRow W) _ _ (fun _ _ => True) initial (fun _ => True.intro) _ lo hi owned well runtime bounds requestLower requestUpper
  intro location saved rowRuntime range
  obtain ⟨byte,inside,segment,member,lower,upper,rfl⟩ := saved
  have actual := wildcard_write W G exclusive byte inside segment member lower upper wild distinct rowRuntime.1 short rowRuntime.2.1 rowRuntime.2.2 visit range
  exact ⟨actual.1,actual.2.2.2.2,⟨actual.2.1,actual.2.2.1,actual.2.2.2.1⟩,True.intro⟩

include G exclusive in
/-- One actual all-provenance Write range consumer. The concrete tag is the
input pointer's tag (proved equal to its fixed grant node), and wildcard uses
maximum NONE. No total completion or caller authorization is a premise. -/
theorem write_range
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
      (W.allocation.extra.performBorrowAccessRange (match W.pointer.value.provenance with | .concrete _ tag => .concrete tag | .wildcard => .wildcard) request len .Write tracker.global.protectedTags visit) := by
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

end
end DuplicatePrefix.CurrentCallResourceAccess

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallResourceAccess.").length != 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved current resource access dependency {dependency}"
