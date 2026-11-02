import duplicate_prefix.CurrentCallEmptyEntryNormalWrite
import duplicate_prefix.GeneralBorrowCompatibleScopedNormalMetadata
import duplicate_prefix.GeneralBorrowWriteActivationUnique
import duplicate_prefix.GeneralBorrowFreshActiveWithinAccess
import duplicate_prefix.GeneralRangeMapCoverage

/-! The actual Boolchild local Write activates its reserved permission. Exact
selected-column framing retains that state through the production root scan. -/
namespace DuplicatePrefix.CurrentCallEmptyEntryWriteKind
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowExposedNonleafPrimaryPath OrdinaryBorrowAuthority
open GeneralBorrowWildcardParentTagOrder GeneralBorrowExposureCardinality GeneralBorrowProjection
open GeneralBorrowConcreteRowCutoffAccess (State scan)
open DuplicatePrefix.BorrowRangeAccess GeneralBorrowEvents
open GeneralRangeMapState GeneralRangeMapOrigins
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem normal_unique (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (source : UniIndex) (sourceNode : TreeNode) (sourcePresent : tree.nodes.get source = some sourceNode)
    (normal : DuplicatePrefixBorrowAuthorization.Normal tree initial protections source)
    (reserved : (RawState initial source sourceNode).permission = .ReservedFrz false)
    (mode : ChildrenVisitMode) :
    ∃ state, (tree.performNormalAccessAt initial source .Write protections mode).location.perms.get source = some state ∧
      state.permission = .Unique := by
  obtain ⟨forest⟩ := formed.forest initial protections
  obtain ⟨depth⟩ := formed.depth
  let projection := source_normal_projection tree initial protections
  let schedule := projection.topology.traverse source.toNat mode (sourceNormalSkipped projection .Write)
  have geometry := GeneralBorrowExposedScopedNormalMetadata.valid_aligned tree initial protections source sourceNode sourcePresent
  have size : projection.topology.nodes.size = tree.nodes.data.size := by
    unfold projection;unfold_general_projection;unfold_general_topology;simp only [Array.size_map]
  have owned : GeneralBorrowCompatibleScopedNormal.Owned projection source.toNat .Write normal.component := by
    intro index included valid
    exact normal.permissions .Write index included (by rw [size] at valid;exact valid)
  have completed := GeneralBorrowCompatibleScopedNormal.normal projection source.toNat .Write mode forest geometry.1 geometry.2 normal.component owned
  have visited := GeneralBorrowStorage.events_visited schedule.2 schedule.1 .Write projection completed
  change (projection.performAccess source.toNat .Write mode).visited = schedule.2 at visited
  have member : (⟨source.toNat,.LocalAccess⟩ : TraversalEvent) ∈ (projection.performAccess source.toNat .Write mode).visited := by
    rw [visited]
    have head : schedule.2.head? = some ⟨source.toNat,.LocalAccess⟩ :=
      TraversalTree.traverse_starts_at_accessed_node projection.topology source.toNat mode (sourceNormalSkipped projection .Write)
    cases found : schedule.2 with
    | nil => simp only [found,List.head?_nil] at head;cases head
    | cons event rest =>
      have same : event = ⟨source.toNat,.LocalAccess⟩ := Option.some.inj (by simpa only [found,List.head?_cons] using head)
      simp only [same,List.mem_cons,true_or]
  have metadata := GeneralBorrowCompatibleScopedNormalMetadata.metadata tree initial protections source .Write mode forest
    normal.component owned depth formed.children sourceNode sourcePresent
  obtain ⟨facts⟩ := metadata.2 ⟨source.toNat,.LocalAccess⟩ member
  have indexEq : facts.index = source := Option.some.inj (facts.converted.symm.trans (index_self source))
  have oldPresent := facts.oldPresent
  rw [indexEq] at oldPresent
  have sourceAt : tree.nodeAt source = some sourceNode := sourcePresent
  have oldEq : facts.oldState = RawState initial source sourceNode := by
    simpa only [BorrowTree.locationStateAt,sourceAt,bind,pure,Option.bind_some,Option.some.injEq,RawState] using oldPresent.symm
  have localTransition : performAccessTransition .Write .LocalAccess (.ReservedFrz false) (protections.contains facts.node.tag) =
      .Transition ⟨.ReservedFrz false,.Unique⟩ := by
    cases protections.contains facts.node.tag <;> rfl
  have performed := facts.performed
  rw [oldEq,reserved,localTransition] at performed
  have transitionEq : facts.transition = ⟨.ReservedFrz false,.Unique⟩ :=
    (PermTransitionOutcome.Transition.inj performed).symm
  have unique : facts.newState.permission = .Unique := by rw [←facts.finalEndpoint,transitionEq]
  have stored := GeneralBorrowNormalStoredWriteback.stored tree initial protections source facts.index .Write mode facts.newState facts.finalStored
  rw [indexEq] at stored
  exact ⟨facts.newState,stored,unique⟩

theorem write_unique (tree : BorrowTree) (completion : Completion) (initial : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree) (distinct : tree.roots.toList.Nodup)
    (selectedPosition : Nat) (selected source : UniIndex) (selectedNode sourceNode : TreeNode)
    (selectedSlot : tree.roots[selectedPosition]? = some selected)
    (selectedPresent : tree.nodes.get selected = some selectedNode) (sourcePresent : tree.nodes.get source = some sourceNode)
    (sourcePath : Path tree selected source)
    (normal : DuplicatePrefixBorrowAuthorization.Normal tree initial protections source)
    (reserved : (RawState initial source sourceNode).permission = .ReservedFrz false)
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
      let result := tree.performWildcardAccessAt current root (some selectedNode.tag) .Write protections (position != 0)
      result.status = .Completed ∧ LocationCoherent tree result.location protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
      (∀ query,¬Path tree root query → result.location.perms.get query = current.perms.get query) ∧
      S05CompletedAncestryReadMutable.Authority tree completion protections source result.location)
    (mode : ChildrenVisitMode) (range : ByteRange) :
    let result := source_tree_access_at tree initial (some source) .Write protections mode range
    source_access_status result = none ∧ LocationCoherent tree (source_access_location result) protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree (source_access_location result) protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree (source_access_location result) ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree (source_access_location result) protections source) ∧
      S05CompletedAncestryReadMutable.Authority tree completion protections source (source_access_location result) ∧
      ∃ state, (source_access_location result).perms.get source = some state ∧ state.permission = .Unique := by
  obtain ⟨depth⟩ := formed.depth
  obtain ⟨forest⟩ := formed.forest initial protections
  obtain ⟨actual,actualAt,parentless⟩ := formed.rootNodes selected (Array.mem_toList_iff.mpr (Array.mem_of_getElem? selectedSlot))
  have actualEq : actual = selectedNode := Option.some.inj (actualAt.symm.trans selectedPresent)
  subst actual
  have rootPath := S05CompletedAncestryNormal.root_path tree initial protections formed selected source selectedNode selectedPresent parentless sourcePath
  have normalDone := DuplicatePrefixNormalKind.access tree initial protections source .Write mode
    (DuplicatePrefixNormalKind.of_normal tree initial protections source normal .Write) formed sourceNode sourcePresent coherent
  have fits : tree.nodes.data.size ≤ 4294967296 := formed.fits
  have owned : GeneralBorrowCompatibleScopedNormal.Owned (source_normal_projection tree initial protections) source.toNat .Write normal.component := by
    intro index inside valid
    have sizes : (source_normal_projection tree initial protections).topology.nodes.size = tree.nodes.data.size := by
      unfold_general_projection;unfold_general_topology;simp only [Array.size_map]
    exact normal.permissions .Write index inside (by rw [←sizes];exact valid)
  have afterProfile := (GeneralBorrowCompatibleLocationSifaConsistency.normal tree initial protections source .Write mode
    fits depth formed.children sourceNode sourcePresent forest normal.component owned profile).2.2
  have afterPossible := GeneralBorrowCompatibleNormalPossible.normal tree initial protections source .Write mode fits forest
    (GeneralBorrowExposedScopedNormalMetadata.valid_aligned tree initial protections source sourceNode sourcePresent).1 normal possible
  have frame : ∀ (position : Nat) (root : UniIndex),tree.roots[position]? = some root → root ≠ selected →
      ∀ index node,tree.nodes.get index = some node → Path tree root index →
      (tree.performNormalAccessAt initial source .Write protections mode).location.perms.get index = initial.perms.get index := by
    intro position root rootAt different index node present path
    have member := Array.mem_toList_iff.mpr (Array.mem_of_getElem? rootAt)
    exact (GeneralBorrowNormalOtherRootFrame.access tree initial protections formed source selected root sourceNode sourcePresent normal rootPath member
      (Ne.symm different) .Write coherent mode).2.2.2 index node present path
  have currentNormal := DuplicatePrefixNormalAuthorizationPreservation.normal_preserves tree initial protections source .Write mode fits forest
    (GeneralBorrowExposedScopedNormalMetadata.valid_aligned tree initial protections source sourceNode sourcePresent).1 normal
  obtain ⟨currentNormal⟩ := currentNormal
  have currentAuthority : S05CompletedAncestryReadMutable.Authority tree completion protections source
      (tree.performNormalAccessAt initial source .Write protections mode).location := by
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
      S05CompletedAncestryReadMutable.Authority tree completion protections source row) (some selectedNode.tag) .Write
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
    (tree.performNormalAccessAt initial source .Write protections mode).location ⟨⟨currentNormal⟩,currentAuthority⟩ normalDone.2.2 afterProfile afterPossible frame
  obtain ⟨sourceState,normalStored,unique⟩ := normal_unique tree initial protections formed source sourceNode sourcePresent normal reserved mode
  have finalUnique : ∃ state, (forIn (List.range' 0 tree.roots.size)
      ((tree.performNormalAccessAt initial source .Write protections mode).location,none,false)
      (scan tree selected (some selectedNode.tag)
        (if mode == .SkipChildrenOfAccessed then source_min_exposed tree source else none) .Write protections mode range) : Id State).1.perms.get source = some state ∧ state.permission = .Unique := by
    exact ⟨sourceState,(final.2.2.2.2.1 source sourceNode sourcePresent sourcePath).trans normalStored,unique⟩
  have ending : ((source_normal_projection tree initial protections).topology.ancestorPath source.toNat).getLast! = selected.toNat := by
    rw [List.getLast!_eq_getLast?_getD,rootPath];rfl
  have rootEq : (tree.performNormalAccessAt initial source .Write protections mode).access.root = selected.toNat :=
    (GeneralBorrowStorage.events_root _ _ .Write (source_normal_projection tree initial protections)).trans ending
  dsimp only
  simp_tree_helpers
  simp only [normalDone.1,normalDone.2.1,rootEq,GeneralBorrowProjection.index_self,Option.bind_some,selectedPresent,Option.map_some]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  simpa only [GeneralBorrowConcreteRowCutoffAccess.scan,Id.run,bind,pure] using
    (show _ from ⟨final.1,final.2.1,final.2.2.1,final.2.2.2.1,final.2.2.2.2.2.1,final.2.2.2.2.2.2,finalUnique⟩)


/-- The only associated access of an active stored source state is Write. -/
def WriteOnly (source : UniIndex) (location : LocationTree) : Prop :=
  ∀ state, location.perms.get source = some state → state.accessed = true →
    ∀ kind, state.permission.associatedAccess = some kind → kind = .Write

private abbrev RangeState := DedupRangeMap LocationTree × Array BorrowTree.BorrowTreeLocationResult × BorrowTree.BorrowTreeAccessStatus

/-- Actual range composition consumes successful Unique-producing callbacks
on the saved segments. The FnEntry consumer derives them from write_unique;
initially active reserved states inside the window need not be WriteOnly. -/
theorem range_write_kind (tree : BorrowTree) (protections : ProtectedTags)
    (tag : BorTag) (source : UniIndex) (mapped : tree.indexOfTag tag = some source)
    (offset len : Size) (mode : ChildrenVisitMode)
    (well : tree.locations.WellFormed)
    (bounds : offset.bytes.toNat + len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree source .Write offset.bytes (offset.bytes+len.bytes))
    (callback : ∀ cursor (valid : cursor < (tree.locations.iterMut offset len).segments.size),
      let segment := (tree.locations.iterMut offset len).segments[cursor]'valid
      let accessed := source_tree_access_at tree segment.data (some source) .Write protections mode segment.range
      source_access_status accessed = none ∧
        ∃ state, (source_access_location accessed).perms.get source = some state ∧ state.permission = .Unique) :
    let result := tree.performBorrowAccessRange (.concrete tag) offset len .Write protections mode
    result.status = .Completed ∧ Every (WriteOnly source) result.tree.locations := by
  classical
  let prepared := tree.locations.iterMut offset len
  have origins := GeneralRangeMapOriginPrepare.iter_mut tree.locations offset len well bounds
  have good := origins.1
  have preparedActive := GeneralBorrowFreshActiveWithin.refines tree.locations prepared.state origins.2.1
    source .Write offset.bytes (offset.bytes+len.bytes) active
  let Safe (remaining : List Nat) (state : RangeState) : Prop :=
    state.2.2 = .Completed ∧ state.1.entries.size = prepared.state.entries.size ∧
      ∀ position (valid : position < state.1.entries.size), WriteOnly source (state.1.entries[position]'valid).data ∨
        ∃ cursor, cursor ∈ remaining ∧ prepared.positions[cursor]? = some position
  have initial : Safe (List.range' 0 prepared.positions.size) (prepared.state,#[],.Completed) := by
    refine ⟨rfl,rfl,?_⟩
    intro position valid
    change position < prepared.state.entries.size at valid
    by_cases pending : ∃ cursor, cursor ∈ List.range' 0 prepared.positions.size ∧ prepared.positions[cursor]? = some position
    · exact Or.inr pending
    · left
      intro state stored accessed kind associated
      have positive := (GeneralRangeMapGeometry.facts prepared.state good.wellFormed (by omega)).2.1 position valid
      have interval := preparedActive (prepared.state.entries[position]'valid).range.start
        (prepared.state.entries[position]'valid).data ⟨position,valid,Nat.le_refl _,positive,rfl⟩ state stored accessed kind associated
      have windowPositive : offset.bytes.toNat < (offset.bytes+len.bytes).toNat := Nat.lt_of_le_of_lt interval.1 interval.2.1
      have beforeStop : offset.bytes.toNat < (prepared.state.entries[position]'valid).range.stop.toNat := by omega
      obtain ⟨cursor,bounded,same⟩ := GeneralRangeMapCoverage.overlap_selected tree.locations offset len well bounds
        windowPositive position valid interval.2.1 beforeStop
      have cursorBound : cursor < prepared.positions.size := bounded
      apply False.elim
      apply pending
      refine ⟨cursor,List.mem_range'_1.mpr ⟨Nat.zero_le _,by simpa only [Nat.zero_add] using cursorBound⟩,?_⟩
      rw [Array.getElem?_eq_getElem bounded,same]
  unfold BorrowTree.performBorrowAccessRange
  simp only [mapped,Option.isNone_some,Bool.false_eq_true,↓reduceIte,Id.run,bind,pure,good.outcome]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  name_borrow_range_scan
  have run : ∀ cursors : List Nat, (∀ cursor ∈ cursors, cursor < prepared.positions.size) →
      ∀ state : RangeState, Safe cursors state → Safe [] (forIn cursors state scan : Id RangeState) := by
    intro cursors
    induction cursors with
    | nil => intro _ state safe;simpa only [List.forIn_nil,pure] using safe
    | cons cursor rest ih =>
      intro valid state safe
      rcases state with ⟨current,visited,status⟩
      have completed := safe.1
      dsimp only at completed
      subst status
      have cursorBound := valid cursor (by simp)
      have segmentBound : cursor < prepared.segments.size := by rw [←good.lengths];exact cursorBound
      let position := prepared.positions[cursor]'cursorBound
      let segment := prepared.segments[cursor]'segmentBound
      obtain ⟨positionBound,selected⟩ := good.selected cursor cursorBound
      have currentBound : position < current.entries.size := by rw [safe.2.1];exact positionBound
      let accessed := source_tree_access_at tree segment.data (some source) .Write protections mode segment.range
      obtain ⟨done,sourceState,stored,unique⟩ := callback cursor segmentBound
      have rowKind : WriteOnly source (source_access_location accessed) := by
        intro state stateAt _ kind associated
        have same : state = sourceState := Option.some.inj (stateAt.symm.trans stored)
        subst state
        simpa only [unique,Permission.associatedAccess,Option.some.injEq] using associated.symm
      let next : RangeState := (replaced current position currentBound (source_access_location accessed),
        visited.push ⟨segment.range,source_access_normal accessed⟩,.Completed)
      have positionLookup : (tree.locations.iterMut offset len).positions[cursor]? = some position := Array.getElem?_eq_getElem cursorBound
      have segmentLookup : (tree.locations.iterMut offset len).segments[cursor]? = some segment := Array.getElem?_eq_getElem segmentBound
      have doneAt : source_access_status (source_tree_access_at tree segment.data (some source) .Write protections mode segment.range) = none := done
      have actual : scan cursor (current,visited,.Completed) = .yield next := by
        simp only [scan,beq_self_eq_true,↓reduceIte,positionLookup,segmentLookup,setAtPos_exact current position currentBound,doneAt]
        rfl
      have nextSafe : Safe rest next := by
        refine ⟨rfl,(replaced_length current position currentBound _).trans safe.2.1,?_⟩
        intro query queryBound
        have oldBound : query < current.entries.size := by simpa only [next,replaced_length] using queryBound
        by_cases same : query = position
        · subst query
          left
          simpa only [next,replaced,Array.getElem_set_self] using rowKind
        · have dataSame : (replaced current position currentBound (source_access_location accessed)).entries[query].data = current.entries[query].data := by
            simp [replaced,Array.getElem_set,Ne.symm same]
          rcases safe.2.2 query oldBound with quiet | ⟨later,inRemaining,lookup⟩
          · left
            change WriteOnly source (replaced current position currentBound (source_access_location accessed)).entries[query].data
            rw [dataSame]
            exact quiet
          · right
            rcases List.mem_cons.mp inRemaining with first | laterMember
            · subst later
              have equal : position = query := Option.some.inj (positionLookup.symm.trans lookup)
              exact False.elim (same equal.symm)
            · exact ⟨later,laterMember,lookup⟩
      rw [List.forIn_cons,actual]
      simp only [bind]
      exact ih (fun later member => valid later (by simp [member])) next nextSafe
  have final := run (List.range' 0 prepared.positions.size)
    (fun cursor member => by have bound := List.mem_range'_1.mp member;omega) (prepared.state,#[],.Completed) initial
  refine ⟨final.1,?_⟩
  intro position valid
  rcases final.2.2 position valid with quiet | ⟨cursor,impossible,_⟩
  · exact quiet
  · cases impossible

end DuplicatePrefix.CurrentCallEmptyEntryWriteKind
