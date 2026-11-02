import duplicate_prefix.GeneralBorrowRange
import duplicate_prefix.GeneralBorrowOwnership
namespace DuplicatePrefix.GeneralBorrowRangePreserves
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess GeneralBorrowProjection GeneralBorrowExposure GeneralRangeMapState
open GeneralBorrowPermissions GeneralBorrowEvents
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

/-- The abstract normal visitor preserves the same anchor's data ownership.
This is the source normal operation, not yet the ranged map/write-back bridge. -/
theorem normal_owned_as (tree : NormalTreeState)
    (forest : GeneralBorrowForest.Forest tree.topology) (anchor : Nat)
    (kind ownerKind : AccessKind) (mode : ChildrenVisitMode)
    (allowed : ownerKind = .Read → kind = .Read)
    (owned : GeneralBorrowAnchor.AnchorOwned tree anchor ownerKind) :
    GeneralBorrowAnchor.AnchorOwned (tree.performAccess anchor kind mode).tree anchor ownerKind := by
  let writable := fun (_ : Nat) => ownerKind == .Write
  have pointwise : GeneralBorrowOwnership.Pointwise tree writable (GeneralBorrowAnchor.relation tree anchor) := by
    intro position valid
    obtain ⟨state,present,permitted⟩ := owned.permissions position (by rw [←owned.locationsAligned];exact valid)
    refine ⟨state,present,?_⟩
    cases ownerKind <;> exact permitted
  have preserved := GeneralBorrowOwnership.normal_preserves tree forest anchor owned.anchorValid kind mode
    writable owned.locationsAligned pointwise (by
      intro index valid notWritable localAccess
      cases ownerKind with
      | Read => exact allowed rfl
      | Write => simp [writable] at notWritable)
  have storage : GeneralBorrowStorage.SameStorage tree (tree.performAccess anchor kind mode).tree :=
    GeneralBorrowStorage.events_storage
      (tree.topology.traverse anchor mode (sourceNormalSkipped tree kind)).2
      (tree.topology.traverse anchor mode (sourceNormalSkipped tree kind)).1 kind tree
  refine ⟨?_,?_,?_,?_⟩
  · rw [storage.1]
    exact owned.anchorValid
  · rw [storage.2.2.2,storage.1]
    exact owned.locationsAligned
  · rw [storage.2.1,storage.1]
    exact owned.defaultsAligned
  · intro position valid
    have validLocation : position < (tree.performAccess anchor kind mode).tree.locationStates.size := by
      rw [storage.2.2.2,owned.locationsAligned]
      rw [storage.1] at valid
      exact valid
    obtain ⟨state,present,permitted⟩ := preserved.2 position validLocation
    refine ⟨state,present,?_⟩
    have relationSame : GeneralBorrowAnchor.relation (tree.performAccess anchor kind mode).tree anchor position =
        GeneralBorrowAnchor.relation tree anchor position := by
      unfold GeneralBorrowAnchor.relation
      rw [storage.1]
    rw [relationSame]
    cases ownerKind <;> exact permitted


theorem normal_owned (tree : NormalTreeState)
    (forest : GeneralBorrowForest.Forest tree.topology) (anchor : Nat)
    (kind : AccessKind) (mode : ChildrenVisitMode)
    (owned : GeneralBorrowAnchor.AnchorOwned tree anchor kind) :
    GeneralBorrowAnchor.AnchorOwned (tree.performAccess anchor kind mode).tree anchor kind :=
  normal_owned_as tree forest anchor kind kind mode (fun same => same) owned

/-- Normal processing only materializes optional states; it never clears a
previously stored state back to a lazy default. -/
theorem events_none_before (events : List TraversalEvent) (root : Nat) (kind : AccessKind)
    (tree : NormalTreeState) (position : Nat)
    (empty : (sourceNormalEvents tree root kind events).tree.locationStates[position]? = some none) :
    tree.locationStates[position]? = some none := by
  induction events generalizing tree with
  | nil => exact empty
  | cons event rest ih =>
    cases present : tree.stateAt event.node with
    | none => unfold_storage_events; simpa only [present] using empty
    | some state =>
      cases record : state.recordNewAccess kind event.relatedness with
      | DebugAssertion => unfold_storage_events; simpa only [present,record] using empty
      | Recorded recorded =>
        cases access : recorded.performAccess kind event.relatedness (tree.protectedNodes.contains event.node) <;>
          by_cases valid : event.node < tree.locationStates.size
        all_goals unfold_storage_events
        all_goals simp only [present,record,access,valid,↓reduceDIte,LocationState.AccessResult.resultingState] at empty
        all_goals first
          | exact empty
          | have stored := ih _ empty
            by_cases same : event.node = position
            · subst position; simp at stored
            · simpa only [Array.getElem?_set,ite_eq_right same] using stored
          | by_cases same : event.node = position
            · subst position; simp at empty
            · simpa only [Array.getElem?_set,ite_eq_right same] using empty

theorem normal_none_before (tree : NormalTreeState) (anchor : Nat) (kind : AccessKind)
    (mode : ChildrenVisitMode) (position : Nat)
    (empty : (tree.performAccess anchor kind mode).tree.locationStates[position]? = some none) :
    tree.locationStates[position]? = some none :=
  events_none_before _ _ kind tree position empty

/-- The real optional-value insertion's lookup law, including vector extension.
Extending absent slots introduces only None, so other indices are unaffected. -/
theorem insert_get {α : Type} (map : UniValMap α) (index query : UniIndex) (value : α) :
    (map.insert index value).get query = if query = index then some value else map.get query := by
  have bounded : index.toNat < (UniValMap.extendTo map.data (index.toNat+1)).size := by
    simp only [UniValMap.extendTo,Array.size_append,Array.size_replicate]
    omega
  have sameNat : index.toNat = query.toNat ↔ query = index := by
    constructor
    · intro same
      cases index with | mk old => cases query with | mk new =>
        exact congrArg UniIndex.mk (UInt32.toNat_inj.mp same.symm)
    · intro same; subst query; rfl
  simp only [UniValMap.insert,Id.run,pure,bounded,↓reduceDIte,UniValMap.get,Array.getElem?_set]
  by_cases same : query = index
  · subst query; simp
  · simp only [sameNat,ite_eq_right same]
    unfold UniValMap.extendTo
    by_cases inside : query.toNat < map.data.size
    · rw [Array.getElem?_append_left inside]
    · rw [Array.getElem?_append_right (by omega)]
      rw [Array.getElem?_eq_none (xs := map.data) (i := query.toNat) (by omega)]
      simp only [Array.getElem?_replicate]
      by_cases extra : query.toNat-map.data.size < index.toNat+1-map.data.size <;> simp only [extra,↓reduceIte]

private def writeState (states : Array (Option LocationState)) (position : Nat) (location : LocationTree) : LocationTree :=
  match states[position]? with
  | some (some state) =>
      match UniIndex.ofNat? position with
      | some index => {location with perms := location.perms.insert index state}
      | none => location
  | _ => location

private def writeStates (location : LocationTree) (states : Array (Option LocationState)) : LocationTree := Id.run do
  let mut current := location
  for position in [:states.size] do
    match states[position]? with
    | some (some state) =>
        match UniIndex.ofNat? position with
        | some index => current := {current with perms := current.perms.insert index state}
        | none => pure ()
    | _ => pure ()
  return current

private theorem writeState_get (states : Array (Option LocationState)) (position : Nat)
    (location : LocationTree) (query : UniIndex) :
    (writeState states position location).perms.get query =
      if position = query.toNat then (states[position]?.getD none).or (location.perms.get query)
      else location.perms.get query := by
  unfold writeState
  cases stored : states[position]? with
  | none => simp [stored]
  | some row =>
    cases row with
    | none => simp [stored]
    | some state =>
      cases converted : UniIndex.ofNat? position with
      | none =>
        have different : position ≠ query.toNat := by
          intro same
          subst position
          rw [index_self] at converted
          cases converted
        simp [stored,converted,different]
      | some index =>
        have eqNat : index.toNat = position := by
          unfold UniIndex.ofNat? at converted
          split at converted
          · cases converted
            simp only [UniIndex.toNat,UInt32.toNat_ofNat']
            omega
          · cases converted
        have same : query = index ↔ position = query.toNat := by
          constructor
          · intro same; subst query; exact eqNat.symm
          · intro equal
            cases query with | mk q => cases index with | mk i =>
              exact congrArg UniIndex.mk (UInt32.toNat_inj.mp (equal.symm.trans eqNat.symm))
        simp only [insert_get,same,Option.getD_some]
        rfl



private def writeScan (states : Array (Option LocationState)) (position : Nat) (location : LocationTree) : Id (ForInStep LocationTree) :=
  match states[position]? with
  | some (some state) =>
      match UniIndex.ofNat? position with
      | some index => .yield {location with perms := location.perms.insert index state}
      | none => .yield location
  | _ => .yield location

private theorem writeScan_eq (states : Array (Option LocationState)) (position : Nat) (location : LocationTree) :
    writeScan states position location = .yield (writeState states position location) := by
  unfold writeScan writeState
  cases states[position]? with
  | none => rfl
  | some row => cases row with
    | none => rfl
    | some state => cases UniIndex.ofNat? position <;> rfl

private theorem writeList_get (items : List Nat) (states : Array (Option LocationState))
    (location : LocationTree) (query : UniIndex) :
    (forIn items location (writeScan states)).perms.get query =
      if query.toNat ∈ items then (states[query.toNat]?.getD none).or (location.perms.get query)
      else location.perms.get query := by
  induction items generalizing location with
  | nil => simp only [List.forIn_nil,pure,List.not_mem_nil,ite_false]
  | cons position rest ih =>
    rw [List.forIn_cons,writeScan_eq]
    change (forIn rest (writeState states position location) (writeScan states)).perms.get query = _
    rw [ih,writeState_get]
    by_cases same : position = query.toNat
    · subst position
      simp only [eq_self_iff_true,ite_true,List.mem_cons,true_or]
      cases saved : states[query.toNat]?.getD none <;>
        by_cases contains : query.toNat ∈ rest <;> simp [saved,contains,Option.or]
    · simp only [same,ite_false,List.mem_cons,Ne.symm same,false_or]

/-- The source materialization loop agrees pointwise with its optional-state
array, retaining old values only when that array leaves a lazy None entry. -/
private theorem writeStates_get (location : LocationTree) (states : Array (Option LocationState))
    (query : UniIndex) (valid : query.toNat < states.size) :
    (writeStates location states).perms.get query =
      (states[query.toNat]?.getD none).or (location.perms.get query) := by
  unfold writeStates
  simp only [Id.run,bind,pure,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  change (forIn (List.range' 0 states.size) location (writeScan states)).perms.get query = _
  rw [writeList_get]
  have member : query.toNat ∈ List.range' 0 states.size := List.mem_range'_1.mpr ⟨by omega,by simpa using valid⟩
  simp only [member,ite_true]



/-- The actual exposed-cache loop following normal-state materialization never
changes permission-map data, on successful or failing cache outcomes. -/
private theorem normal_location_perms (tree : BorrowTree) (location : LocationTree)
    (protections : ProtectedTags) (anchor : UniIndex) (kind : AccessKind) (mode : ChildrenVisitMode) :
    (tree.performNormalAccessAt location anchor kind protections mode).location.perms =
      (writeStates location ((source_normal_projection tree location protections).performAccess anchor.toNat kind mode).tree.locationStates).perms := by
  unfold BorrowTree.performNormalAccessAt
  simp only [Id.run,bind,pure,ForIn.forIn]
  name_normal_cache_scan
  let property := fun state : LocationTree × Except ExposedCacheError Unit =>
    state.1.perms = (writeStates location
      ((source_normal_projection tree location protections).performAccess anchor.toNat kind mode).tree.locationStates).perms
  have step : ∀ event member state, property state → property (scan event member state).value := by
    intro event member state good
    dsimp only [property] at good ⊢
    simp only [scan]
    repeat' first | exact good | split
  have initial : property (writeStates location
      ((source_normal_projection tree location protections).performAccess anchor.toNat kind mode).tree.locationStates,.ok ()) := rfl
  exact GeneralBorrowLoop.list_invariant' _ scan property step _ initial



private theorem projection_cell (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (position : Nat) (index : UniIndex)
    (valid : position < (source_normal_projection tree location protections).locationStates.size)
    (converted : UniIndex.ofNat? position = some index) :
    (source_normal_projection tree location protections).locationStates[position]'valid = location.perms.get index := by
  have bounded : position < tree.nodes.data.size := by
    rw [(projection_sizes tree location protections).1] at valid
    exact valid
  apply Option.some.inj
  rw [←Array.getElem?_eq_getElem valid]
  unfold_general_projection
  rw [Array.getElem?_mapIdx,Array.getElem?_eq_getElem bounded]
  simp only [Option.map_some,converted]

private theorem normal_ext (before after : NormalTreeState)
    (topology : before.topology = after.topology) (defaults : before.defaultStates = after.defaultStates)
    (protectedNodes : before.protectedNodes = after.protectedNodes)
    (locations : before.locationStates = after.locationStates) : before = after := by
  cases before
  cases after
  cases topology
  cases defaults
  cases protectedNodes
  cases locations
  rfl

/-- Reprojecting the actual materialized permission map recovers the source
normal result exactly. The u32 vector bound is an input-data condition; cache
outcome success is neither needed nor assumed for this representation fact. -/
theorem normal_projection (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (kind : AccessKind) (mode : ChildrenVisitMode)
    (fits : tree.nodes.data.size ≤ 4294967296) :
    source_normal_projection tree (tree.performNormalAccessAt location anchor kind protections mode).location protections =
      ((source_normal_projection tree location protections).performAccess anchor.toNat kind mode).tree := by
  let initial := source_normal_projection tree location protections
  let normal := initial.performAccess anchor.toNat kind mode
  let next := (tree.performNormalAccessAt location anchor kind protections mode).location
  have storage : GeneralBorrowStorage.SameStorage initial normal.tree :=
    GeneralBorrowStorage.events_storage
      (initial.topology.traverse anchor.toNat mode (sourceNormalSkipped initial kind)).2
      (initial.topology.traverse anchor.toNat mode (sourceNormalSkipped initial kind)).1 kind initial
  have afterSize : normal.tree.locationStates.size = tree.nodes.data.size :=
    storage.2.2.2.trans (projection_sizes tree location protections).1
  have postSize : (source_normal_projection tree next protections).locationStates.size = tree.nodes.data.size :=
    (projection_sizes tree next protections).1
  have cells : (source_normal_projection tree next protections).locationStates = normal.tree.locationStates := by
    apply Array.ext
    · exact postSize.trans afterSize.symm
    · intro position left right
      have bounded : position < tree.nodes.data.size := by rw [←postSize];exact left
      obtain ⟨index,converted,indexEq⟩ := index_nat position (by omega)
      have oldValid : position < initial.locationStates.size := by
        rw [(projection_sizes tree location protections).1]
        exact bounded
      have postCell := projection_cell tree next protections position index left converted
      have normalValid : index.toNat < normal.tree.locationStates.size := by rw [indexEq];exact right
      have written : next.perms.get index =
          (normal.tree.locationStates[position]?.getD none).or (location.perms.get index) := by
        change (tree.performNormalAccessAt location anchor kind protections mode).location.perms.get index = _
        rw [normal_location_perms,writeStates_get location normal.tree.locationStates index normalValid,indexEq]
      rw [postCell,written]
      cases current : normal.tree.locationStates[position]'right with
      | some state => simp [Array.getElem?_eq_getElem right,current,Option.or]
      | none =>
        have notCleared : initial.locationStates[position]? = some none :=
          normal_none_before initial anchor.toNat kind mode position (by
            rw [Array.getElem?_eq_getElem right,current])
        have oldCell := projection_cell tree location protections position index oldValid converted
        have oldEmpty : location.perms.get index = none := by
          rw [Array.getElem?_eq_getElem oldValid,oldCell] at notCleared
          exact Option.some.inj notCleared
        simp [Array.getElem?_eq_getElem right,current,oldEmpty,Option.or]
  apply normal_ext
  · exact storage.1.symm
  · exact storage.2.1.symm
  · exact storage.2.2.1.symm
  · exact cells

/-- The actual per-location normal access preserves the same anchor's ownership,
including permission-map write-back and exposed-cache processing. -/
theorem normal_location_owned (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (kind : AccessKind) (mode : ChildrenVisitMode)
    (fits : tree.nodes.data.size ≤ 4294967296)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (owned : GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree location protections) anchor.toNat kind) :
    GeneralBorrowAnchor.AnchorOwned
      (source_normal_projection tree (tree.performNormalAccessAt location anchor kind protections mode).location protections)
      anchor.toNat kind := by
  rw [normal_projection tree location protections anchor kind mode fits]
  exact normal_owned _ forest anchor.toNat kind mode owned



/-- A read may retain the stronger mutable ownership required by a later
reborrow. A merely readable anchor may only perform a read. -/
theorem normal_location_owned_as (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (kind ownerKind : AccessKind) (mode : ChildrenVisitMode)
    (allowed : ownerKind = .Read → kind = .Read)
    (fits : tree.nodes.data.size ≤ 4294967296)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (owned : GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree location protections) anchor.toNat ownerKind) :
    GeneralBorrowAnchor.AnchorOwned
      (source_normal_projection tree (tree.performNormalAccessAt location anchor kind protections mode).location protections)
      anchor.toNat ownerKind := by
  rw [normal_projection tree location protections anchor kind mode fits]
  exact normal_owned_as _ forest anchor.toNat kind ownerKind mode allowed owned

/-- Mutable pointwise permission implies its read-only counterpart. -/
theorem write_readable (state : LocationState) (related : AccessRelatedness) (held : Bool)
    (owned : AccessOwned state .Write related held) : AccessOwned state .Read related held := by
  cases related with
  | ForeignAccess => exact owned
  | LocalAccess =>
    refine ⟨owned.1,?_⟩
    intro disabled
    simp [AccessOwned,Owned,LocalOwned,disabled] at owned

theorem owned_for_access (tree : NormalTreeState) (anchor : Nat) (kind ownerKind : AccessKind)
    (allowed : ownerKind = .Read → kind = .Read)
    (owned : GeneralBorrowAnchor.AnchorOwned tree anchor ownerKind) :
    GeneralBorrowAnchor.AnchorOwned tree anchor kind := by
  refine ⟨owned.anchorValid,owned.locationsAligned,owned.defaultsAligned,?_⟩
  intro position valid
  obtain ⟨state,present,permitted⟩ := owned.permissions position valid
  refine ⟨state,present,?_⟩
  cases ownerKind with
  | Read => rw [allowed rfl];exact permitted
  | Write => cases kind with
    | Read => exact write_readable state _ _ permitted
    | Write => exact permitted



private theorem location_choice (condition : Prop) [Decidable condition] (location : LocationTree) :
    (ForInStep.value (if condition then ForInStep.yield (location,(none : Option BorrowTree.BorrowTreeAccessStatus),true)
      else ForInStep.yield (location,none,false))).1 = location := by
  by_cases chosen : condition <;> simp [chosen,ForInStep.value]

/-- Under the single-root data invariant, the actual concrete-tree wrapper
returns the normal component's location; no other wildcard root is accessed. -/
theorem single_root_location (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor root : UniIndex) (kind : AccessKind) (mode : ChildrenVisitMode) (range : ByteRange)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (owned : GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree location protections) anchor.toNat kind)
    (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (roots : tree.roots = #[root]) (covered : GeneralBorrowGraph.RootsCover tree) :
    source_access_location (source_tree_access_at tree location (some anchor) kind protections mode range) =
      (tree.performNormalAccessAt location anchor kind protections mode).location := by
  have succeeded := GeneralBorrowNormalLocation.normal_succeeds tree location protections anchor kind mode
    forest owned depth children anchorNode anchorPresent
  have pathRoot := GeneralBorrowTerminal.ancestor_root_present
    (source_normal_projection tree location protections).topology forest (GeneralBorrowGraph.Present tree)
    (GeneralBorrowGraph.parents_closed tree location protections depth) anchor.toNat root.toNat owned.anchorValid
    ⟨anchor,anchorNode,rfl,anchorPresent⟩
    (fun index _ present parentless => GeneralBorrowGraph.unique_root tree location protections root roots covered index present parentless)
  have normalRoot : (tree.performNormalAccessAt location anchor kind protections mode).access.root = root.toNat :=
    (GeneralBorrowStorage.events_root _ _ kind (source_normal_projection tree location protections)).trans pathRoot
  have converted : UniIndex.ofNat? (tree.performNormalAccessAt location anchor kind protections mode).access.root = some root := by
    rw [normalRoot]
    exact index_self root
  simp_tree_helpers
  simp only [succeeded.1,succeeded.2,converted]
  simp [roots,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    List.range'_succ,List.range'_zero,bind,pure]
  change (ForInStep.value (_ : ForInStep (LocationTree × Option BorrowTree.BorrowTreeAccessStatus × Bool))).1 = _
  exact location_choice _ _

/-- Full real single-root location access preserves ownership at a selected
strength, including a mutable parent's ownership across a read. -/
theorem location_owned (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor root : UniIndex) (kind ownerKind : AccessKind) (mode : ChildrenVisitMode) (range : ByteRange)
    (allowed : ownerKind = .Read → kind = .Read) (fits : tree.nodes.data.size ≤ 4294967296)
    (owned : GeneralBorrowRange.LocationOwned tree protections anchor ownerKind location)
    (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (roots : tree.roots = #[root]) (covered : GeneralBorrowGraph.RootsCover tree) :
    GeneralBorrowRange.LocationOwned tree protections anchor ownerKind
      (source_access_location (source_tree_access_at tree location (some anchor) kind protections mode range)) := by
  rcases owned with ⟨⟨forest⟩,owner⟩
  have accessOwner := owned_for_access _ anchor.toNat kind ownerKind allowed owner
  rw [single_root_location tree location protections anchor root kind mode range forest accessOwner depth children
    anchorNode anchorPresent roots covered]
  refine ⟨⟨forest⟩,normal_location_owned_as tree location protections anchor kind ownerKind mode allowed fits forest owner⟩



/-- Real ranged access preserves the original ownership strength, map
well-formedness and capacity. In particular a parent's write ownership survives
its retagging read. Ownership outside the requested interval is an explicit
strong premise here; range-local callers need the separate selected-origin lift. -/
theorem ranged (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag) (anchor root : UniIndex)
    (offset len : Size) (kind ownerKind : AccessKind) (mode : ChildrenVisitMode)
    (allowed : ownerKind = .Read → kind = .Read) (fits : tree.nodes.data.size ≤ 4294967296)
    (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (roots : tree.roots = #[root]) (covered : GeneralBorrowGraph.RootsCover tree)
    (tagPresent : tree.indexOfTag tag = some anchor)
    (well : tree.locations.WellFormed)
    (all : Every (GeneralBorrowRange.LocationOwned tree protections anchor ownerKind) tree.locations)
    (bounds : offset.bytes.toNat + len.bytes.toNat ≤ tree.locations.size.bytes.toNat) :
    let result := tree.performNormalAccessRange tag offset len kind protections mode
    result.status = .Completed ∧
      Every (GeneralBorrowRange.LocationOwned result.tree protections anchor ownerKind) result.tree.locations ∧
      result.tree.locations.WellFormed ∧ result.tree.locations.size = tree.locations.size := by
  dsimp only
  let predicate := GeneralBorrowRange.LocationOwned tree protections anchor ownerKind
  let prepared := tree.locations.iterMut offset len
  have preparedGood := GeneralRangeMapSafety.iter_mut predicate tree.locations offset len well all bounds
  unfold BorrowTree.performNormalAccessRange BorrowTree.performBorrowAccessRange
  simp only [tagPresent,Option.isNone_some,Bool.false_eq_true,↓reduceIte]
  simp only [Id.run,bind,pure,preparedGood.outcome]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  name_borrow_range_scan
  let property := fun state : DedupRangeMap LocationTree × Array BorrowTree.BorrowTreeLocationResult × BorrowTree.BorrowTreeAccessStatus =>
    state.2.2 = .Completed ∧ state.1.entries.size = prepared.state.entries.size ∧
      Every predicate state.1 ∧ state.1.WellFormed ∧ state.1.size = tree.locations.size
  have step : ∀ cursor ∈ List.range' 0 prepared.positions.size, ∀ state,
      property state → property (scan cursor state).value := by
    intro cursor member state good
    rcases state with ⟨current,visited,status⟩
    rcases good with ⟨statusEq,sizeEq,every,wellFormed,capacity⟩
    dsimp only at statusEq sizeEq
    subst status
    have cursorBound : cursor < prepared.positions.size := by
      have bounded := List.mem_range'_1.mp member
      simpa using bounded.2
    have segmentBound : cursor < prepared.segments.size := by rw [←preparedGood.lengths];exact cursorBound
    let position := prepared.positions[cursor]'cursorBound
    let segment := prepared.segments[cursor]'segmentBound
    obtain ⟨positionBound,selected⟩ := preparedGood.selected cursor cursorBound
    have ownedHere : predicate segment.data := by
      rw [show segment = prepared.state.entries[position]'positionBound from selected]
      exact preparedGood.every position positionBound
    have updatedOwned := location_owned tree segment.data protections anchor root kind ownerKind mode segment.range allowed fits
      ownedHere depth children anchorNode anchorPresent roots covered
    obtain ⟨⟨forest⟩,owner⟩ := ownedHere
    have accessGood := GeneralBorrowSingleRoot.access_at tree segment.data protections anchor root kind mode segment.range
      forest (owned_for_access _ anchor.toNat kind ownerKind allowed owner) depth children anchorNode anchorPresent roots covered
    let access := source_tree_access_at tree segment.data (some anchor) kind protections mode segment.range
    let mutation := current.setAtPos position (source_access_location access)
    have currentBound : position < current.entries.size := by rw [sizeEq];exact positionBound
    have positionLookup : (tree.locations.iterMut offset len).positions[cursor]? = some position := Array.getElem?_eq_getElem cursorBound
    have segmentLookup : (tree.locations.iterMut offset len).segments[cursor]? = some segment := Array.getElem?_eq_getElem segmentBound
    have actual : scan cursor (current,visited,.Completed) =
        .yield (mutation.state,visited.push ⟨segment.range,source_access_normal access⟩,.Completed) := by
      simp only [scan,beq_self_eq_true,↓reduceIte,positionLookup,segmentLookup,
        setAtPos_success current position currentBound,accessGood]
      rfl
    rw [actual]
    refine ⟨rfl,(setAtPos_length current position currentBound _).trans sizeEq,?_,?_,?_⟩
    · dsimp only [mutation]
      rw [setAtPos_exact current position currentBound]
      exact replaced_every predicate current position currentBound _ every updatedOwned
    · dsimp only [mutation]
      rw [setAtPos_exact current position currentBound]
      exact replaced_wellFormed current position currentBound _ wellFormed
    · dsimp only [mutation]
      rw [setAtPos_exact current position currentBound]
      exact (replaced_size current position currentBound _).trans capacity
  have initial : property (prepared.state,#[],.Completed) :=
    ⟨rfl,rfl,preparedGood.every,preparedGood.wellFormed,congrArg Size.ofBytes preparedGood.capacity⟩
  have final := GeneralBorrowLoop.list_invariant _ scan property step _ initial
  exact ⟨final.1,final.2.2.1,final.2.2.2.1,final.2.2.2.2⟩


end DuplicatePrefix.GeneralBorrowRangePreserves
#print axioms DuplicatePrefix.GeneralBorrowRangePreserves.normal_owned
open Lean Elab Command in
run_cmd do
  for dependency in (←collectAxioms ``DuplicatePrefix.GeneralBorrowRangePreserves.normal_owned) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved ranged ownership dependency {dependency}"
