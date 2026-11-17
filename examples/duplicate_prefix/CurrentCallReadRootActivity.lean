import duplicate_prefix.S02HiddenLeafQuietWildcard
import duplicate_prefix.S03EmptyPopFactsTreeAccess
import duplicate_prefix.CurrentCallRootActivity
import duplicate_prefix.DuplicatePrefixNormalKind
import duplicate_prefix.S05CurrentReleaseIterator
import duplicate_prefix.GeneralBorrowStructuralReleaseGeometryFrame

namespace DuplicatePrefix.CurrentCallReadRootActivity
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection BorrowRangeAccess GeneralBorrowExposureCardinality
open GeneralRangeMapOrigins GeneralRangeMapState GeneralBorrowFreshActiveWithin
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Real normal access to a distinct source keeps a zero child inactive.
The actual cache result supplies its zero local counter for later callbacks. -/
theorem normal (tree : BorrowTree) (graph : GeneralBorrowStructuralHistoryState.GraphState tree)
    (location : LocationTree) (protections : ProtectedTags)
    (query source : UniIndex) (node sourceNode : TreeNode)
    (present : tree.nodeAt query = some node) (sourcePresent : tree.nodeAt source = some sourceNode)
    (leaf : node.children = #[]) (hidden : node.isExposed = false) (different : query ≠ source)
    (kind : AccessKind)
    (authorization : DuplicatePrefixNormalKind.Capability tree location protections source kind)
    (coherent : LocationCoherent tree location protections)
    (mode : ChildrenVisitMode)
    (quiet : S02HiddenLeafQuietNormal.Quiet (GeneralBorrowWildcardVirtualLeaf.effective location query node)) :
    let result := tree.performNormalAccessAt location source kind protections mode
    result.access.status = .Completed ∧ result.outcome = .ok () ∧
    S02HiddenLeafQuietNormal.Quiet (GeneralBorrowWildcardVirtualLeaf.effective result.location query node) ∧
    counter result.location.exposedCache query kind = 0 := by
  obtain ⟨forest⟩ := graph.forest location protections
  obtain ⟨depth⟩ := graph.depth
  have owned : GeneralBorrowCompatibleScopedNormal.Owned (source_normal_projection tree location protections)
      source.toNat kind authorization.component := by
    intro index included valid
    have size : (source_normal_projection tree location protections).topology.nodes.size = tree.nodes.data.size := by
      unfold_general_projection
      unfold_general_topology
      simp only [Array.size_map]
    exact authorization.permissions index included (by rwa [←size])
  obtain ⟨done,outcome,afterCoherent⟩ := GeneralBorrowCompatibleScopedNormalExposure.access tree location protections
    source kind mode depth graph.children sourceNode sourcePresent forest authorization.component owned coherent
  have before : S02HiddenLeafQuietNormal.LocationTyped location query := by
    intro state stored
    change S02HiddenLeafQuietNormal.Quiet state
    simpa only [GeneralBorrowWildcardVirtualLeaf.effective,stored,Option.getD_some] using quiet
  have after := S02HiddenLeafQuietNormal.normal tree location protections source query kind mode before
    (S03EmptyPopFactsLeaf.foreign_events tree location protections query source node sourceNode present sourcePresent leaf different forest kind mode)
  refine ⟨done,outcome,?_,?_⟩
  · cases stored : (tree.performNormalAccessAt location source kind protections mode).location.perms.get query with
    | none => left;simp only [GeneralBorrowWildcardVirtualLeaf.effective,stored,Option.getD_none,TreeNode.defaultLocationState]
    | some state => simpa only [GeneralBorrowWildcardVirtualLeaf.effective,stored,Option.getD_some,S02HiddenLeafQuietNormal.Quiet] using after state stored
  · rw [afterCoherent query kind,S03EmptyPopFactsAuthorization.leaf_cardinality tree _ protections graph query node present leaf hidden kind]
    rfl

/-- The actual concrete per-row operation preserves the empty leaf through
its normal phase and every ordered physical-root callback. -/
theorem concrete (tree : BorrowTree) (graph : GeneralBorrowStructuralHistoryState.GraphState tree)
    (location : LocationTree) (protections : ProtectedTags)
    (query source : UniIndex) (node sourceNode : TreeNode)
    (present : tree.nodeAt query = some node) (sourcePresent : tree.nodeAt source = some sourceNode)
    (leaf : node.children = #[]) (hidden : node.isExposed = false) (different : query ≠ source)
    (kind : AccessKind)
    (authorization : DuplicatePrefixNormalKind.Capability tree location protections source kind)
    (coherent : LocationCoherent tree location protections)
    (mode : ChildrenVisitMode) (range : ByteRange)
    (quiet : S02HiddenLeafQuietNormal.Quiet (GeneralBorrowWildcardVirtualLeaf.effective location query node)) :
    let result := source_access_location (source_tree_access_at tree location (some source) kind protections mode range)
    S02HiddenLeafQuietNormal.Quiet (GeneralBorrowWildcardVirtualLeaf.effective result query node) ∧
      counter result.exposedCache query kind = 0 := by
  have initial := normal tree graph location protections query source node sourceNode
    present sourcePresent leaf hidden different kind authorization coherent mode quiet
  unfold_internal ".BorrowTree.performTreeAccessAt"
  simp only [Id.run,bind,pure,initial.1,initial.2.1,beq_self_eq_true,bne_self_eq_false,Bool.not_true,Bool.false_eq_true,↓reduceIte]
  cases converted : UniIndex.ofNat? (tree.performNormalAccessAt location source kind protections mode).access.root with
  | none => simpa only [converted] using initial.2.2
  | some selected =>
    simp only [converted,Id.run,bind,pure,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
      Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
    name_borrow_range_scan
    let predicate := fun (state : LocationTree × Option BorrowTree.BorrowTreeAccessStatus × Bool) =>
      S02HiddenLeafQuietNormal.Quiet (GeneralBorrowWildcardVirtualLeaf.effective state.1 query node) ∧
        counter state.1.exposedCache query kind = 0
    have step : ∀ position ∈ List.range' 0 tree.roots.size, ∀ state,
        predicate state → predicate (scan position state).value := by
      intro position member state good
      rcases state with ⟨current,status,stopped⟩
      dsimp only [scan]
      repeat' first | split | simp_all only [Bool.and_eq_true,ForInStep.value]
      all_goals first
        | exact good
        | exact S02HiddenLeafQuietWildcard.access tree graph query node present leaf hidden current _ _ kind protections _ good.1 good.2
    have retained := GeneralBorrowLoop.list_invariant _ scan predicate step
      ((tree.performNormalAccessAt location source kind protections mode).location,none,false) initial.2.2
    exact retained

private theorem replace_write (map : DedupRangeMap LocationTree) (position : Nat)
    (valid : position < map.entries.size) (location : LocationTree) (anchor : UniIndex) (lower upper : UInt64)
    (active : Profile map anchor .Write lower upper)
    (preserved : ∀ (point : UInt64), map.entries[position].range.start.toNat ≤ point.toNat → point.toNat < map.entries[position].range.stop.toNat →
      ∀ state,location.perms.get anchor = some state → state.accessed = true → ∀ kind,state.permission.associatedAccess = some kind →
        lower.toNat ≤ point.toNat ∧ point.toNat < upper.toNat) :
    Profile (replaced map position valid location) anchor .Write lower upper := by
  intro point value atPoint state stored accessed kind associated
  obtain ⟨query,bounded,startPoint,pointStop,dataEq⟩ := atPoint
  have oldBound : query < map.entries.size := by simpa only [replaced_length] using bounded
  rw [replaced_range map position valid location query oldBound] at startPoint pointStop
  by_cases same : position = query
  · subst query
    have sameData : location = value := by simpa only [replaced,Array.getElem_set_self] using dataEq
    rw [←sameData] at stored
    have bounds := preserved point startPoint pointStop state stored accessed kind associated
    exact ⟨bounds.1,bounds.2,by intro h;cases h⟩
  · have dataSame : (replaced map position valid location).entries[query].data = map.entries[query].data := by simp [replaced,Array.getElem_set,same]
    rw [dataSame] at dataEq
    exact active point value ⟨query,oldBound,startPoint,pointStop,dataEq⟩ state stored accessed kind associated

/-- An arbitrary-root concrete Read preserves a distinct hidden old
leaf's bytewise activity interval through its normal visitor and every callback.
No singleton root, sibling relation, successful operation or extra caller
permission profile is assumed. The access and owner intervals may overlap. -/
theorem concrete_of_normal (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (tag : BorTag) (source query : UniIndex) (sourceNode : TreeNode)
    (sourcePresent : tree.nodeAt source = some sourceNode)
    (offset len : UInt64) (requestBounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (normalRows : OwnedOn (fun location => Nonempty (DuplicatePrefixNormalKind.Capability tree location global.protectedTags source .Read))
      offset (offset+len) tree.locations)
    (tagged : tree.indexOfTag tag = some source)
    (node : TreeNode) (present : tree.nodeAt query = some node)
    (leaf : node.children = #[]) (hidden : node.isExposed = false) (different : query ≠ source)
    (lower upper : UInt64) (active : ActiveWithin tree query .Write lower upper)
    (mode : ChildrenVisitMode) :
    ActiveWithin (tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes offset) (Size.ofBytes len)
      .Read global.protectedTags mode).tree query .Write lower upper := by
  let requestedOffset := Size.ofBytes offset
  let requestedLen := Size.ofBytes len
  let protections := global.protectedTags
  have well := runtime.formed.well
  have bounds : requestedOffset.bytes.toNat+requestedLen.bytes.toNat ≤ tree.locations.size.bytes.toNat := requestBounds
  let prepared := tree.locations.iterMut requestedOffset requestedLen
  have preparedData := GeneralRangeMapOriginPrepare.iter_mut tree.locations requestedOffset requestedLen well bounds
  have good := preparedData.1
  have preparedActive := refines tree.locations prepared.state preparedData.2.1 query .Write lower upper active
  have preparedCoherent := GeneralRangeMapSafety.iter_mut
    (fun location => GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    tree.locations requestedOffset requestedLen well runtime.coherent bounds
  have preparedOwners := GeneralRangeMapOriginPrepare.selected_owned_on tree.locations requestedOffset requestedLen well bounds
    (fun location => Nonempty (DuplicatePrefixNormalKind.Capability tree location protections source .Read))
    offset (offset+len) normalRows (Nat.le_refl _) (Nat.le_refl _)
  have preparedOutcome : (tree.locations.iterMut (Size.ofBytes offset) (Size.ofBytes len)).outcome = .ok () := good.outcome
  unfold BorrowTree.performBorrowAccessRange
  simp only [tagged,Option.isNone_some,Bool.false_eq_true,↓reduceIte,Id.run,bind,pure,preparedOutcome]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  name_borrow_range_scan
  let property := fun state : DedupRangeMap LocationTree × Array BorrowTree.BorrowTreeLocationResult × BorrowTree.BorrowTreeAccessStatus =>
    state.1.entries.map (·.range) = prepared.state.entries.map (·.range) ∧ Profile state.1 query .Write lower upper
  have step : ∀ cursor ∈ List.range' 0 prepared.positions.size, ∀ state,
      property state → property (scan cursor state).value := by
    intro cursor member state maintained
    rcases state with ⟨current,visited,status⟩
    rcases maintained with ⟨ranges,currentActive⟩
    by_cases completed : status = .Completed
    · subst status
      have sizeEq : current.entries.size = prepared.state.entries.size := by
        have known := congrArg Array.size ranges
        simpa only [Array.size_map] using known
      have cursorBound : cursor < prepared.positions.size := by have := List.mem_range'_1.mp member;omega
      have segmentBound : cursor < prepared.segments.size := by rw [←good.lengths];exact cursorBound
      let position := prepared.positions[cursor]'cursorBound
      let segment := prepared.segments[cursor]'segmentBound
      obtain ⟨positionBound,selected⟩ := good.selected cursor cursorBound
      have currentBound : position < current.entries.size := by rw [sizeEq];exact positionBound
      have rangeSame : current.entries[position].range = segment.range := by
        have known := congrArg (fun rows => rows[position]?) ranges
        simp only [Array.getElem?_map,
          Array.getElem?_eq_getElem (xs := current.entries) (i := position) currentBound,
          Array.getElem?_eq_getElem (xs := prepared.state.entries) (i := position) positionBound,
          Option.map_some,Option.some.injEq] at known
        have selectedRange : prepared.state.entries[position].range = segment.range :=
          (congrArg (fun entry : RangeMapSegment LocationTree => entry.range) selected).symm
        exact known.trans selectedRange
      let access := source_tree_access_at tree segment.data (some source) .Read protections mode segment.range
      let mutation := current.setAtPos position (source_access_location access)
      have afterRanges : mutation.state.entries.map (·.range) = prepared.state.entries.map (·.range) := by
        dsimp only [mutation]
        rw [setAtPos_exact current position currentBound,replaced_ranges]
        exact ranges
      have afterActive : Profile mutation.state query .Write lower upper := by
        dsimp only [mutation]
        rw [setAtPos_exact current position currentBound]
        apply replace_write current position currentBound _ query lower upper currentActive
        intro point startPoint pointStop state stored accessed accessKind associated
        by_cases inside : lower.toNat ≤ point.toNat ∧ point.toNat < upper.toNat
        · exact inside
        · have oldRange : prepared.state.entries[position].range = segment.range := (congrArg (fun entry : RangeMapSegment LocationTree => entry.range) selected).symm
          have oldData : prepared.state.entries[position].data = segment.data := (congrArg (fun entry : RangeMapSegment LocationTree => entry.data) selected).symm
          have atPoint : ValueAt prepared.state point segment.data := ⟨position,positionBound,by rw [oldRange,←rangeSame];exact startPoint,by rw [oldRange,←rangeSame];exact pointStop,oldData⟩
          have oldQuiet : S02HiddenLeafQuietNormal.LocationTyped segment.data query := by
            intro old oldStored
            by_cases cell : old.permission = .Cell
            · exact Or.inr cell
            · apply Or.inl
              by_cases notFalse : old.accessed = false
              · exact notFalse
              · have oldAccessed : old.accessed = true := by
                  cases flag : old.accessed with
                  | false => exact False.elim (notFalse flag)
                  | true => first | exact flag | rfl
                have oldAssociated : ∃ accessKind,old.permission.associatedAccess = some accessKind := by
                  cases permission : old.permission <;> simp_all [Permission.associatedAccess]
                obtain ⟨oldKind,oldAssociated⟩ := oldAssociated
                have wasInside := preparedActive point segment.data atPoint old oldStored oldAccessed oldKind oldAssociated
                exact False.elim (inside ⟨wasInside.1,wasInside.2.1⟩)
          have segmentCoherent : GeneralBorrowExposureCardinality.LocationCoherent tree segment.data global.protectedTags := by
            have property := preparedCoherent.every position positionBound
            rw [←selected] at property
            exact property
          obtain ⟨normal⟩ := preparedOwners.2.2 cursor segmentBound
          have oldEffectiveQuiet : S02HiddenLeafQuietNormal.Quiet (GeneralBorrowWildcardVirtualLeaf.effective segment.data query node) := by
            cases oldStored : segment.data.perms.get query with
            | none => left;simp only [GeneralBorrowWildcardVirtualLeaf.effective,oldStored,Option.getD_none,TreeNode.defaultLocationState]
            | some old => simpa only [GeneralBorrowWildcardVirtualLeaf.effective,oldStored,Option.getD_some] using oldQuiet old oldStored
          have newEffectiveQuiet := (concrete tree runtime.formed.toGraphState segment.data global.protectedTags
            query source node sourceNode present sourcePresent leaf hidden different .Read normal segmentCoherent mode segment.range oldEffectiveQuiet).1
          have newQuiet : S02HiddenLeafQuietNormal.LocationTyped
              (source_access_location access) query := by
            intro value valueStored
            change S02HiddenLeafQuietNormal.Quiet value
            change S02HiddenLeafQuietNormal.Quiet (((source_access_location access).perms.get query).getD node.defaultLocationState) at newEffectiveQuiet
            simpa only [valueStored,Option.getD_some] using newEffectiveQuiet
          rcases newQuiet state stored with inactive | cell
          · rw [accessed] at inactive;cases inactive
          · rw [cell,Permission.associatedAccess] at associated;cases associated
      have positionLookup : (tree.locations.iterMut (Size.ofBytes offset) (Size.ofBytes len)).positions[cursor]? = some position := Array.getElem?_eq_getElem cursorBound
      have segmentLookup : (tree.locations.iterMut (Size.ofBytes offset) (Size.ofBytes len)).segments[cursor]? = some segment := Array.getElem?_eq_getElem segmentBound
      dsimp only [mutation,access,protections] at afterRanges afterActive
      cases failure : source_access_status access
      all_goals dsimp only [access,protections] at failure
      all_goals simpa only [scan,beq_self_eq_true,↓reduceIte,positionLookup,segmentLookup,
          setAtPos_success current position currentBound,failure,property,ForInStep.value]
          using And.intro afterRanges afterActive
    · simpa only [scan,beq_iff_eq,completed,Bool.false_eq_true,↓reduceIte,ForInStep.value,property] using And.intro ranges currentActive
  have initial : property (prepared.state,#[],.Completed) := ⟨rfl,preparedActive⟩
  have final := DuplicatePrefix.GeneralBorrowLoop.list_invariant _ scan property step (prepared.state,#[],.Completed) initial
  exact final.2
private theorem list_partial {α β : Type} (items : List α) (scan : α → β → Id (ForInStep β))
    (property : List α → β → Prop) (base : β → Prop)
    (forget : ∀ rest state, property rest state → base state)
    (step : ∀ position rest, position ∉ rest → ∀ state, property (position::rest) state →
      match scan position state with
      | .done next => base next
      | .yield next => property rest next)
    (distinct : items.Nodup) (initial : β) (good : property items initial) :
    base (forIn items initial scan) := by
  induction items generalizing initial with
  | nil => exact forget [] initial good
  | cons position rest ih =>
    obtain ⟨notMember,tailDistinct⟩ := List.nodup_cons.mp distinct
    have next := step position rest notMember initial good
    rw [List.forIn_cons]
    cases actual : scan position initial with
    | done final => simpa only [actual,bind,pure] using next
    | yield more =>
      simp only [bind]
      exact ih tailDistinct more (by simpa only [actual] using next)

private theorem release_rows (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag) (source : UniIndex)
    (sourceNode : TreeNode) (present : tree.nodeAt source = some sourceNode)
    (hidden : sourceNode.isExposed = false) (tagged : tree.indexOfTag tag = some source)
    (P : ByteRange → LocationTree → Prop) (rows : S05CurrentReleaseIterator.Rows P tree.locations)
    (row : ∀ position (valid : position < tree.locations.entries.size) state,
      tree.locations.entries[position].data.perms.get source = some state → state.accessed = true →
      ∀ kind, state.permission.associatedAccess = some kind →
      P tree.locations.entries[position].range (source_access_location (source_tree_access_at tree
        tree.locations.entries[position].data (some source) kind protections .SkipChildrenOfAccessed tree.locations.entries[position].range))) :
    S05CurrentReleaseIterator.Rows P (tree.releaseProtector tag protections).tree.locations := by
  open GeneralBorrowFreshReleaseLoop GeneralBorrowStructuralReleaseGeometryFrame in
  unfold BorrowTree.releaseProtector
  rw [tagged]
  simp only [Id.run,bind,pure,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  name_fresh_release_scan
  let invariant := fun current : BorrowTree =>
    current = {tree with locations := current.locations} ∧
    current.locations.entries.size = tree.locations.entries.size ∧ S05CurrentReleaseIterator.Rows P current.locations
  let base := fun state : Option BorrowTree.ProtectorReleaseResult × BorrowTree =>
    invariant state.2 ∧ ∀ result, state.1 = some result → invariant result.tree
  let property := fun (remaining : List Nat) (state : Option BorrowTree.ProtectorReleaseResult × BorrowTree) =>
    state.1 = none ∧ base state ∧ ∀ position ∈ remaining,
      ∃ valid : position < tree.locations.entries.size, ∃ bounded : position < state.2.locations.entries.size,
        state.2.locations.entries[position] = tree.locations.entries[position]
  have step : ∀ position rest, position ∉ rest → ∀ state, property (position::rest) state →
      match scan position state with | .done next => base next | .yield next => property rest next := by
    intro position rest notMember state good
    rcases state with ⟨returned,current⟩
    rcases good with ⟨returnedEq,⟨currentGood,_⟩,untouched⟩
    dsimp only at returnedEq currentGood untouched
    subst returned
    obtain ⟨oldValid,currentValid,same⟩ := untouched position (by simp)
    have skipped : property rest (none,current) := by
      exact ⟨rfl,⟨currentGood,by simp⟩,fun other member => untouched other (by simp [member])⟩
    cases stored : tree.locations.entries[position].data.perms.get source with
    | none => simpa only [scan,index_exact current.locations position currentValid,same,stored] using skipped
    | some before =>
      cases associated : before.permission.associatedAccess with
      | none => simpa only [scan,index_exact current.locations position currentValid,same,stored,associated] using skipped
      | some accessKind =>
        cases accessed : before.accessed with
        | false => simpa only [scan,index_exact current.locations position currentValid,same,stored,associated,accessed,Bool.false_eq_true,↓reduceIte] using skipped
        | true =>
          let access := source_tree_access_at tree tree.locations.entries[position].data (some source)
            accessKind protections .SkipChildrenOfAccessed tree.locations.entries[position].range
          let next : BorrowTree := {current with locations := (current.locations.setAtPos position (source_access_location access)).state}
          have nextGood : invariant next := by
            refine ⟨?_,(setAtPos_length current.locations position currentValid _).trans currentGood.2.1,?_⟩
            · dsimp only [next]
              rw [currentGood.1]
            · intro index bounded
              have oldBound : index < current.locations.entries.size := by
                simpa only [next,setAtPos_exact current.locations position currentValid,replaced_length] using bounded
              by_cases equal : position = index
              · subst index
                have ready := row position oldValid before stored accessed accessKind associated
                have rangeEq : current.locations.entries[position].range = tree.locations.entries[position].range := congrArg RangeMapSegment.range same
                simpa only [next,setAtPos_exact current.locations position currentValid,replaced,Array.getElem_set_self,rangeEq] using ready
              · have old := currentGood.2.2 index oldBound
                simpa only [next,setAtPos_exact current.locations position currentValid,replaced,Array.getElem_set,equal,↓reduceIte] using old
          have nextProperty : property rest (none,next) := by
            refine ⟨rfl,⟨nextGood,by simp⟩,?_⟩
            intro other member
            obtain ⟨valid,otherValid,entryEq⟩ := untouched other (by simp [member])
            have different : position ≠ other := by intro same;subst other;exact notMember member
            refine ⟨valid,by change other < (current.locations.setAtPos position _).state.entries.size; rw [setAtPos_length current.locations position currentValid]; exact otherValid,?_⟩
            simpa only [next,setAtPos_exact current.locations position currentValid,replaced,Array.getElem_set,different,↓reduceIte] using entryEq
          have context : source_tree_access_at current tree.locations.entries[position].data (some source) accessKind protections .SkipChildrenOfAccessed tree.locations.entries[position].range = access := by
            rw [currentGood.1]
            rfl
          cases failure : source_access_status access
          · simpa only [scan,index_exact current.locations position currentValid,same,stored,associated,accessed,↓reduceIte,
              context,setAtPos_success current.locations position currentValid,failure,next] using nextProperty
          · rename_i error
            have returnedGood : base (some ⟨next,.AccessFailure tree.locations.entries[position].range error⟩,next) :=
              ⟨nextGood,fun result same => by cases same;exact nextGood⟩
            simpa only [scan,index_exact current.locations position currentValid,same,stored,associated,accessed,↓reduceIte,
              context,setAtPos_success current.locations position currentValid,failure,next] using returnedGood
  have initial : property (List.range' 0 tree.locations.entries.size) (none,tree) := by
    refine ⟨rfl,⟨⟨rfl,rfl,rows⟩,by simp⟩,?_⟩
    intro position member
    have valid : position < tree.locations.entries.size := by have := List.mem_range'_1.mp member;omega
    exact ⟨valid,valid,rfl⟩
  have final := list_partial (List.range' 0 tree.locations.entries.size) scan property base (fun _ _ good => good.2.1) (by
    intro position rest distinct state good
    have next := step position rest distinct state good
    cases actual : scan position state <;> simpa only [actual] using next) (List.nodup_range' 1) (none,tree) initial
  split
  · exact (final.2 _ (by assumption)).2.2
  · have currentGood := final.1
    have sameTag : (forIn (List.range' 0 tree.locations.entries.size) (none,tree) scan).2.indexOfTag tag = some source := by
      rw [currentGood.1]
      exact tagged
    have sameNode : (forIn (List.range' 0 tree.locations.entries.size) (none,tree) scan).2.nodeAt source = some sourceNode := by
      rw [currentGood.1]
      exact present
    unfold BorrowTree.updateExposureForProtectorRelease
    simp only [sameTag,sameNode,hidden,Bool.not_false,↓reduceIte,Id.run,pure]
    exact currentGood.2.2

/-- The actual hidden Read-protector release preserves a distinct hidden leaf's
activity, including an early failing access prefix. Only the helper's Read
capability is needed at rows where that helper is actually active. -/
theorem release (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (tag : BorTag) (source target : UniIndex) (sourceNode targetNode : TreeNode)
    (tagged : tree.indexOfTag tag = some source) (sourceAt : tree.nodeAt source = some sourceNode)
    (sourceHidden : sourceNode.isExposed = false)
    (targetAt : tree.nodeAt target = some targetNode) (targetLeaf : targetNode.children = #[])
    (targetHidden : targetNode.isExposed = false) (different : target ≠ source)
    (offset upper lower targetUpper : UInt64)
    (sourceActive : ActiveWithin tree source .Read offset upper)
    (normalRows : OwnedOn (fun location => Nonempty (DuplicatePrefixNormalKind.Capability tree location global.protectedTags source .Read))
      offset upper tree.locations)
    (targetActive : ActiveWithin tree target .Write lower targetUpper) :
    ActiveWithin (tree.releaseProtector tag global.protectedTags).tree target .Write lower targetUpper := by
  let P := fun (range : ByteRange) (location : LocationTree) =>
    ∀ point : UInt64, range.start.toNat ≤ point.toNat → point.toNat < range.stop.toNat →
      ∀ state, location.perms.get target = some state → state.accessed = true →
      ∀ kind, state.permission.associatedAccess = some kind → lower.toNat ≤ point.toNat ∧ point.toNat < targetUpper.toNat
  have rows : S05CurrentReleaseIterator.Rows P tree.locations := by
    intro position valid point start stop state stored accessed kind associated
    have old := targetActive point tree.locations.entries[position].data ⟨position,valid,start,stop,rfl⟩ state stored accessed kind associated
    exact ⟨old.1,old.2.1⟩
  have activeRows := GeneralBorrowFreshActiveWithin.active_on tree source .Read offset upper runtime.formed.well sourceActive
  have retained := release_rows tree global.protectedTags tag source sourceNode sourceAt sourceHidden tagged P rows (by
    intro position valid state stored accessed kind associated
    obtain ⟨start,stop,readKind⟩ := activeRows position valid state stored accessed kind associated
    have kindEq := readKind rfl
    subst kind
    have positive := (GeneralRangeMapGeometry.facts tree.locations runtime.formed.well (by omega)).2.1 position valid
    have first := sourceActive tree.locations.entries[position].range.start tree.locations.entries[position].data
      ⟨position,valid,Nat.le_refl _,positive,rfl⟩ state stored accessed .Read associated
    obtain ⟨normal⟩ := normalRows position valid (by omega) start stop
    intro point pointStart pointStop after afterStored afterAccessed afterKind afterAssociated
    by_cases inside : lower.toNat ≤ point.toNat ∧ point.toNat < targetUpper.toNat
    · exact inside
    have quiet : S02HiddenLeafQuietNormal.Quiet (GeneralBorrowWildcardVirtualLeaf.effective tree.locations.entries[position].data target targetNode) := by
      cases oldStored : tree.locations.entries[position].data.perms.get target with
      | none => left;simp only [GeneralBorrowWildcardVirtualLeaf.effective,oldStored,Option.getD_none,TreeNode.defaultLocationState]
      | some old =>
        simp only [GeneralBorrowWildcardVirtualLeaf.effective,oldStored,Option.getD_some]
        by_cases cell : old.permission = .Cell
        · exact .inr cell
        · left
          cases h : old.accessed with
          | false => rfl
          | true =>
            have oldAssociated : ∃ k,old.permission.associatedAccess = some k := by cases p : old.permission <;> simp_all [Permission.associatedAccess]
            obtain ⟨k,oldAssociated⟩ := oldAssociated
            exact False.elim (inside (rows position valid point pointStart pointStop old oldStored h k oldAssociated))
    have afterQuiet := (concrete tree runtime.formed.toGraphState tree.locations.entries[position].data global.protectedTags
      target source targetNode sourceNode targetAt sourceAt targetLeaf targetHidden different .Read normal (runtime.coherent position valid)
      .SkipChildrenOfAccessed tree.locations.entries[position].range quiet).1
    change S02HiddenLeafQuietNormal.Quiet (((source_access_location (source_tree_access_at tree tree.locations.entries[position].data (some source) .Read global.protectedTags
      .SkipChildrenOfAccessed tree.locations.entries[position].range)).perms.get target).getD targetNode.defaultLocationState) at afterQuiet
    rw [afterStored] at afterQuiet
    rcases afterQuiet with inactive | cell
    · simp only [Option.getD_some] at inactive;rw [afterAccessed] at inactive;cases inactive
    · simp only [Option.getD_some] at cell;rw [cell,Permission.associatedAccess] at afterAssociated;cases afterAssociated)
  intro point location valueAt state stored accessed kind associated
  obtain ⟨position,valid,start,stop,data⟩ := valueAt
  rw [←data] at stored
  have inside := retained position valid point start stop state stored accessed kind associated
  exact ⟨inside.1,inside.2,by intro impossible;cases impossible⟩

end DuplicatePrefix.CurrentCallReadRootActivity
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "CurrentCallReadRootActivity").length > 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved read root activity dependency {dependency}"
