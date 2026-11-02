import duplicate_prefix.S03EmptyPopFactsWildcard
import duplicate_prefix.S03EmptyTagState
import duplicate_prefix.GeneralRangeMapOriginPrepare

namespace DuplicatePrefix.S03EmptyPopFactsWildcardRange
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection BorrowRangeAccess GeneralBorrowExposureCardinality GeneralRangeMapState
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- Wildcard per-row access has no normal phase. The real ordered callbacks
retain the inactive bit and zero local counter of a hidden empty leaf, including
error outcomes. No successful primary callback is a premise. -/
theorem at_row (tree : BorrowTree) (graph : GeneralBorrowStructuralHistoryState.GraphState tree)
    (location : LocationTree) (protections : ProtectedTags)
    (query : UniIndex) (node : TreeNode) (present : tree.nodeAt query = some node)
    (leaf : node.children = #[]) (hidden : node.isExposed = false)
    (coherent : LocationCoherent tree location protections)
    (kind : AccessKind) (mode : ChildrenVisitMode) (range : ByteRange)
    (inactive : (GeneralBorrowWildcardVirtualLeaf.effective location query node).accessed = false) :
    let result := source_access_location (source_tree_access_at tree location none kind protections mode range)
    (GeneralBorrowWildcardVirtualLeaf.effective result query node).accessed = false ∧
      counter result.exposedCache query kind = 0 := by
  have zero : counter location.exposedCache query kind = 0 := by
    rw [coherent query kind,S03EmptyPopFactsAuthorization.leaf_cardinality tree location protections graph query node present leaf hidden kind]
    rfl
  unfold_internal ".BorrowTree.performTreeAccessAt"
  simp only [Id.run,bind,pure,Option.bind_none,ite_self]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  name_borrow_range_scan
  let predicate := fun (state : LocationTree × Option BorrowTree.BorrowTreeAccessStatus × Bool) =>
    (GeneralBorrowWildcardVirtualLeaf.effective state.1 query node).accessed = false ∧
      counter state.1.exposedCache query kind = 0
  have step : ∀ position ∈ List.range' 0 tree.roots.size, ∀ state,
      predicate state → predicate (scan position state).value := by
    intro position member state good
    rcases state with ⟨current,status,stopped⟩
    dsimp only [scan]
    repeat' first | split | simp_all only [Bool.and_eq_true,ForInStep.value]
    all_goals first
      | exact good
      | exact S03EmptyPopFactsWildcard.access tree graph query node present leaf hidden current _ _ kind protections _ good.1 good.2
  have retained := GeneralBorrowLoop.list_invariant _ scan predicate step (location,none,false) ⟨inactive,zero⟩
  exact retained

/-- Actual ranged wildcard Read/Write, including range splitting and write-back,
preserves the hidden empty leaf on every outcome. Bounds and cache coherence
are obtained from the initial wildcard owner/runtime packets. -/
theorem wildcard (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (offset len : UInt64)
    (positive : DuplicatePrefixBorrowAuthorization.Positive tree global.protectedTags none none none offset len)
    (query : UniIndex) (node : TreeNode) (present : tree.nodeAt query = some node)
    (leaf : node.children = #[]) (hidden : node.isExposed = false)
    (inactive : Every (fun location => (GeneralBorrowWildcardVirtualLeaf.effective location query node).accessed = false) tree.locations)
    (kind : AccessKind) (mode : ChildrenVisitMode) :
    Every (fun location => (GeneralBorrowWildcardVirtualLeaf.effective location query node).accessed = false)
      (tree.performBorrowAccessRange .wildcard (Size.ofBytes offset) (Size.ofBytes len) kind global.protectedTags mode).tree.locations := by
  let predicate := fun location => (GeneralBorrowWildcardVirtualLeaf.effective location query node).accessed = false
  let prepared := tree.locations.iterMut (Size.ofBytes offset) (Size.ofBytes len)
  have preparedGood := GeneralRangeMapSafety.iter_mut predicate tree.locations (Size.ofBytes offset) (Size.ofBytes len)
    runtime.formed.well inactive positive.bounds
  have preparedCoherent := GeneralRangeMapSafety.iter_mut
    (fun location => LocationCoherent tree location global.protectedTags) tree.locations (Size.ofBytes offset) (Size.ofBytes len)
    runtime.formed.well runtime.coherent positive.bounds
  unfold BorrowTree.performBorrowAccessRange
  simp only [Id.run,bind,pure,preparedGood.outcome]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  name_borrow_range_scan
  let property := fun (state : DedupRangeMap LocationTree × Array BorrowTree.BorrowTreeLocationResult × BorrowTree.BorrowTreeAccessStatus) =>
    state.1.entries.size = prepared.state.entries.size ∧ Every predicate state.1
  have step : ∀ cursor ∈ List.range' 0 prepared.positions.size, ∀ state,
      property state → property (scan cursor state).value := by
    intro cursor member state maintained
    rcases state with ⟨current,visited,status⟩
    have sizeEq := maintained.1
    by_cases completed : status = .Completed
    · subst status
      have cursorBound : cursor < prepared.positions.size := by have bound := List.mem_range'_1.mp member;omega
      have segmentBound : cursor < prepared.segments.size := by rw [←preparedGood.lengths];exact cursorBound
      let position := prepared.positions[cursor]'cursorBound
      let segment := prepared.segments[cursor]'segmentBound
      obtain ⟨positionBound,selectedPosition⟩ := preparedGood.selected cursor cursorBound
      have currentBound : position < current.entries.size := by rw [sizeEq];exact positionBound
      have segmentInactive : predicate segment.data := by
        rw [show segment = prepared.state.entries[position]'positionBound from selectedPosition]
        exact preparedGood.every position positionBound
      have segmentCoherent : LocationCoherent tree segment.data global.protectedTags := by
        rw [show segment = prepared.state.entries[position]'positionBound from selectedPosition]
        exact preparedCoherent.every position positionBound
      have preserved := (at_row tree runtime.formed.toGraphState segment.data global.protectedTags query node present leaf hidden
        segmentCoherent kind mode segment.range segmentInactive).1
      let access := source_tree_access_at tree segment.data none kind global.protectedTags mode segment.range
      let mutation := current.setAtPos position (source_access_location access)
      have nextSize : mutation.state.entries.size = prepared.state.entries.size :=
        (setAtPos_length current position currentBound _).trans sizeEq
      have nextEvery : Every predicate mutation.state := by
        dsimp only [mutation]
        rw [setAtPos_exact current position currentBound]
        exact replaced_every predicate current position currentBound _ maintained.2 preserved
      have positionLookup : (tree.locations.iterMut (Size.ofBytes offset) (Size.ofBytes len)).positions[cursor]? = some position :=
        Array.getElem?_eq_getElem cursorBound
      have segmentLookup : (tree.locations.iterMut (Size.ofBytes offset) (Size.ofBytes len)).segments[cursor]? = some segment :=
        Array.getElem?_eq_getElem segmentBound
      cases failure : source_access_status access
      all_goals dsimp only [access] at failure
      all_goals simpa only [scan,beq_self_eq_true,↓reduceIte,positionLookup,segmentLookup,setAtPos_success current position currentBound,
          failure,property,ForInStep.value] using And.intro nextSize nextEvery
    · simpa only [scan,beq_iff_eq,completed,Bool.false_eq_true,↓reduceIte,ForInStep.value,property] using maintained
  have initial : property (prepared.state,#[],.Completed) := ⟨rfl,preparedGood.every⟩
  exact (GeneralBorrowLoop.list_invariant _ scan property step _ initial).2

/-- Permission/cache access never mutates node metadata or the tag map. -/
theorem frame (tree : BorrowTree) (offset len : UInt64) (protections : ProtectedTags)
    (kind : AccessKind) (mode : ChildrenVisitMode) :
    let after := (tree.performBorrowAccessRange .wildcard (Size.ofBytes offset) (Size.ofBytes len) kind protections mode).tree
    after.nodes = tree.nodes ∧ after.tagMapping = tree.tagMapping := by
  unfold BorrowTree.performBorrowAccessRange
  simp only [Id.run,bind,pure]
  split <;> exact ⟨rfl,rfl⟩

/-- The actual wildcard Read used by return-place protection retains the full
produced zero-tag packet. Strong registration is handled by the existing raw
registration bridge before supplying this CURRENT runtime/owner packet. -/
theorem read_data (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (offset len : UInt64)
    (positive : DuplicatePrefixBorrowAuthorization.Positive tree global.protectedTags none none none offset len)
    (zeroTag : BorTag) (query : UniIndex) (zero : S03EmptyTagState.Data tree zeroTag query) :
    Nonempty (S03EmptyTagState.Data
      (tree.performBorrowAccessRange .wildcard (Size.ofBytes offset) (Size.ofBytes len)
        .Read global.protectedTags .VisitChildrenOfAccessed).tree zeroTag query) := by
  let after := (tree.performBorrowAccessRange .wildcard (Size.ofBytes offset) (Size.ofBytes len)
    .Read global.protectedTags .VisitChildrenOfAccessed).tree
  have kept := wildcard tree global runtime offset len positive query zero.node zero.present zero.leaf zero.hidden
    (S03EmptyTagState.effective tree query zero.node zero.inactive) .Read .VisitChildrenOfAccessed
  have fields := frame tree offset len global.protectedTags .Read .VisitChildrenOfAccessed
  refine ⟨⟨zero.node,?_,?_,zero.sameTag,zero.leaf,zero.hidden,?_⟩⟩
  · change after.tagMapping.get zeroTag = some query
    rw [fields.2]
    exact zero.tagged
  · change after.nodes.get query = some zero.node
    rw [fields.1]
    exact zero.present
  · intro position valid state stored
    have here := kept position valid
    simpa only [GeneralBorrowWildcardVirtualLeaf.effective,stored,Option.getD_some] using here

end DuplicatePrefix.S03EmptyPopFactsWildcardRange
