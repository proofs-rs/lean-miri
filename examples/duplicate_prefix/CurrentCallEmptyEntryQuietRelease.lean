import duplicate_prefix.S03EmptyPopFactsRange
import duplicate_prefix.GeneralBorrowSifaWritableFrame
import duplicate_prefix.GeneralBorrowFreshMetadataChildMutableReuse

/-! Actual inactive zero-source retention under concrete accesses whose row
Normal certificates are derived by the empty entry kernel. No positive-source
package or post-entry completed ancestry is required. -/
namespace DuplicatePrefix.CurrentCallEmptyEntryQuietRelease
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection BorrowRangeAccess GeneralBorrowExposureCardinality GeneralRangeMapState
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

theorem concrete (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (tag : BorTag) (source query : UniIndex) (offset len : UInt64)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (normals : GeneralRangeMapOrigins.OwnedOn (fun location => Nonempty
      (DuplicatePrefixBorrowAuthorization.Normal tree location global.protectedTags source)) offset (offset+len) tree.locations)
    (sourceNode : TreeNode) (sourcePresent : tree.nodeAt source = some sourceNode)
    (tagged : tree.indexOfTag tag = some source)
    (node : TreeNode) (present : tree.nodeAt query = some node)
    (leaf : node.children = #[]) (hidden : node.isExposed = false) (different : query ≠ source)
    (inactive : Every (fun location => (GeneralBorrowWildcardVirtualLeaf.effective location query node).accessed = false) tree.locations)
    (kind : AccessKind) (mode : ChildrenVisitMode) :
    Every (fun location => (GeneralBorrowWildcardVirtualLeaf.effective location query node).accessed = false)
      (tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes offset) (Size.ofBytes len)
        kind global.protectedTags mode).tree.locations := by
  let predicate := fun location => (GeneralBorrowWildcardVirtualLeaf.effective location query node).accessed = false
  let prepared := tree.locations.iterMut (Size.ofBytes offset) (Size.ofBytes len)
  have preparedGood := GeneralRangeMapSafety.iter_mut predicate tree.locations (Size.ofBytes offset) (Size.ofBytes len) runtime.formed.well inactive bounds
  have preparedOwners := GeneralRangeMapOriginPrepare.selected_owned_on tree.locations (Size.ofBytes offset) (Size.ofBytes len) runtime.formed.well bounds
    (fun location => Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree location global.protectedTags source)) offset (offset+len) normals (Nat.le_refl _) (Nat.le_refl _)
  have preparedCoherent := GeneralRangeMapSafety.iter_mut
    (fun location => LocationCoherent tree location global.protectedTags) tree.locations (Size.ofBytes offset) (Size.ofBytes len) runtime.formed.well runtime.coherent bounds
  unfold BorrowTree.performBorrowAccessRange
  simp only [tagged,Option.isNone_some,Bool.false_eq_true,↓reduceIte,Id.run,bind,pure,preparedGood.outcome]
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
      obtain ⟨normal⟩ := preparedOwners.2.2 cursor segmentBound
      have preserved := (S03EmptyPopFactsTreeAccess.concrete tree runtime.formed.toGraphState segment.data global.protectedTags
        query source node sourceNode present sourcePresent leaf hidden different normal segmentCoherent kind mode segment.range segmentInactive).1
      let access := source_tree_access_at tree segment.data (some source) kind global.protectedTags mode segment.range
      let mutation := current.setAtPos position (source_access_location access)
      have nextSize : mutation.state.entries.size = prepared.state.entries.size :=
        (setAtPos_length current position currentBound _).trans sizeEq
      have nextEvery : Every predicate mutation.state := by
        dsimp only [mutation]
        rw [setAtPos_exact current position currentBound]
        exact replaced_every predicate current position currentBound _ maintained.2 preserved
      have positionLookup : (tree.locations.iterMut (Size.ofBytes offset) (Size.ofBytes len)).positions[cursor]? = some position := Array.getElem?_eq_getElem cursorBound
      have segmentLookup : (tree.locations.iterMut (Size.ofBytes offset) (Size.ofBytes len)).segments[cursor]? = some segment := Array.getElem?_eq_getElem segmentBound
      cases failure : source_access_status access
      all_goals dsimp only [access] at failure
      all_goals simpa only [scan,beq_self_eq_true,↓reduceIte,positionLookup,segmentLookup,setAtPos_success current position currentBound,
          failure,property,ForInStep.value] using And.intro nextSize nextEvery
    · simpa only [scan,beq_iff_eq,completed,Bool.false_eq_true,↓reduceIte,ForInStep.value,property] using maintained
  have initial : property (prepared.state,#[],.Completed) := ⟨rfl,preparedGood.every⟩
  exact (GeneralBorrowLoop.list_invariant _ scan property step _ initial).2

/-- Materializing a distinct real child keeps the zero tag inactive globally. -/
theorem modified (map : DedupRangeMap LocationTree) (child query : UniIndex) (node : TreeNode)
    (offset len : Size) (state : LocationState) (different : query ≠ child)
    (well : map.WellFormed) (bounds : offset.bytes.toNat+len.bytes.toNat ≤ map.size.bytes.toNat)
    (inactive : Every (fun row => (GeneralBorrowWildcardVirtualLeaf.effective row query node).accessed = false) map) :
    Every (fun row => (GeneralBorrowWildcardVirtualLeaf.effective row query node).accessed = false)
      (map.modifyRange offset len (fun _ row => GeneralBorrowFreshMaterialization.materialized row child state)).state := by
  let predicate := fun row => (GeneralBorrowWildcardVirtualLeaf.effective row query node).accessed = false
  have prepared := GeneralRangeMapSafety.iter_mut predicate map offset len well inactive bounds
  rw [GeneralBorrowFreshModify.state_exact map offset len _ well bounds]
  have fold : ∀ (positions : List Nat) (current : DedupRangeMap LocationTree),Every predicate current →
      Every predicate (positions.foldl (fun current position => GeneralBorrowFreshModify.atPosition current position
        (fun _ row => GeneralBorrowFreshMaterialization.materialized row child state)) current) := by
    intro positions
    induction positions with
    | nil => intro current all;exact all
    | cons position rest ih =>
      intro current all
      apply ih
      dsimp only [GeneralBorrowFreshModify.atPosition]
      split
      · rename_i valid
        apply replaced_every _ current position valid _ all
        dsimp only [predicate,GeneralBorrowWildcardVirtualLeaf.effective,GeneralBorrowFreshMaterialization.materialized]
        rw [GeneralBorrowFreshLocation.get_other _ child query state different]
        exact all position valid
      · exact all
  exact fold _ _ prepared.every

theorem shape (before after : BorrowTree) (same : GeneralBorrowView.treeShape after = GeneralBorrowView.treeShape before)
    (query : UniIndex) (node : TreeNode)
    (inactive : Every (fun row => (GeneralBorrowWildcardVirtualLeaf.effective row query node).accessed = false) before.locations) :
    Every (fun row => (GeneralBorrowWildcardVirtualLeaf.effective row query node).accessed = false) after.locations := by
  have entries := congrArg (fun value => value.2.2.1) same
  have sizes : after.locations.entries.size = before.locations.entries.size := by
    simpa only [GeneralBorrowView.treeShape,Array.size_map] using congrArg Array.size entries
  intro position valid
  have oldValid : position < before.locations.entries.size := by omega
  have cell := congrArg (fun rows => rows[position]?) entries
  simp only [GeneralBorrowView.treeShape,Array.getElem?_map,Array.getElem?_eq_getElem valid,
    Array.getElem?_eq_getElem oldValid,Option.map_some,Option.some.injEq,Prod.mk.injEq] at cell
  have state := GeneralBorrowSifaWritableFrame.effective_shape before.locations.entries[position].data
    after.locations.entries[position].data query node node cell.2 rfl
  exact (congrArg Prod.snd state).trans (inactive position oldValid)

/-- The actual mutable child constructor preserves another live tag's inactivity. -/
theorem construct (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (offset len : UInt64) (nonzero : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (query : UniIndex) (node : TreeNode) (queryAt : tree.nodes.get query = some node)
    (inactive : Every (fun row => (GeneralBorrowWildcardVirtualLeaf.effective row query node).accessed = false) tree.locations) :
    Every (fun row => (GeneralBorrowWildcardVirtualLeaf.effective row query node).accessed = false)
      (tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
        (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree.locations := by
  let rank := GeneralBorrowStructuralHistoryMutable.depth tree runtime.formed.toState
  let slot := GeneralBorrowStructuralHistoryMutable.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildMutable.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        noFree,aligned,fits,offset,len,nonzero,runtime.formed.well,bounds⟩
    have vacant : tree.nodes.get (GeneralBorrowFreshMetadataChildMutable.index input) = none := by
      have atEnd : (GeneralBorrowFreshMetadataChildMutable.index input).toNat = tree.nodes.data.size := GeneralBorrowFreshMetadataChildMutable.at_end input
      simp only [UniValMap.get,atEnd,Array.getElem?_eq_none (Nat.le_refl _)]
    have different : query ≠ GeneralBorrowFreshMetadataChildMutable.index input := by intro same;rw [same,vacant] at queryAt;cases queryAt
    have staged := modified tree.locations (GeneralBorrowFreshMetadataChildMutable.index input) query node
      (Size.ofBytes offset) (Size.ofBytes len) GeneralBorrowFreshChild.inside different runtime.formed.well bounds inactive
    exact shape (GeneralBorrowFreshMetadataChildMutable.stage input) (GeneralBorrowFreshMetadataChildMutable.result input)
      (GeneralBorrowFreshMetadataChildMutable.shape input) query node staged
  | reuse index available bounded vacant slack =>
    let input : GeneralBorrowFreshMetadataChildMutableReuse.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        index,available,bounded,vacant,slack,offset,len,nonzero,runtime.formed.well,bounds⟩
    have different : query ≠ index := by intro same;rw [same,vacant] at queryAt;cases queryAt
    have staged := modified tree.locations index query node (Size.ofBytes offset) (Size.ofBytes len)
      GeneralBorrowFreshChild.inside different runtime.formed.well bounds inactive
    exact shape (GeneralBorrowFreshMetadataChildMutableReuse.stage input) (GeneralBorrowFreshMetadataChildMutableReuse.result input)
      (GeneralBorrowFreshMetadataChildMutableReuse.shape input) query node staged

/-- Stored inactive rows, including materialized Disabled states, cause the
real full release scan to skip all implicit accesses. -/
theorem release (tree : BorrowTree) (tag : BorTag) (query : UniIndex) (node : TreeNode)
    (tagged : tree.indexOfTag tag = some query) (present : tree.nodeAt query = some node)
    (hidden : node.isExposed = false)
    (inactive : Every (fun location => (GeneralBorrowWildcardVirtualLeaf.effective location query node).accessed = false) tree.locations)
    (protections : ProtectedTags) : tree.releaseProtector tag protections = ⟨tree,.Released⟩ := by
  apply S04ReturnReleaseInactive.release tree tag query node tagged present hidden
  intro position valid state stored
  left
  simpa only [GeneralBorrowWildcardVirtualLeaf.effective,stored,Option.getD_some] using inactive position valid

end DuplicatePrefix.CurrentCallEmptyEntryQuietRelease
open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CurrentCallEmptyEntryQuietRelease." then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved empty quiet release dependency {dependency}"
