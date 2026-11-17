import duplicate_prefix.CurrentCallEmptyEntryCompleteRelease
import duplicate_prefix.CurrentCallEmptyEntryQuietRelease
import duplicate_prefix.S03EmptyPopFactsWildcard
import duplicate_prefix.S02HiddenLeafQuietWildcardRange
namespace DuplicatePrefix.CurrentCallEmptyEntryQuietCompleteBorrow
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection BorrowRangeAccess GeneralBorrowExposureCardinality GeneralRangeMapState GeneralRangeMapOrigins
open CandidateStableCallOwnership CandidateCurrentJointCall GeneralBorrowExposedNonleafPrimaryPath
open GeneralBorrowWildcardParentTagOrder GeneralBorrowFnEntryRegistration
open S05CompletedAncestryReadMutable (Authority)
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
private theorem wildcard_row (tree : BorrowTree) (graph : GeneralBorrowStructuralHistoryState.GraphState tree)
    (location : LocationTree) (protections : ProtectedTags) (query : UniIndex) (node : TreeNode)
    (present : tree.nodeAt query = some node) (leaf : node.children = #[]) (hidden : node.isExposed = false)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (kind : AccessKind) (mode : ChildrenVisitMode) (range : ByteRange)
    (quiet : (GeneralBorrowWildcardVirtualLeaf.effective location query node).accessed = false) :
    let result := source_access_location (source_tree_access_at tree location none kind protections mode range)
    (GeneralBorrowWildcardVirtualLeaf.effective result query node).accessed = false ∧
      GeneralBorrowExposureCardinality.counter result.exposedCache query kind = 0 := by
  have zero : GeneralBorrowExposureCardinality.counter location.exposedCache query kind = 0 := by
    rw [coherent query kind,S03EmptyPopFactsAuthorization.leaf_cardinality tree location protections graph query node present leaf hidden kind]
    rfl
  unfold_internal ".BorrowTree.performTreeAccessAt"
  simp only [Id.run,bind,pure,Option.bind_none,ite_self,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  name_borrow_range_scan
  let predicate := fun (state : LocationTree × Option BorrowTree.BorrowTreeAccessStatus × Bool) =>
    (GeneralBorrowWildcardVirtualLeaf.effective state.1 query node).accessed = false ∧
      GeneralBorrowExposureCardinality.counter state.1.exposedCache query kind = 0
  have step : ∀ position ∈ List.range' 0 tree.roots.size, ∀ state,
      predicate state → predicate (scan position state).value := by
    intro position member state good
    rcases state with ⟨current,status,stopped⟩
    dsimp only [scan]
    repeat' first | split | simp_all only [Bool.and_eq_true,ForInStep.value]
    all_goals first
      | exact good
      | exact S03EmptyPopFactsWildcard.access tree graph query node present leaf hidden current _ _ kind protections _ good.1 good.2
  exact GeneralBorrowLoop.list_invariant _ scan predicate step (location,none,false) ⟨quiet,zero⟩

private theorem wildcard_range (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (offset len : UInt64) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (query : UniIndex)
    (node : TreeNode) (present : tree.nodeAt query = some node)
    (leaf : node.children = #[]) (hidden : node.isExposed = false)
    (inactive : Every (fun location => (GeneralBorrowWildcardVirtualLeaf.effective location query node).accessed = false) tree.locations)
    (kind : AccessKind) (mode : ChildrenVisitMode) :
    Every (fun location => (GeneralBorrowWildcardVirtualLeaf.effective location query node).accessed = false)
      (tree.performBorrowAccessRange .wildcard (Size.ofBytes offset) (Size.ofBytes len)
        kind global.protectedTags mode).tree.locations := by
  let predicate := fun location => (GeneralBorrowWildcardVirtualLeaf.effective location query node).accessed = false
  let prepared := tree.locations.iterMut (Size.ofBytes offset) (Size.ofBytes len)
  have preparedGood := GeneralRangeMapSafety.iter_mut predicate tree.locations (Size.ofBytes offset) (Size.ofBytes len) runtime.formed.well inactive bounds
  have preparedCoherent := GeneralRangeMapSafety.iter_mut
    (fun location => LocationCoherent tree location global.protectedTags) tree.locations (Size.ofBytes offset) (Size.ofBytes len) runtime.formed.well runtime.coherent bounds
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
      have preserved := (wildcard_row tree runtime.formed.toGraphState segment.data global.protectedTags
        query node present leaf hidden segmentCoherent kind mode segment.range segmentInactive).1
      let access := source_tree_access_at tree segment.data none kind global.protectedTags mode segment.range
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

private theorem prepared_read (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (completion : Completion) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (complete : Completes tree completion) (order : ParentTagOrder tree)
    (pointer : PointerInstance) (node : TreeNode) (present : tree.nodes.get pointer.grant = some node)
    (provenance : match pointer.value.provenance with | .concrete _ tag => tag=node.tag | .wildcard => node.isExposed=true)
    (room : global.nextPointerTag.value < 18446744073709551615)
    (short : tree.nodes.size < 65536) (offset : UInt64) (bounds : offset.toNat+1 ≤ tree.locations.size.bytes.toNat)
    (owned : OwnedOn (Authority tree completion global.protectedTags pointer.grant) offset (offset+1) tree.locations) :
    let output := CurrentCallTypedFnEntry.literal tree global frame allocation room pointer.value.provenance offset 1
    DuplicatePrefixBorrowContract.RuntimeFacts output.access.tree output.global ∧
      Completes output.access.tree completion ∧ output.access.tree.nodes=tree.nodes ∧
      output.access.tree.tagMapping=tree.tagMapping ∧ output.access.tree.locations.size=tree.locations.size := by
  obtain ⟨position,root,rootNode,slot,rootAt,path⟩ := CandidateCurrentWindowAuthority.root_path tree runtime.formed.toGraphState pointer.grant node present
  cases prov : pointer.value.provenance with
  | concrete id tag =>
    have tagEq : tag=node.tag := by simpa only [prov] using provenance
    obtain ⟨_,afterRuntime,afterComplete,_,nodes,_,tags,capacity⟩ := S05ConcreteFnEntryRaw.prepare_read tree global frame allocation completion runtime complete order
      position root pointer.grant rootNode node slot rootAt present path room offset 1 bounds owned short .VisitChildrenOfAccessed
    simpa only [CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,CandidateCurrentWindowPointerChecks.extraOf,prov,tagEq]
      using And.intro afterRuntime (And.intro afterComplete (And.intro nodes (And.intro tags capacity)))
  | wildcard =>
    have exposed : node.isExposed=true := by simpa only [prov] using provenance
    obtain ⟨_,afterRuntime,afterComplete,_,nodes,_,tags,capacity⟩ := S05WildcardFnEntryRaw.prepare_read tree global frame allocation completion runtime complete order
      position root pointer.grant rootNode node slot rootAt present exposed path room offset 1 bounds owned short .VisitChildrenOfAccessed
    simpa only [CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,CandidateCurrentWindowPointerChecks.extraOf,prov]
      using And.intro afterRuntime (And.intro afterComplete (And.intro nodes (And.intro tags capacity)))

private theorem effective_node (map : DedupRangeMap LocationTree) (query : UniIndex) (old next : TreeNode)
    (inactive : Every (fun row => (GeneralBorrowWildcardVirtualLeaf.effective row query old).accessed=false) map) :
    Every (fun row => (GeneralBorrowWildcardVirtualLeaf.effective row query next).accessed=false) map := by
  intro position valid
  have known := inactive position valid
  cases stored : map.entries[position].data.perms.get query with
  | none => simp [GeneralBorrowWildcardVirtualLeaf.effective,stored,TreeNode.defaultLocationState]
  | some state => simpa only [GeneralBorrowWildcardVirtualLeaf.effective,stored,Option.getD_some] using known

private theorem normals (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (complete : Completes tree completion)
    (source : UniIndex) (node : TreeNode) (present : tree.nodeAt source=some node) (short : tree.nodes.size<65536)
    (lower upper : UInt64) (owned : OwnedOn (Authority tree completion global.protectedTags source) lower upper tree.locations) :
    OwnedOn (fun row => Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree row global.protectedTags source)) lower upper tree.locations := by
  obtain ⟨position,root,rootNode,slot,rootAt,path⟩ := CandidateCurrentWindowAuthority.root_path tree runtime.formed.toGraphState source node present
  obtain ⟨depth⟩ := runtime.formed.depth
  intro cursor valid positive start stop
  have authority := owned cursor valid positive start stop
  apply S05CompletedAncestryNormal.normal tree completion _ _ complete runtime.formed.toGraphState depth
    (by change tree.nodes.size≤4294967296;omega) position root source rootNode slot rootAt path
  · intro index current atNode path below;exact (authority index current atNode).1 below
  · intro index current atNode path outside;exact (authority index current atNode).2 outside

private theorem wildcard_construct (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+1≤4294967295)
    (offset : UInt64) (bounds : offset.toNat+1≤tree.locations.size.bytes.toNat)
    (query : UniIndex) (node : TreeNode) (present : tree.nodeAt query=some node)
    (inactive : Every (fun row => (GeneralBorrowWildcardVirtualLeaf.effective row query node).accessed=false) tree.locations) :
    let actual := tree.newChild (Size.ofBytes offset) .wildcard tag
      (DedupRangeMap.new (Size.ofBytes 1) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    actual.tree.nodeAt query=some node ∧
      Every (fun row => (GeneralBorrowWildcardVirtualLeaf.effective row query node).accessed=false) actual.tree.locations := by
  obtain ⟨mapping,index,inserted,rows,vacant,graph,monotone,growth⟩ :=
    GeneralBorrowWildcardConstructorSlot.select tree global runtime tag fresh room (.ReservedFrz false) .None
  have actual := GeneralBorrowWildcardConstructorExact.exact tree runtime.formed.toState tag fresh room mapping index inserted
    (.ReservedFrz false) .None GeneralBorrowFreshChild.inside true rfl rfl rfl rfl rfl offset 1 (by decide) bounds
  have different : query≠index := by
    intro equal
    change tree.nodes.get query=some node at present
    rw [equal,vacant] at present;cases present
  have staged := CurrentCallEmptyEntryQuietRelease.modified tree.locations index query node (Size.ofBytes offset) (Size.ofBytes 1)
    GeneralBorrowFreshChild.inside different runtime.formed.well bounds inactive
  rw [actual]
  constructor
  · change (tree.nodes.insert index _).get query=some node
    rw [GeneralBorrowFreshLocation.get_other _ _ _ _ different];exact present
  · exact staged
/-- A distinct hidden empty-source leaf remains inactive through the exact
complete-case Bool operation, so its same-flags release is an unchanged tree. -/
theorem retained (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (completion : Completion) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (complete : Completes tree completion) (order : ParentTagOrder tree)
    (pointer : PointerInstance) (sourceNode : TreeNode) (present : tree.nodes.get pointer.grant=some sourceNode)
    (provenance : match pointer.value.provenance with | .concrete _ tag => tag=sourceNode.tag | .wildcard => sourceNode.isExposed=true)
    (room : global.nextPointerTag.value < 18446744073709551615)
    (nodeRoom : tree.nodes.size+1≤4294967295) (short : tree.nodes.size+1<65536)
    (offset : UInt64) (bounds : offset.toNat+1≤tree.locations.size.bytes.toNat)
    (owned : OwnedOn (Authority tree completion global.protectedTags pointer.grant) offset (offset+1) tree.locations)
    (borrow : CurrentCallEmptyEntryCompleteRelease.Result tree global frame allocation completion pointer offset room)
    (query : UniIndex) (node : TreeNode) (queryAt : tree.nodeAt query=some node)
    (leaf : node.children=#[]) (hidden : node.isExposed=false) (different : query≠pointer.grant)
    (inactive : Every (fun row => (GeneralBorrowWildcardVirtualLeaf.effective row query node).accessed=false) tree.locations) :
    ∃ next, (CurrentCallEmptyEntryCompleteRelease.written borrow.output offset).tree.nodeAt query=some next ∧
      next.tag=node.tag ∧ next.children=#[] ∧ next.isExposed=false ∧
      Every (fun row => (GeneralBorrowWildcardVirtualLeaf.effective row query next).accessed=false)
        (CurrentCallEmptyEntryCompleteRelease.written borrow.output offset).tree.locations ∧
      (CurrentCallEmptyEntryCompleteRelease.written borrow.output offset).tree.releaseProtector node.tag borrow.output.global.protectedTags =
        ⟨(CurrentCallEmptyEntryCompleteRelease.written borrow.output offset).tree,.Released⟩ := by
  let output := borrow.output
  let literal := CurrentCallTypedFnEntry.literal tree global frame allocation room pointer.value.provenance offset 1
  have outputEq : output=literal := Except.ok.inj (borrow.actual.symm.trans (CurrentCallTypedFnEntry.literal_operation _ _ _ _ room _ _ _))
  obtain ⟨_,_,_,registeredRuntime,nodeFresh,originalFresh⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare tree global frame allocation room runtime
  have flags : ∀ index current,tree.nodes.get index=some current →
      (registered global frame allocation room).1.protectedTags.contains current.tag=global.protectedTags.contains current.tag := by
    intro index current atNode
    exact ProtectorInsertion.contains_other _ _ _ .StrongProtector
      (nodeFresh (index,current) (Array.mem_toList_iff.mp ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes index current).mpr atNode)))
  have registeredOwned : OwnedOn (Authority tree completion (registered global frame allocation room).1.protectedTags pointer.grant)
      offset (offset+1) tree.locations := by
    intro cursor valid positive start stop index current atNode
    rw [flags index current atNode]
    exact owned cursor valid positive start stop index current atNode
  have registeredNormals := normals tree (registered global frame allocation room).1 completion registeredRuntime complete pointer.grant sourceNode
    present (by omega) offset (offset+1) registeredOwned
  obtain ⟨readRuntime,readComplete,readNodes,readTags,readCapacity⟩ := prepared_read tree global frame allocation completion runtime complete order
    pointer sourceNode present provenance room (by omega) offset bounds owned
  change DuplicatePrefixBorrowContract.RuntimeFacts literal.access.tree literal.global at readRuntime
  change Completes literal.access.tree completion at readComplete
  change literal.access.tree.nodes=tree.nodes at readNodes
  change literal.access.tree.tagMapping=tree.tagMapping at readTags
  change literal.access.tree.locations.size=tree.locations.size at readCapacity
  have readAt : literal.access.tree.nodeAt query=some node := by change literal.access.tree.nodes.get query=_;rw [readNodes];exact queryAt
  have sourceAt : literal.access.tree.nodeAt pointer.grant=some sourceNode := by change literal.access.tree.nodes.get pointer.grant=_;rw [readNodes];exact present
  have readBounds : offset.toNat+1≤literal.access.tree.locations.size.bytes.toNat := by rw [readCapacity];exact bounds
  have readRoom : literal.access.tree.nodes.size+1≤4294967295 := by rw [readNodes];exact nodeRoom
  have readFresh : GeneralBorrowTagMap.Fresh literal.access.tree.tagMapping global.nextPointerTag := by rw [readTags];exact originalFresh
  have readInactive : Every (fun row => (GeneralBorrowWildcardVirtualLeaf.effective row query node).accessed=false) literal.access.tree.locations := by
    cases prov : pointer.value.provenance with
    | concrete id tag =>
      have tagEq : tag=sourceNode.tag := by simpa only [prov] using provenance
      have tagged : tree.indexOfTag tag=some pointer.grant := by rw [tagEq];exact (complete.2.2.2.2.1 pointer.grant sourceNode present).1
      have quiet := CurrentCallEmptyEntryQuietRelease.concrete tree (registered global frame allocation room).1 registeredRuntime
        tag pointer.grant query offset 1 bounds registeredNormals sourceNode present tagged node queryAt leaf hidden different inactive .Read .VisitChildrenOfAccessed
      simpa only [literal,CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,CandidateCurrentWindowPointerChecks.extraOf,prov] using quiet
    | wildcard =>
      have quiet := wildcard_range tree (registered global frame allocation room).1 registeredRuntime offset 1 bounds query node queryAt leaf hidden
        inactive .Read .VisitChildrenOfAccessed
      simpa only [literal,CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,CandidateCurrentWindowPointerChecks.extraOf,prov] using quiet
  have constructed : ∃ next,output.child.tree.nodeAt query=some next ∧ next.tag=node.tag ∧ next.children=node.children ∧
      next.isExposed=node.isExposed ∧ Every (fun row => (GeneralBorrowWildcardVirtualLeaf.effective row query next).accessed=false) output.child.tree.locations := by
    cases prov : pointer.value.provenance with
    | concrete id tag =>
      have tagEq : tag=sourceNode.tag := by simpa only [prov] using provenance
      have tagged : literal.access.tree.indexOfTag tag=some pointer.grant := by
        rw [tagEq];exact (readComplete.2.2.2.2.1 pointer.grant sourceNode sourceAt).1
      have quiet := CurrentCallEmptyEntryQuietRelease.construct literal.access.tree literal.global readRuntime tag global.nextPointerTag pointer.grant sourceNode
        tagged sourceAt readFresh readRoom offset 1 (by decide) readBounds query node readAt readInactive
      obtain ⟨next,atNext,nextTag,nextLeaf,nextHidden⟩ := CurrentCallEntryProtectionData.concrete_old_node literal.access.tree literal.global readRuntime
        tag global.nextPointerTag pointer.grant sourceNode tagged sourceAt readFresh readRoom offset 1 (by decide) readBounds query node readAt different
      have quietNext := effective_node _ query node next quiet
      refine ⟨next,?_,nextTag,nextLeaf,nextHidden,?_⟩
      · rw [outputEq]
        simpa only [literal,CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,CandidateCurrentWindowPointerChecks.extraOf,prov,
          GeneralBorrowFreshMetadataChildMutableSlot.result,GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation] using atNext
      · rw [outputEq]
        simpa only [literal,CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,CandidateCurrentWindowPointerChecks.extraOf,prov,
          GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation] using quietNext
    | wildcard =>
      obtain ⟨atNext,quiet⟩ := wildcard_construct literal.access.tree literal.global readRuntime global.nextPointerTag readFresh readRoom offset readBounds query node readAt readInactive
      refine ⟨node,?_,rfl,rfl,rfl,?_⟩
      · rw [outputEq]
        simpa only [literal,CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,CandidateCurrentWindowPointerChecks.extraOf,prov,
          GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation] using atNext
      · rw [outputEq]
        simpa only [literal,CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,CandidateCurrentWindowPointerChecks.extraOf,prov,
          GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation] using quiet
  obtain ⟨next,nextAt,nextTag,nextLeaf,nextHidden,nextInactive⟩ := constructed
  obtain ⟨actual,actualEq,_,_,_,_,childRuntime,child,lookup,childComplete,childOwned,metadata,_⟩ :=
    CandidateCurrentFnEntryRaw.source_only tree global frame allocation completion runtime complete order pointer sourceNode present provenance
      room nodeRoom (by omega) offset 1 (by decide) bounds owned
  have actualSame : actual=borrow.output := Except.ok.inj (actualEq.symm.trans borrow.actual)
  subst actual
  have childSame : child=borrow.child := Option.some.inj (lookup.symm.trans borrow.lookup)
  subst child
  have afterBounds : offset.toNat+1≤output.child.tree.locations.size.bytes.toNat := by rw [metadata.capacity];exact bounds
  have afterShort : output.child.tree.nodes.size<65536 := Nat.lt_of_le_of_lt metadata.growth short
  have childNormals := normals output.child.tree output.global _ childRuntime childComplete borrow.child borrow.node borrow.childAt afterShort offset (offset+1) childOwned
  have freshTag : global.nextPointerTag≠node.tag :=
    Ne.symm (nodeFresh (query,node) (Array.mem_toList_iff.mp ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes query node).mpr queryAt)))
  have notChild : query≠borrow.child := by
    intro same
    have atSame : output.child.tree.nodeAt borrow.child=some next := by simpa only [same] using nextAt
    have nodeEq : next=borrow.node := Option.some.inj (atSame.symm.trans borrow.childAt)
    exact freshTag (borrow.tag.symm.trans (borrow.nodeTag.symm.trans ((congrArg TreeNode.tag nodeEq).symm.trans nextTag)))
  have tagged : output.child.tree.indexOfTag borrow.node.tag=some borrow.child := by rw [borrow.nodeTag];exact borrow.lookup
  have quiet := CurrentCallEmptyEntryQuietRelease.concrete output.child.tree output.global childRuntime borrow.node.tag borrow.child query offset 1
    afterBounds childNormals borrow.node borrow.childAt tagged next nextAt (nextLeaf.trans leaf) (nextHidden.trans hidden) notChild nextInactive .Write .VisitChildrenOfAccessed
  rw [borrow.nodeTag] at quiet
  let written := CurrentCallEmptyEntryCompleteRelease.written output offset
  have finalAt : written.tree.nodeAt query=some next := by change written.tree.nodes.get query=_;rw [borrow.writeNodes];exact nextAt
  have finalTagged : written.tree.indexOfTag node.tag=some query := by
    rw [←nextTag]
    exact borrow.writeRuntime.formed.allocator.nodeTags query next finalAt
  have release := CurrentCallEmptyEntryQuietRelease.release written.tree node.tag query next finalTagged finalAt (nextHidden.trans hidden) quiet output.global.protectedTags
  exact ⟨next,finalAt,nextTag,nextLeaf.trans leaf,nextHidden.trans hidden,quiet,release⟩

end
end DuplicatePrefix.CurrentCallEmptyEntryQuietCompleteBorrow
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallEmptyEntryQuietCompleteBorrow" then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved quiet complete Bool dependency {dependency}"
