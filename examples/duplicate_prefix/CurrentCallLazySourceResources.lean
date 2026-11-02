import duplicate_prefix.CurrentCallLazyTypedSourceCopy
import duplicate_prefix.S05CompletedRootOrigins
import duplicate_prefix.S05ConcreteFnEntryRaw
import duplicate_prefix.CurrentCallParentInsertion

namespace DuplicatePrefix.CurrentCallLazySourceResources
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources CurrentCallResourceNormalization
open OrdinaryBorrowAuthority
open GeneralBorrowFullSharedSeed GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowWildcardParentTagOrder GeneralRangeMapOrigins
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

private theorem root_cases (tag : BorTag) (capacity : UInt64) (nonzero : capacity≠0) (index : UniIndex) (value : TreeNode)
    (present : (BorrowTree.new tag (Size.ofBytes capacity)).nodes.get index=some value) :
    index=allocationRoot ∧value=GeneralBorrowFullSharedSeed.node tag := by
  have shape:=tree_eq capacity nonzero tag
  change BorrowTree.new tag (Size.ofBytes capacity)=_ at shape
  have bounded:=GeneralBorrowNodeUpdate.lookup_valid (BorrowTree.new tag (Size.ofBytes capacity)).nodes index value present
  rw [shape] at bounded
  have same : index=allocationRoot:=GeneralBorrowNodeUpdate.index_injective index allocationRoot (by change index.toNat=0;change index.toNat<1 at bounded;omega)
  subst index
  have nodeEq : value=GeneralBorrowFullSharedSeed.node tag := by rw [shape] at present;exact (Option.some.inj present).symm
  exact ⟨rfl,nodeEq⟩

private theorem root_order (tag : BorTag) (capacity : UInt64) (nonzero : capacity≠0) :
    ParentTagOrder (BorrowTree.new tag (Size.ofBytes capacity)) := by
  intro child childNode childAt parent parentNode edge parentAt
  obtain ⟨rfl,rfl⟩:=root_cases tag capacity nonzero child childNode childAt
  cases edge

private theorem root_completion (tag : BorTag) (capacity : UInt64) (nonzero : capacity≠0)
    (global : GlobalState) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts (BorrowTree.new tag (Size.ofBytes capacity)) global) :
    ∃ C,Completes (BorrowTree.new tag (Size.ofBytes capacity)) C := by
  apply S05CompletedRootOrigins.exists_completion _ runtime.formed.toGraphState (by change [allocationRoot].Nodup;simp) (root_order tag capacity nonzero)
  intro position root slot different
  have valid:=(Array.getElem?_eq_some_iff.mp slot).1
  change position<1 at valid
  exact False.elim (different (by omega))

private theorem seed_owned (tag : BorTag) (capacity offset len : UInt64) (nonzero : capacity≠0)
    (held : ProtectedTags) (completion : Completion) :
    OwnedOn (S05CompletedAncestryReadMutable.Authority (BorrowTree.new tag (Size.ofBytes capacity)) completion held allocationRoot)
      offset (offset+len) (BorrowTree.new tag (Size.ofBytes capacity)).locations := by
  have shape := tree_eq capacity nonzero tag
  change BorrowTree.new tag (Size.ofBytes capacity)=_ at shape
  intro position valid positive start stop index node present
  have positionZero : position=0 := by rw [shape] at valid;change position<1 at valid;omega
  subst position
  have bounded := GeneralBorrowNodeUpdate.lookup_valid (BorrowTree.new tag (Size.ofBytes capacity)).nodes index node present
  rw [shape] at bounded
  have indexZero : index=allocationRoot := GeneralBorrowNodeUpdate.index_injective index allocationRoot (by change index.toNat=0;change index.toNat<1 at bounded;omega)
  subst index
  have actual : node=GeneralBorrowFullSharedSeed.node tag := by rw [shape] at present;exact (Option.some.inj present).symm
  subst node
  refine ⟨?_,fun outside=>False.elim (outside (.refl allocationRoot))⟩
  intro below
  simp only [shape]
  change LocalWrite GeneralBorrowWildcardLeaf.unique (held.contains tag)
  simp [LocalWrite,GeneralBorrowWildcardLeaf.unique,LocationState.possible,Permission.isUnique]


private theorem parents_of_complete (tree : BorrowTree) (C : Completion)
    (complete : Completes tree C) (global : GlobalState) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (order : ParentTagOrder tree) (roots : tree.roots=#[allocationRoot]) : ParentInterpretation tree C := by
  have primary : tree.roots[0]?=some allocationRoot:=by rw [roots];rfl
  have first:=complete.2.2.2.2.2.1 0 allocationRoot primary
  have primaryNone : C.parents[allocationRoot.toNat]?=some none:=by simpa using first
  refine ⟨runtime.formed.toGraphState,order,complete.1,?_,?_,primaryNone,?_⟩
  · intro index node present parent edge
    exact (complete.2.2.2.2.1 index node present).2.2.1 parent edge
  · intro child parent edge
    exact ⟨(complete.2.2.2.2.2.2 child parent edge).1,(complete.2.2.2.2.2.2 child parent edge).2.1⟩
  · intro position root slot origin edge
    have valid:=(Array.getElem?_eq_some_iff.mp slot).1
    rw [roots] at valid
    have zero : position=0:=by change position<1 at valid;omega
    subst position
    have same : root=allocationRoot:=Option.some.inj (slot.symm.trans primary)
    subst root
    rw [primaryNone] at edge
    cases edge

/-- Pure resource facts for the SINGLE root actually born by lazy ensure and
its SAME protected child constructor. No initial live-source predicate occurs. -/
structure Stage (global : GlobalState) (frame : FrameState) (id : AllocId) (root : BorTag)
    (capacity offset len : UInt64) (room : global.nextPointerTag.value<18446744073709551615) where
  initialCompletion : Completion
  output : GeneralBorrowForestFnEntry.Output
  operation : GeneralBorrowForestFnEntry.operation (BorrowTree.new root (Size.ofBytes capacity)) global frame id root offset len .VisitChildrenOfAccessed=.ok output
  tag : output.tag=global.nextPointerTag
  globalEq : output.global=(GeneralBorrowFnEntryRegistration.registered global frame id room).1
  treeEq : output.child.tree=PositiveGlobalTypedReborrow.finalTree root global.nextPointerTag (Size.ofBytes capacity) output.global.protectedTags offset len
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree output.global
  size : output.child.tree.locations.size=Size.ofBytes capacity
  growth : output.child.tree.nodes.size≤2
  child : UniIndex
  lookup : output.child.tree.indexOfTag output.tag=some child
  roots : output.child.tree.roots=#[allocationRoot]
  parents : ParentInterpretation output.child.tree (S05ConcreteProtectedChildCompletion.extend initialCompletion child allocationRoot)
  owned : OwnedOn (S05CompletedAncestryReadMutable.Authority output.child.tree
    (S05ConcreteProtectedChildCompletion.extend initialCompletion child allocationRoot) output.global.protectedTags child)
    offset (offset+len) output.child.tree.locations
  activity : GeneralBorrowFreshActiveWithin.ActiveWithin output.child.tree child .Write offset (offset+len)
  node : TreeNode
  nodeAt : output.child.tree.nodes.get child=some node
  nodeTag : node.tag=output.tag
  hidden : node.isExposed=false
  physical : node.parent=some allocationRoot
  rootNode : TreeNode
  rootAt : output.child.tree.nodes.get allocationRoot=some rootNode
  rootTag : rootNode.tag=root
  rootParent : rootNode.parent=none
  rootDisabled : rootNode.defaultInitialPermission=.Disabled

theorem construct (global : GlobalState) (frame : FrameState) (id : AllocId) (root : BorTag)
    (capacity offset len : UInt64) (room : global.nextPointerTag.value<18446744073709551615)
    (positive : 0<len.toNat) (bounds : offset.toNat+len.toNat≤capacity.toNat)
    (rootBelow : root.value.toNat<global.nextPointerTag.value.toNat)
    (protectorBelow : ∀ row∈global.protectedTags.entries,row.1.value.toNat<global.nextPointerTag.value.toNat) :
    Nonempty (Stage global frame id root capacity offset len room) := by
  have nonzeroCapacity : capacity≠0:=by intro zero;rw [zero] at bounds;simp only [UInt64.toNat_zero] at bounds;omega
  have nonzero : len≠0:=by intro zero;rw [zero] at positive;contradiction
  let tree:=BorrowTree.new root (Size.ofBytes capacity)
  have shape:=GeneralBorrowFullSharedSeed.tree_eq capacity nonzeroCapacity root
  change tree=_ at shape
  have runtime:=PositiveGlobalFnEntryInput.new_runtime root capacity nonzeroCapacity global rootBelow protectorBelow
  obtain ⟨C,complete⟩:=root_completion root capacity nonzeroCapacity global runtime
  have order:=root_order root capacity nonzeroCapacity
  have rootAt : tree.nodes.get allocationRoot=some (GeneralBorrowFullSharedSeed.node root):=BorrowTree.new_root_node _ _
  have path : Path tree allocationRoot allocationRoot:=.refl _ _ rootAt
  have short : tree.nodes.size<65536:=by rw [shape];change (1 : Nat)<65536;decide
  have nodeRoom : tree.nodes.size+1≤4294967295:=by rw [shape];change (2 : Nat)≤4294967295;decide
  have bound : offset.toNat+len.toNat≤tree.locations.size.bytes.toNat:=by rw [shape];exact bounds
  have oldOwned:=seed_owned root capacity offset len nonzeroCapacity global.protectedTags C
  obtain ⟨output,actual,tag,globalEq,frameEq,readDone,childDone,afterRuntime,size,growth,child,lookup,roots,afterComplete,owned,normals,ancestry,activity,afterOrder,oldNodes,⟨childNode,childAt,childTag⟩⟩:=
    S05ConcreteFnEntryRaw.invoke tree global frame id C runtime complete order 0 allocationRoot allocationRoot
      (GeneralBorrowFullSharedSeed.node root) (GeneralBorrowFullSharedSeed.node root) rfl rootAt rootAt path room nodeRoom short offset len nonzero bound oldOwned
  have normalized:=CurrentCallTypedFnEntry.literal_operation tree global frame id room (.concrete id root) offset len
  have outputEq : output=CurrentCallTypedFnEntry.literal tree global frame id room (.concrete id root) offset len:=Except.ok.inj (actual.symm.trans normalized)
  have treeEq : output.child.tree=PositiveGlobalTypedReborrow.finalTree root global.nextPointerTag (Size.ofBytes capacity) output.global.protectedTags offset len:=by
    rw [outputEq]
    rfl
  obtain ⟨_,readRuntime,_,_,readNodes,readRoots,readTags,readCapacity⟩:=S05ConcreteFnEntryRaw.prepare_read tree global frame id C runtime complete order
    0 allocationRoot allocationRoot (GeneralBorrowFullSharedSeed.node root) (GeneralBorrowFullSharedSeed.node root) rfl rootAt rootAt path room offset len bound oldOwned short .VisitChildrenOfAccessed
  let accessed:=(CurrentCallTypedFnEntry.literal tree global frame id room (.concrete id root) offset len).access.tree
  change DuplicatePrefixBorrowContract.RuntimeFacts accessed (GeneralBorrowFnEntryRegistration.registered global frame id room).1 at readRuntime
  change accessed.nodes=tree.nodes at readNodes
  change accessed.tagMapping=tree.tagMapping at readTags
  change accessed.locations.size=tree.locations.size at readCapacity
  have parentAt : accessed.nodeAt allocationRoot=some (GeneralBorrowFullSharedSeed.node root):=by change accessed.nodes.get _=_;rw [readNodes];exact rootAt
  have tagged : accessed.indexOfTag root=some allocationRoot:=readRuntime.formed.allocator.nodeTags _ _ parentAt
  obtain ⟨_,held,_,_,_,fresh⟩:=GeneralBorrowFnEntryRegistrationRuntime.prepare tree global frame id room runtime
  have afterFresh : GeneralBorrowTagMap.Fresh accessed.tagMapping global.nextPointerTag:=by rw [readTags];exact fresh
  have afterRoom : accessed.nodes.size+1≤4294967295:=by rw [readNodes];exact nodeRoom
  have afterBound : offset.toNat+len.toNat≤accessed.locations.size.bytes.toNat:=by rw [readCapacity];exact bound
  obtain ⟨hiddenChild,hiddenLookup,⟨node,nodeAt,nodeTag,hidden⟩,_,_⟩:=GeneralBorrowProtectedChildMetadata.construct accessed _ readRuntime root global.nextPointerTag allocationRoot
    (GeneralBorrowFullSharedSeed.node root) tagged parentAt afterFresh afterRoom offset len nonzero afterBound
  have treeHidden : GeneralBorrowFreshMetadataChildMutableSlot.result accessed root global.nextPointerTag offset len=output.child.tree := by rw [outputEq];rfl
  rw [treeHidden] at hiddenLookup nodeAt
  have sameChild : hiddenChild=child:=Option.some.inj (hiddenLookup.symm.trans (tag ▸ lookup))
  subst hiddenChild
  have tagBound : global.nextPointerTag.value.toNat<(GeneralBorrowFnEntryRegistration.registered global frame id room).1.nextPointerTag.value.toNat:=by
    have successor:=GenericFunctionEntryNumerics.successor_value global.nextPointerTag room
    change global.nextPointerTag.value.toNat<(TypedRetagEmpty.successorTag global.nextPointerTag room).value.toNat
    omega
  have isHeld : (GeneralBorrowFnEntryRegistration.registered global frame id room).1.protectedTags.contains global.nextPointerTag=true:=by
    unfold ProtectedTags.contains
    rw [held]
    rfl
  obtain ⟨_,_,_,_,frameChild,frameLookup,leaf,metadata⟩:=CurrentCallParentInsertion.concrete_frame accessed _ readRuntime root global.nextPointerTag allocationRoot
    (GeneralBorrowFullSharedSeed.node root) tagged parentAt afterFresh afterRoom tagBound isHeld offset len nonzero afterBound
  have literalTree : (accessed.newChild (Size.ofBytes offset) (.concrete root) global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree=output.child.tree :=by rw [outputEq];rfl
  rw [literalTree] at frameLookup leaf metadata
  have frameChildEq : frameChild=child:=Option.some.inj (frameLookup.symm.trans (tag ▸ lookup))
  subst frameChild
  obtain ⟨actualNode,actualAt,actualParent⟩:=leaf.childLive
  have sameNode : actualNode=node:=Option.some.inj (actualAt.symm.trans nodeAt)
  have physical : node.parent=some allocationRoot:=sameNode ▸ actualParent
  obtain ⟨newRoot,newRootAt,newRootTag,newRootParent,_,newRootPermission⟩:=metadata allocationRoot (GeneralBorrowFullSharedSeed.node root) parentAt
  have rootsAfter : output.child.tree.roots=#[allocationRoot]:=roots
  have model:=parents_of_complete output.child.tree (S05ConcreteProtectedChildCompletion.extend C child allocationRoot) afterComplete output.global afterRuntime afterOrder rootsAfter
  have oldSize : tree.locations.size=Size.ofBytes capacity:=by rw [shape];rfl
  exact ⟨⟨C,output,actual,tag,globalEq,treeEq,afterRuntime,size.trans oldSize,by rw [shape] at growth;exact growth,
    child,lookup,roots,model,owned,activity,node,nodeAt,nodeTag.trans tag.symm,hidden,physical,newRoot,newRootAt,newRootTag,newRootParent,newRootPermission⟩⟩

private theorem local_token (state : LocationState) (held : Bool)
    (realized : Realized state held) (right : OrdinaryBorrowAuthority.LocalWrite state held) :
    .exclusive ∈ tokens (denote state held) := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflicted => cases conflicted <;> cases accessed <;> cases held <;>
      simp_all [OrdinaryBorrowAuthority.LocalWrite,Realized,WellFormed,denote,tokens,LocationState.possible]
  | Cell | ReservedIM | Unique | Frozen | Disabled => cases accessed <;> cases held <;>
      simp_all [OrdinaryBorrowAuthority.LocalWrite,Realized,WellFormed,denote,tokens,LocationState.possible,Permission.isUnique]

private theorem foreign_no_clash (state : LocationState) (held : Bool)
    (realized : Realized state held) (right : OrdinaryBorrowAuthority.ForeignWrite state held) :
    ¬Clash (guard (denote state held)) .exclusive := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflicted => cases conflicted <;> cases accessed <;> cases held <;>
      simp_all [OrdinaryBorrowAuthority.ForeignWrite,Realized,WellFormed,denote,CandidateCurrentGrantResources.guard,Clash,LocationState.possible]
  | Cell | ReservedIM | Unique | Frozen | Disabled => cases accessed <;> cases held <;>
      simp_all [OrdinaryBorrowAuthority.ForeignWrite,Realized,WellFormed,denote,CandidateCurrentGrantResources.guard,Clash,LocationState.possible,Permission.isUnique]


/-- The actual copied heap row, not a pre-materialized source domain, installs
canonical root capability and the real child issuance. -/
theorem at_post (global : GlobalState) (frame : FrameState) (id : AllocId) (root : BorTag)
    (source : Allocation CtfeProvenance Unit) (converted : Allocation Provenance Unit)
    (attributes : GlobalAllocationAttributes.Attributes source converted)
    (storage : source.len=source.byteSize.bytes.toNat) (rootCached : global.rootTag? id=some root)
    (offset len : UInt64) (room : global.nextPointerTag.value<18446744073709551615)
    (stage : Stage global frame id root source.byteSize.bytes offset len room)
    (bounds : offset.toNat+len.toNat≤source.byteSize.bytes.toNat)
    (base : UInt64) (post : Before) (next : MachineHooks.BorrowState) (globalEq : next.global=stage.output.global)
    (present : Present (ActualWorld post) id (converted.mapExtra (fun _=>stage.output.child.tree)))
    (data : Identities) :
    ∃ nextData nextOwner,
    ∃ current : UniformWindow post next nextData nextOwner id offset.toNat len.toNat .mut,
      current.pointer=⟨id,Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes (base+offset)),stage.child⟩ ∧
      current.allocation=converted.mapExtra (fun _=>stage.output.child.tree) ∧
      current.precise.completion=S05ConcreteProtectedChildCompletion.extend stage.initialCompletion stage.child allocationRoot := by
  let allocation:=converted.mapExtra (fun _=>stage.output.child.tree)
  let C:=S05ConcreteProtectedChildCompletion.extend stage.initialCompletion stage.child allocationRoot
  let pointer : PointerInstance:=⟨id,Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes (base+offset)),stage.child⟩
  have cap : AllocationCapability post next id allocation := by
    refine ⟨present,?_,?_,?_,stage.rootNode,stage.rootAt,stage.rootParent,stage.rootDisabled,?_⟩
    · change converted.len=converted.byteSize.bytes.toNat
      rw [attributes.storage,attributes.size]
      exact storage
    · change stage.output.child.tree.locations.size=converted.byteSize
      rw [stage.size,attributes.size]
      rfl
    · change stage.output.child.tree.roots[0]?=some allocationRoot
      rw [stage.roots]
      rfl
    · rw [globalEq,stage.globalEq,stage.rootTag]
      exact rootCached
  have issued : SpatialDelegation post next id allocation C stage.child:=
    .concrete (.allocated cap) (.step (.refl allocationRoot stage.rootNode stage.rootAt) stage.node stage.nodeAt stage.physical)
  have binding : PointerBinds allocation pointer := by
    refine ⟨stage.node,stage.nodeAt,stage.runtime.formed.allocator.nodeTags _ _ stage.nodeAt,?_⟩
    exact ⟨rfl,stage.tag.symm.trans stage.nodeTag.symm⟩
  have window : ∀byte,Window id offset.toNat len.toNat byte→byte.2<allocation.len ∧
      Embeds allocation next.global.protectedTags C stage.child byte.2 .exclusive := by
    intro byte inside
    have length : allocation.len=source.byteSize.bytes.toNat:=by change converted.len=_;rw [attributes.storage];exact storage
    refine ⟨by rw [length];have interval:=inside.2;omega,?_⟩
    have noWrap : offset.toNat+len.toNat<2^64:=Nat.lt_of_le_of_lt bounds (UInt64.toNat_lt _)
    have endEq : (offset+len).toNat=offset.toNat+len.toNat:=by simp only [UInt64.toNat_add,Nat.mod_eq_of_lt noWrap]
    have byteLower : offset.toNat≤byte.2:=inside.2.1
    have byteUpper : byte.2<(offset+len).toNat:=by have interval:=inside.2;omega
    intro segment member lower upper index node found
    dsimp only [allocation,Allocation.mapExtra] at member lower upper found ⊢
    obtain ⟨position,valid,same⟩:=Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
    subst segment
    have rights:=stage.owned position valid (by omega) (by omega) (by omega) index node found
    have realized:=CandidateCurrentGrantRuntime.realized _ _ (stage.runtime.possible position valid index node found)
      ((stage.runtime.formed.profile position valid).present index node found)
    rw [globalEq]
    constructor
    · intro below
      exact local_token _ _ realized (rights.1 below)
    · intro clash
      apply Classical.byContradiction
      intro outside
      exact foreign_no_clash _ _ realized (rights.2 outside) clash
  let precise : PreciseAllocation:=⟨C,#[]⟩
  let nextData : Identities:={data with interpretation:={data.interpretation with
    pointers:=data.interpretation.pointers.push pointer
    loans:=data.interpretation.loans.push ⟨data.interpretation.pointers.size,none,0⟩
    precise:=data.interpretation.precise.push (id,precise)}}
  let current : UniformWindow post next nextData data.interpretation.loans.size id offset.toNat len.toNat .mut:={
    loan:=⟨data.interpretation.pointers.size,none,0⟩,pointer:=pointer,allocation:=allocation,precise:=precise,
    loanAt:=by simp [nextData],pointerAt:=by simp [nextData],pointerId:=rfl,present:=present,
    preciseAt:=by simp [nextData],binding:=binding,issued:=issued,parents:=stage.parents,window:=window}
  exact ⟨nextData,data.interpretation.loans.size,current,rfl,rfl,rfl⟩


/-- The SAME actual lazy-source copy supplies its current child resource and
retains the current Bool family; no future resource or copy outcome is an input. -/
theorem invoke_with_binding (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : Before) (tracker : MachineHooks.BorrowState)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker=some borrowFrame)
    (id : AllocId) (root : BorTag) (source : Allocation CtfeProvenance Unit) (base offset len : UInt64) (pointer : Pointer Provenance)
    (ready : CurrentCallLazyCurrentDescriptor.Ready options (Storage.withCurrent frames frame before) tracker id root source base offset len pointer)
    (noFunction : before.memory.hasFunctionPointer id=false) (noVaList : before.memory.hasVaListId id=false)
    (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (preciseOff : options.retag.preciseInteriorMut=false) (implicitOff : options.retag.implicitWrites=false)
    (nullComparator : ProjectionMetadataFacts.NullComparator) (dynamicFuel validationFuel : Nat)
    (fuelEq : options.place.dynamicFuel=dynamicFuel+1) (validationEq : options.limits.validation=validationFuel+1)
    (metadata : before.user.payload.payload.user.types.metadata=PreparedReflection.actual.runtime)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins before.user.payload.payload.user.types)
    (debugOff : options.place.debugAssertions=false) (ghostOff : before.user.payload.ghost=false)
    (shallowMode : before.user.payload.validation=.Shallow)
    (localId : MIR.LocalId) (valid : localId<frame.locals.size)
    (old : Immediate Provenance) (live : frame.locals[localId].value=.live (.immediate old))
    (cached : frame.locals[localId].layout=some ActualReferenceMetadata.reference) (noClocks : frame.extra.dataRace=none)
    {data sourceOwner boolOwner boolId boolOffset}
    (license : CurrentCallLazyCurrentDescriptor.License data id offset len sourceOwner boolOwner boolId boolOffset)
    (B : UniformWindow before tracker data boolOwner boolId boolOffset 1 .ret)
    (boolRuntime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra tracker.global) :
    ∃ (converted : Allocation Provenance Unit) (stage : Stage tracker.global borrowFrame id root source.byteSize.bytes offset len room),
      GlobalAllocationAttributes.Attributes source converted ∧
    let copied:=CurrentCallTypedSourceCopy.copiedFrame options remaining span frame localId valid pointer len
    let validCopied : localId<copied.locals.size:=by simpa only [copied,CurrentCallTypedSourceCopy.copiedFrame,Array.size_set] using valid
    let doneFrame:=CurrentCallTypedSourceCopy.writtenFrame options remaining span copied borrowFrame localId validCopied pointer len id tracker.global.nextPointerTag
    let inner:=CurrentCallLazyTypedSourceCopy.validated options frames copied borrowFrame before tracker room id root source converted offset len
    let post:={inner with borrowTracker:=some (CurrentCallLazyTypedSource.nextTracker tracker room)}
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
      ⟨.immediate (CurrentCallTypedSourceCopy.value options remaining span pointer len).imm,ActualReferenceMetadata.reference⟩
      (LocalPlaces.localRuntimePlace frames.size frame localId ActualReferenceMetadata.reference).stackView
      (Storage.withCurrent frames frame (ScopedFrame.entered before tracker .FnEntry))=
      .ok () (Storage.withCurrent frames doneFrame inner) ∧
    MachineHooks.withRetagMode .FnEntry
      ((ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
        ⟨.immediate (CurrentCallTypedSourceCopy.value options remaining span pointer len).imm,ActualReferenceMetadata.reference⟩
        (LocalPlaces.localRuntimePlace frames.size frame localId ActualReferenceMetadata.reference).stackView)
      (Storage.withCurrent frames frame before)=.ok () (Storage.withCurrent frames doneFrame post) ∧
    stage.output.global=(CurrentCallLazyTypedSource.nextTracker tracker room).global ∧
    (∃ qData qOwner,∃ Q : UniformWindow post (CurrentCallLazyTypedSource.nextTracker tracker room) qData qOwner id offset.toNat len.toNat .mut,
      Q.pointer=⟨id,Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset)),stage.child⟩ ∧
      Q.allocation=converted.mapExtra (fun _=>stage.output.child.tree) ∧
      Q.precise.completion=S05ConcreteProtectedChildCompletion.extend stage.initialCompletion stage.child allocationRoot) ∧
    (∃ current : UniformWindow post (CurrentCallLazyTypedSource.nextTracker tracker room) data boolOwner boolId boolOffset 1 .ret,
      current.pointer=B.pointer ∧current.allocation=B.allocation ∧current.precise=B.precise) ∧
    CandidateCallBindings.WindowBinding post (CurrentCallTypedFnEntry.changedPointer pointer id tracker.global.nextPointerTag) id offset.toNat len.toNat := by
  obtain ⟨converted,attributes,checked,copy,scopedResult,tracked,sourceLive,binding,frameBorrowed,frameSize,localValue,ghost,types,addresses,threads,race,⟨Bpost,bPointer,bAllocation,bPrecise⟩⟩:=
    CurrentCallLazyTypedSourceCopy.invoke options limits remaining span before tracker frames frame borrowFrame frameBorrow
      id root source base offset len pointer ready noFunction noVaList room preciseOff implicitOff nullComparator dynamicFuel validationFuel fuelEq validationEq
      metadata origins debugOff ghostOff shallowMode localId valid old live cached noClocks license B boolRuntime
  obtain ⟨stage⟩:=construct tracker.global borrowFrame id root source.byteSize.bytes offset len room ready.window.positive ready.window.bounds ready.rootBelow ready.protectors
  have globalEq : stage.output.global=(CurrentCallLazyTypedSource.nextTracker tracker room).global:=by rw [stage.globalEq];rfl
  have treeEq:=stage.treeEq
  rw [globalEq] at treeEq
  let copied:=CurrentCallTypedSourceCopy.copiedFrame options remaining span frame localId valid pointer len
  let inner:=CurrentCallLazyTypedSourceCopy.validated options frames copied borrowFrame before tracker room id root source converted offset len
  let post:={inner with borrowTracker:=some (CurrentCallLazyTypedSource.nextTracker tracker room)}
  have actualLive : post.memory.live.find? (fun row=>row.1==id)=some (id,⟨.machine .global,converted.mapExtra (fun _=>stage.output.child.tree)⟩):=by
    rw [treeEq]
    exact sourceLive
  have present : Present (ActualWorld post) id (converted.mapExtra (fun _=>stage.output.child.tree)) := by
    simp only [Present,ActualWorld,Array.toList_map]
    exact List.mem_map.mpr ⟨(id,⟨.machine .global,converted.mapExtra (fun _=>stage.output.child.tree)⟩),
      Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some actualLive),rfl⟩
  obtain ⟨qData,qOwner,Q,qPointer,qAllocation,qCompletion⟩:=at_post tracker.global borrowFrame id root source converted attributes ready.storage ready.rootCached
    offset len room stage ready.window.bounds base post (CurrentCallLazyTypedSource.nextTracker tracker room) globalEq.symm present data
  exact ⟨converted,stage,attributes,copy,scopedResult,globalEq,⟨qData,qOwner,Q,qPointer,qAllocation,qCompletion⟩,⟨Bpost,bPointer,bAllocation,bPrecise⟩,binding⟩

/-- Preserve the existing resource endpoint as a projection of the same copy. -/
theorem invoke (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : Before) (tracker : MachineHooks.BorrowState)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker=some borrowFrame)
    (id : AllocId) (root : BorTag) (source : Allocation CtfeProvenance Unit) (base offset len : UInt64) (pointer : Pointer Provenance)
    (ready : CurrentCallLazyCurrentDescriptor.Ready options (Storage.withCurrent frames frame before) tracker id root source base offset len pointer)
    (noFunction : before.memory.hasFunctionPointer id=false) (noVaList : before.memory.hasVaListId id=false)
    (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (preciseOff : options.retag.preciseInteriorMut=false) (implicitOff : options.retag.implicitWrites=false)
    (nullComparator : ProjectionMetadataFacts.NullComparator) (dynamicFuel validationFuel : Nat)
    (fuelEq : options.place.dynamicFuel=dynamicFuel+1) (validationEq : options.limits.validation=validationFuel+1)
    (metadata : before.user.payload.payload.user.types.metadata=PreparedReflection.actual.runtime)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins before.user.payload.payload.user.types)
    (debugOff : options.place.debugAssertions=false) (ghostOff : before.user.payload.ghost=false)
    (shallowMode : before.user.payload.validation=.Shallow)
    (localId : MIR.LocalId) (valid : localId<frame.locals.size)
    (old : Immediate Provenance) (live : frame.locals[localId].value=.live (.immediate old))
    (cached : frame.locals[localId].layout=some ActualReferenceMetadata.reference) (noClocks : frame.extra.dataRace=none)
    {data sourceOwner boolOwner boolId boolOffset}
    (license : CurrentCallLazyCurrentDescriptor.License data id offset len sourceOwner boolOwner boolId boolOffset)
    (B : UniformWindow before tracker data boolOwner boolId boolOffset 1 .ret)
    (boolRuntime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra tracker.global) :
    ∃ (converted : Allocation Provenance Unit) (stage : Stage tracker.global borrowFrame id root source.byteSize.bytes offset len room),
      GlobalAllocationAttributes.Attributes source converted ∧
    let copied:=CurrentCallTypedSourceCopy.copiedFrame options remaining span frame localId valid pointer len
    let validCopied : localId<copied.locals.size:=by simpa only [copied,CurrentCallTypedSourceCopy.copiedFrame,Array.size_set] using valid
    let doneFrame:=CurrentCallTypedSourceCopy.writtenFrame options remaining span copied borrowFrame localId validCopied pointer len id tracker.global.nextPointerTag
    let inner:=CurrentCallLazyTypedSourceCopy.validated options frames copied borrowFrame before tracker room id root source converted offset len
    let post:={inner with borrowTracker:=some (CurrentCallLazyTypedSource.nextTracker tracker room)}
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
      ⟨.immediate (CurrentCallTypedSourceCopy.value options remaining span pointer len).imm,ActualReferenceMetadata.reference⟩
      (LocalPlaces.localRuntimePlace frames.size frame localId ActualReferenceMetadata.reference).stackView
      (Storage.withCurrent frames frame (ScopedFrame.entered before tracker .FnEntry))=
      .ok () (Storage.withCurrent frames doneFrame inner) ∧
    MachineHooks.withRetagMode .FnEntry
      ((ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
        ⟨.immediate (CurrentCallTypedSourceCopy.value options remaining span pointer len).imm,ActualReferenceMetadata.reference⟩
        (LocalPlaces.localRuntimePlace frames.size frame localId ActualReferenceMetadata.reference).stackView)
      (Storage.withCurrent frames frame before)=.ok () (Storage.withCurrent frames doneFrame post) ∧
    stage.output.global=(CurrentCallLazyTypedSource.nextTracker tracker room).global ∧
    (∃ qData qOwner,∃ Q : UniformWindow post (CurrentCallLazyTypedSource.nextTracker tracker room) qData qOwner id offset.toNat len.toNat .mut,
      Q.pointer=⟨id,Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset)),stage.child⟩ ∧
      Q.allocation=converted.mapExtra (fun _=>stage.output.child.tree) ∧
      Q.precise.completion=S05ConcreteProtectedChildCompletion.extend stage.initialCompletion stage.child allocationRoot) ∧
    (∃ current : UniformWindow post (CurrentCallLazyTypedSource.nextTracker tracker room) data boolOwner boolId boolOffset 1 .ret,
      current.pointer=B.pointer ∧current.allocation=B.allocation ∧current.precise=B.precise) := by
  obtain ⟨converted,stage,attributes,copy,scopedEq,globalEq,qCurrent,bCurrent,_⟩:=invoke_with_binding options limits remaining span before tracker frames frame borrowFrame frameBorrow id root source base offset len pointer
      ready noFunction noVaList room preciseOff implicitOff nullComparator dynamicFuel validationFuel fuelEq validationEq metadata origins debugOff ghostOff shallowMode
      localId valid old live cached noClocks license B boolRuntime
  exact ⟨converted,stage,attributes,copy,scopedEq,globalEq,qCurrent,bCurrent⟩

end
end DuplicatePrefix.CurrentCallLazySourceResources
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallLazySourceResources" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual lazy source resource dependency {dependency}"
