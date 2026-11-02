import duplicate_prefix.CurrentCallCopiedBoolData
import duplicate_prefix.CurrentCallCountBranches
import duplicate_prefix.PositiveRootAddToCopy
import duplicate_prefix.S05CompletedWriteAuthorityConcrete
import duplicate_prefix.CurrentCallCopyGuard
import duplicate_prefix.CurrentCallEntrySourceStorage
import duplicate_prefix.CurrentCallCopyHelperExecution
import duplicate_prefix.CurrentCallCopyGuardReturn
import duplicate_prefix.InitMaskInitializedSubrange

/-! Actual accepted-call execution through pointer arithmetic, copy guards,
physical nonoverlapping copy, and helper return. The internal Read/Write
certificates come from the one current completed raw grant. -/
namespace DuplicatePrefix.CurrentCallAcceptedCopyPrefix
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext CurrentCallLen
open CandidateStableCallOwnership GeneralRangeMapOrigins GeneralRangeMapState GeneralBorrowWildcardParentTagOrder
open GeneralBorrowProjection GeneralBorrowForest GeneralBorrowExposureCardinality GeneralBorrowExposedNonleafPrimaryPath OrdinaryBorrowAuthority
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- Derived facts consumed by the actual root cleanup. -/
structure ReturnFacts {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    {count : UInt64} (s : SharedStage input count) (root : CompilerFrameContext.ActualFrame)
    (post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (held : MachineHooks.BorrowState) (completion : Completion) : Prop where
  boolData : Nonempty (CurrentCallLenRootData.Data s post entry held completion)
  sourceSize : entry.allocation.byteSize = s.entry.allocation.byteSize
  sourceLen : entry.allocation.len = s.entry.allocation.len
  sourceKind : entry.kind = s.entry.kind
  model : DuplicatePrefixCallModel.Model options remaining span post
  origins : DuplicatePrefixTypeCacheOrigins.Origins post.user.payload.payload.user.types
  ready : CurrentCallBoolProtection.ProfileMemoryReadiness post call
  active : ∃ thread, post.threads.activeThread? = some thread
  physical : S02SameDestinationAcceptedCopyPhysical.Physical entry.allocation
  storage : entry.allocation.len = entry.allocation.byteSize.bytes.toNat
  memory : post.memory.live = ((s.out.machine count).memory.live.filter (fun row => row.1 != call.sourceId)).push (call.sourceId,entry)
  addresses : post.user.addresses = (s.out.machine count).user.addresses
  body : root.body = RootBody.reflected.body.body
  identity : root.bodyIdentity = RootBody.reflected.body.identity
  callee : root.functionInstance = RootBody.reflected.functionInstance
  size : root.locals.size = 25
  extra : root.extra = (s.out.frame count).extra
  clocks : root.extra.dataRace = none
  continuation : root.returnContinuation = (s.out.frame count).returnContinuation
  varargs : root.vaList = (s.out.frame count).vaList
  immediate : CopyHelperCleanup.AllImmediate root
  zero : root.locals[0]? = some ⟨.live (.immediate .uninit),none⟩
  seventeen : root.locals[17]? = some ⟨.live (.immediate .uninit),none⟩
  temporaries : ∃ temp15 temp18 temp19 temp21 temp24,
    root.locals[15]?.map (·.value) = some (.live (.immediate temp15)) ∧
    root.locals[18]?.map (·.value) = some (.live (.immediate temp18)) ∧
    root.locals[19]?.map (·.value) = some (.live (.immediate temp19)) ∧
    root.locals[21]?.map (·.value) = some (.live (.immediate temp21)) ∧
    root.locals[24]?.map (·.value) = some (.live (.immediate temp24))

private theorem clock_fields (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) :
    (CopyHelperClock.advance options remaining span machine).user.payload.ghost = machine.user.payload.ghost ∧
    (CopyHelperClock.advance options remaining span machine).user.payload.validation = machine.user.payload.validation ∧
    (CopyHelperClock.advance options remaining span machine).user.payload.payload.user.types = machine.user.payload.payload.user.types := by
  unfold CopyHelperClock.advance PtrMetadataReturn.accountedMachine SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  exact ⟨rfl,rfl,rfl⟩

private theorem maximum (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) :
    (config options remaining span).projection.maxSizeOfVal = Size.ofBytes 9223372036854775807 := by
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  obtain ⟨_,_,_,_,projectionEq,_⟩ := fields.placeConstruction
  have same : (config options remaining span).projection.maxSizeOfVal = (config options remaining span).projection.dynamic.maxSizeOfVal := by
    rw [projectionEq];rfl
  obtain ⟨_,bound,boundEq,dynamicEq⟩ := fields.projectionDynamic
  rw [same,dynamicEq]
  change bound = Size.ofBytes 9223372036854775807
  exact Except.ok.inj (boundEq.symm.trans (show CompilerExecutionBounds.maximum PreparedReflection.actual.compiler.runtime.target =
    .ok (Size.ofBytes 9223372036854775807) from rfl))

private theorem replace_runtime (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (locations : Miri.DataStructures.DedupRangeMap LocationTree)
    (well : locations.WellFormed)
    (rows : Every (fun location => LocationCoherent tree location global.protectedTags ∧
      GeneralBorrowLocationSifaConsistency.Profile tree location global.protectedTags ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location) locations) :
    DuplicatePrefixBorrowContract.RuntimeFacts {tree with locations := locations} global := by
  refine ⟨⟨⟨GeneralBorrowStructuralHistoryState.graph_locations tree locations runtime.formed.toGraphState,well⟩,?_⟩,
    ?_,?_,⟨runtime.below.mapping,runtime.below.protectors⟩⟩
  · intro index valid;exact ⟨(rows index valid).2.1.present,(rows index valid).2.1.vacant⟩
  · intro index valid;exact (rows index valid).1
  · intro index valid;exact (rows index valid).2.2

/-- Literal sequential source-Read/destination-Write certificates come from the
ONE completed current raw grant. These are consumed internally by the actual copy. -/
private theorem copy_access (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (complete : Completes tree completion)
    (order : ParentTagOrder tree) (source : UniIndex) (node : TreeNode) (present : tree.nodes.get source = some node)
    (offset len count : UInt64) (within : count≤len/2)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (short : tree.nodes.size<65536)
    (owned : OwnedOn (S05CompletedAncestryReadMutable.Authority tree completion global.protectedTags source)
      offset (offset+len) tree.locations) :
    let read := tree.performBorrowAccessRange (.concrete node.tag) (Size.ofBytes offset) (Size.ofBytes count) .Read global.protectedTags .VisitChildrenOfAccessed
    let write := read.tree.performBorrowAccessRange (.concrete node.tag) (Size.ofBytes (offset+count)) (Size.ofBytes count) .Write global.protectedTags .VisitChildrenOfAccessed
    read.status = .Completed ∧ write.status = .Completed ∧
      DuplicatePrefixBorrowContract.RuntimeFacts write.tree global ∧ Completes write.tree completion ∧
      ParentTagOrder write.tree ∧ write.tree.nodes = tree.nodes ∧ write.tree.locations.size = tree.locations.size ∧
      OwnedOn (S05CompletedAncestryReadMutable.Authority write.tree completion global.protectedTags source)
        offset (offset+len) write.tree.locations ∧
      (∀ target, GeneralBorrowFreshActiveWithin.ActiveWithin tree target .Write offset (offset+len) →
        GeneralBorrowFreshActiveWithin.ActiveWithin write.tree target .Write offset (offset+len)) := by
  have numeric := PositiveRootCopyBounds.guarded len count offset tree.locations.size.bytes within bounds
  have nowrap : offset.toNat+len.toNat<2^64 := Nat.lt_of_le_of_lt bounds tree.locations.size.bytes.toNat_lt
  have sumEq : (offset+len).toNat = offset.toNat+len.toNat := by simp only [UInt64.toNat_add,Nat.mod_eq_of_lt nowrap]
  have firstNowrap : offset.toNat+count.toNat<2^64 := by omega
  have firstEq : (offset+count).toNat = offset.toNat+count.toNat := by simp only [UInt64.toNat_add,Nat.mod_eq_of_lt firstNowrap]
  have secondNowrap : (offset+count).toNat+count.toNat<2^64 := by omega
  have secondEq : (offset+count+count).toNat = offset.toNat+count.toNat+count.toNat := by
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt secondNowrap,firstEq]
  obtain ⟨position,root,rootNode,slot,rootAt,path⟩ := CandidateCurrentWindowAuthority.root_path tree runtime.formed.toGraphState source node present
  obtain ⟨depth⟩ := runtime.formed.depth
  have rows : OwnedOn (fun location => GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location ∧
      S05CompletedAncestryReadMutable.Authority tree completion global.protectedTags source location) offset (offset+len) tree.locations := by
    intro index valid positive start stop
    exact ⟨runtime.possible index valid,owned index valid positive start stop⟩
  have read := S05CompletedAncestryReadMutable.range tree completion global.protectedTags complete runtime.formed.toGraphState depth order
    position root source rootNode node slot rootAt present path (Size.ofBytes offset) (Size.ofBytes count) offset (offset+len) rows runtime.formed.well
    (fun index valid => ⟨runtime.coherent index valid,runtime.formed.profile index valid,runtime.possible index valid⟩)
    numeric.2.2.1 (Nat.le_refl _) (by change (offset+count).toNat≤(offset+len).toNat;omega) short .VisitChildrenOfAccessed
  let accessed := tree.performBorrowAccessRange (.concrete node.tag) (Size.ofBytes offset) (Size.ofBytes count) .Read global.protectedTags .VisitChildrenOfAccessed
  have afterRuntime : DuplicatePrefixBorrowContract.RuntimeFacts accessed.tree global := by
    rw [read.tree_eq]
    exact replace_runtime tree global runtime accessed.tree.locations read.well read.runtime
  have afterComplete : Completes accessed.tree completion := by
    rw [read.tree_eq]
    exact CandidateCurrentJointRawReplacement.completes tree completion _ complete
  have afterOrder := GeneralBorrowParentTagInvariant.nodes_frame tree accessed.tree read.nodes order
  have afterRows : OwnedOn (fun location => GeneralBorrowSnapshotReadRuntime.GlobalPossible accessed.tree location ∧
      S05CompletedAncestryReadMutable.Authority accessed.tree completion global.protectedTags source location) offset (offset+len) accessed.tree.locations := by
    intro index valid positive start stop
    refine ⟨afterRuntime.possible index valid,?_⟩
    intro query current currentAt
    have prior := (read.rows index valid positive start stop).2
    exact prior query current (by rw [read.nodes] at currentAt;exact currentAt)
  have afterPresent : accessed.tree.nodes.get source = some node := by rw [read.nodes];exact present
  have afterRoot : accessed.tree.nodes.get root = some rootNode := by rw [read.nodes];exact rootAt
  have afterSlot : accessed.tree.roots[position]? = some root := by rw [read.roots];exact slot
  have afterPath : Path accessed.tree root source :=
    GeneralBorrowPrimaryWitnessVisibility.path_nodes (before := accessed.tree) (after := tree) read.nodes.symm path
  obtain ⟨afterDepth⟩ := afterRuntime.formed.depth
  have writeBounds : (offset+count).toNat+count.toNat ≤ accessed.tree.locations.size.bytes.toNat := by rw [read.capacity];omega
  have write := S05CompletedWriteAuthorityConcrete.range accessed.tree completion global.protectedTags afterComplete afterRuntime.formed.toGraphState afterDepth afterOrder
    position root source rootNode node afterSlot afterRoot afterPresent afterPath (Size.ofBytes (offset+count)) (Size.ofBytes count) offset (offset+len)
    afterRows afterRuntime.formed.well (fun index valid => ⟨afterRuntime.coherent index valid,afterRuntime.formed.profile index valid,afterRuntime.possible index valid⟩)
    writeBounds (by change offset.toNat≤(offset+count).toNat;omega) (by change (offset+count+count).toNat≤(offset+len).toNat;omega)
    (by rw [read.nodes];exact short) .VisitChildrenOfAccessed
  let written := accessed.tree.performBorrowAccessRange (.concrete node.tag) (Size.ofBytes (offset+count)) (Size.ofBytes count) .Write global.protectedTags .VisitChildrenOfAccessed
  have finalRuntime : DuplicatePrefixBorrowContract.RuntimeFacts written.tree global := by
    rw [write.tree_eq]
    exact replace_runtime accessed.tree global afterRuntime written.tree.locations write.well write.runtime
  have finalComplete : Completes written.tree completion := by
    rw [write.tree_eq]
    exact CandidateCurrentJointRawReplacement.completes accessed.tree completion _ afterComplete
  refine ⟨read.completed,write.completed,finalRuntime,finalComplete,
    GeneralBorrowParentTagInvariant.nodes_frame accessed.tree written.tree write.nodes afterOrder,write.nodes.trans read.nodes,write.capacity.trans read.capacity,?_,?_⟩
  · intro index valid positive start stop query current currentAt
    have prior := (write.rows index valid positive start stop).2
    exact prior query current (by rw [write.nodes] at currentAt;exact currentAt)
  · intro target active
    have afterRead := GeneralBorrowFreshActiveWithinAccess.normal tree node.tag (Size.ofBytes offset) (Size.ofBytes count)
      .Read global.protectedTags .VisitChildrenOfAccessed target offset (offset+len) runtime.formed.well numeric.2.2.1
      (Nat.le_refl _) (by change (offset+count).toNat≤(offset+len).toNat;omega) active
    exact GeneralBorrowFreshActiveWithinAccess.normal accessed.tree node.tag (Size.ofBytes (offset+count)) (Size.ofBytes count)
      .Write global.protectedTags .VisitChildrenOfAccessed target offset (offset+len) afterRuntime.formed.well writeBounds
      (by change offset.toNat≤(offset+count).toNat;omega) (by change (offset+count+count).toNat≤(offset+len).toNat;omega) afterRead

theorem copied_and_returned {options limits remaining span before tracker argument len place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (stackReady : CurrentCallPush.StackReadiness before #[])
    (memoryReady : CurrentCallBoolProtection.ProfileMemoryReadiness before call)
    (positive : 0 < len.toNat) (count : UInt64) (nonzero : count ≠ 0) (within : count ≤ len/2) :
    ∃ (s : SharedStage input count) (result : CompilerFrameContext.ActualFrame)
      (post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
      (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
      (held : MachineHooks.BorrowState) (completion : Completion),
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] (s.out.frame count) (s.out.machine count)) (Storage.withCurrent #[] result post) ∧
      result.location = .mir ⟨9,0⟩ ∧ result.returnPlace = (s.out.frame count).returnPlace ∧
      post.memory.live.find? (fun row => row.1 == call.sourceId) = some (call.sourceId,entry) ∧
      post.borrowTracker = some held ∧
      DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra held.global ∧
      Completes entry.allocation.extra completion ∧ ParentTagOrder entry.allocation.extra ∧
      entry.allocation.extra.locations.size = entry.allocation.byteSize ∧ entry.allocation.extra.nodes.size < 65536 ∧
      OwnedOn (S05CompletedAncestryReadMutable.Authority entry.allocation.extra completion held.global.protectedTags s.out.source.base.raw.child)
        (UInt64.ofNat call.sourceOffset) (UInt64.ofNat call.sourceOffset+len) entry.allocation.extra.locations ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin entry.allocation.extra s.out.source.base.raw.child .Write
        (UInt64.ofNat call.sourceOffset) (UInt64.ofNat call.sourceOffset+len) ∧
      (∃ node, entry.allocation.extra.nodes.get s.out.source.base.raw.child = some node ∧
        node.tag = tracker.global.nextPointerTag ∧ node.isExposed = false) ∧ ReturnFacts s result post entry held completion := by
  obtain ⟨s,frame,machine,entry,held,completion,child,pointer,trace,located,destination,live,tracked,runtime,complete,sourceOwned,owned,
    window,slot15,⟨node,nodeAt,provenance⟩,model,origins,profile,order,capacity,short,allocation,
    body,identity,callee,size,extra,clocks,trackNone,relevance,all,unused,slot2,⟨temp16,slot16⟩,⟨thread,active,top⟩,sourceNode,sourceActivity,sourceChain,⟨beforeCopyBoolData⟩,rootZero,rootContinuation,rootVarargs,sourceMemory,sourceAddresses,sourceTagFresh⟩ :=
    CurrentCallCountBranches.accepted_as_mut_returned input stackReady memoryReady positive count nonzero within
  obtain ⟨windowEntry,base,windowLive,cached,bytes,room,bounds,address,nonnull,_⟩ := window
  have same : windowEntry = entry := (Prod.mk.inj (Option.some.inj (windowLive.symm.trans live))).2
  subst windowEntry
  let offset := UInt64.ofNat call.sourceOffset
  have offsetEq : offset.toNat = call.sourceOffset := by
    dsimp only [offset]
    simp only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt (by omega : call.sourceOffset<2^64)]
  have sumEq : (base+offset).toNat = base.toNat+call.sourceOffset := by
    simp only [UInt64.toNat_add,offsetEq,Nat.mod_eq_of_lt (by omega : base.toNat+call.sourceOffset<2^64)]
  have bits : pointer.offset.bytes = base+offset := UInt64.toNat_inj.mp (address.trans sumEq.symm)
  have pointerEq : pointer = Pointer.new (.concrete call.sourceId node.tag) (Size.ofBytes (base+offset)) := by
    calc pointer = Pointer.new pointer.provenance pointer.offset := rfl
         _ = Pointer.new (.concrete call.sourceId node.tag) pointer.offset := congrArg (fun prov => Pointer.new prov pointer.offset) provenance
         _ = Pointer.new (.concrete call.sourceId node.tag) (Size.ofBytes (base+offset)) :=
           congrArg (Pointer.new (Provenance.concrete call.sourceId node.tag)) (congrArg Size.ofBytes bits)
  let value : Scalar Provenance := Scalar.fromPointer (config options (remaining+1) span).access.runtime.base pointer
  have valid (index : Fin 25) : index.val < frame.locals.size := by rw [size];exact index.isLt
  have stored (index : Fin 25) (row : LocalState Provenance LocalLayout)
      (found : frame.locals[index.val]? = some row) : frame.locals[index.val]'(valid index) = row :=
    Option.some.inj ((Array.getElem?_eq_getElem (valid index)).symm.trans found)
  have default : held.retagMode = .Default := by
    obtain ⟨other,otherTracked,mode⟩ := model.defaultTracker
    have same : other = held := Option.some.inj (otherTracked.symm.trans tracked)
    simpa only [same] using mode
  let fuel := options.limits.validation-1
  let dispatchFuel := limits.callDispatch-1
  have work : 64 ≤ DuplicatePrefixCallSpecification.work before len := by unfold DuplicatePrefixCallSpecification.work;omega
  have fuelEq : options.limits.validation = fuel+1 := by
    have reserve := input.machine.resources.configuredFuel.2.2.2
    dsimp only [fuel];omega
  have dispatchEq : limits.callDispatch = dispatchFuel+1 := by
    have reserve := input.machine.resources.executionFuel.1
    dsimp only [dispatchFuel];omega
  have countPositive : (0 : UInt64) < count := UInt64.lt_iff_toNat_lt.mpr (by
    have notzero : count.toNat ≠ 0 := by intro zero;exact nonzero (UInt64.toNat_inj.mp zero)
    simp only [UInt64.toNat_zero]
    omega)
  have sliceBounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat := by
    rw [offsetEq,←bytes];exact bounds
  obtain ⟨result,tail,resultBody,resultIdentity,resultCallee,resultExtra,returnPlace,resultContinuation,resultVarargs,resultLocalsIdentity,
    resultTrack,resultSize,resultLocation,live17,live18,live19,live21,live24,keep,resultAll⟩ :=
    PositiveRootAddToCopy.executes options limits remaining span model.debugOff fuel fuelEq #[] frame machine value count temp16 size
      (congrArg LocalState.value (stored ⟨15,by decide⟩ _ slot15)) (congrArg LocalState.layout (stored ⟨15,by decide⟩ _ slot15))
      (congrArg LocalState.value (stored ⟨16,by decide⟩ _ slot16))
      (congrArg LocalState.value (stored ⟨2,by decide⟩ _ slot2)) (congrArg LocalState.layout (stored ⟨2,by decide⟩ _ slot2))
      (by intro index bounded lower upper;exact Option.some.inj ((Array.getElem?_eq_getElem bounded).symm.trans (unused index lower (by omega))))
      body identity callee located clocks held tracked default model.ghostOff model.shallow all trackNone
      (by rw [relevance];decide) thread active top dispatchFuel dispatchEq model.noBackend model.noDataRace model.unchecked model.noGc model.fixedScheduler
      call.sourceId node.tag base offset len entry (congrArg (Scalar.fromPointer (config options (remaining+1) span).access.runtime.base) pointerEq)
      cached live countPositive within sliceBounds (DuplicatePrefixCallModel.sourceComparator options remaining span machine model) model.nullComparator
  have logicalBounds : offset.toNat+len.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat := by rw [capacity];exact sliceBounds
  have certificates := copy_access entry.allocation.extra held.global completion runtime complete order child node nodeAt offset len count within logicalBounds short owned
  obtain ⟨original,originalLive,originalBytes,originalMutable,originalMask,originalMaskLen,originalInit,originalProvenance,originalRoom⟩ :=
    CurrentCallEntrySourceStorage.of_entry s.out count s.facts positive
  have originalEq : original = s.entry := (Prod.mk.inj (Option.some.inj (originalLive.symm.trans s.live))).2
  subst original
  have initialized : InitMaskCopy.InitializedOn entry.allocation.initializationMask (Size.ofBytes offset) (Size.ofBytes (offset+len)) := by
    rw [allocation];exact originalInit
  have provenanceInput : S02SameDestinationUninitProvenanceInput.DirectInput entry.allocation.provenanceMap entry.allocation.len := by
    rw [allocation];exact originalProvenance
  let post := AddOutput.machine options remaining span machine
  obtain ⟨sameMemory,sameTracker,sameThreads,sameRace,sameAddresses,sameGhost,sameShallow,sameBackend,sameExtras,sameTypes⟩ := AddOutput.preserved options remaining span machine
  have postActive : post.threads.activeThread? = some thread := by rw [sameThreads];exact active
  have postTracked : post.borrowTracker = some held := by rw [sameTracker];exact tracked
  have postGhost : post.user.payload.ghost = false := sameGhost.trans model.ghostOff
  have postShallow : post.user.payload.validation = .Shallow := sameShallow.trans model.shallow
  have postRace : post.dataRace = none := sameRace.trans model.noDataRace
  have postBackend : post.user.payload.payload.user.backend = .none := sameBackend.trans model.noBackend
  have postUnchecked : ((config options (remaining+1) span).terminators.getControl post.user).checkedArithmetic = false := by
    rw [AddOutput.control];exact model.unchecked
  have postNoGc : ((config options (remaining+1) span).terminators.getControl post.user).gcInterval = 0 := by
    rw [AddOutput.control];exact model.noGc
  have postFixed : post.threads.fixedScheduling = true := by rw [sameThreads];exact model.fixedScheduler
  let destinationPointer : Scalar Provenance := Scalar.fromPointer (config options (remaining+1) span).access.runtime.base
    (Pointer.new (.concrete call.sourceId node.tag) (Size.ofBytes (base+offset+count)))
  have resultValid (index : Fin 25) : index.val < result.locals.size := by rw [resultSize];exact index.isLt
  have resultStored (index : Fin 25) (row : LocalState Provenance LocalLayout)
      (found : result.locals[index.val]? = some row) : result.locals[index.val]'(resultValid index) = row :=
    Option.some.inj ((Array.getElem?_eq_getElem (resultValid index)).symm.trans found)
  let ready : CopyRootEntry.Input options limits remaining span #[] result post value destinationPointer count := {
    debug := model.debugOff,tracker := held,tracked := postTracked,valid := resultValid ⟨18,by decide⟩,old := .uninit
    live := congrArg LocalState.value (resultStored ⟨18,by decide⟩ _ live18)
    uncached := congrArg LocalState.layout (resultStored ⟨18,by decide⟩ _ live18)
    noClocks := (congrArg (fun extra => extra.dataRace) resultExtra).trans clocks,noRace := postRace
    body := resultBody.trans body,identity := resultIdentity.trans identity,callee := resultCallee.trans callee
    trackNone := resultTrack.trans trackNone,location := resultLocation,fuel := fuel,validationFuel := fuelEq
    ghost := postGhost,shallow := postShallow,thread := thread,active := postActive,top := top
    relevant := by rw [resultExtra,relevance];decide
    budget := dispatchFuel,budgetEq := dispatchEq,backend := postBackend,unchecked := postUnchecked,noGc := postNoGc,fixed := postFixed
    source := DuplicatePrefixCallModel.sourceComparator options remaining span machine model,cmp := model.nullComparator
    valid19 := resultValid ⟨19,by decide⟩,valid21 := resultValid ⟨21,by decide⟩,valid24 := resultValid ⟨24,by decide⟩
    live19 := congrArg LocalState.value (resultStored ⟨19,by decide⟩ _ live19)
    cache19 := congrArg LocalState.layout (resultStored ⟨19,by decide⟩ _ live19)
    live21 := congrArg LocalState.value (resultStored ⟨21,by decide⟩ _ live21)
    cache21 := congrArg LocalState.layout (resultStored ⟨21,by decide⟩ _ live21)
    live24 := congrArg LocalState.value (resultStored ⟨24,by decide⟩ _ live24)
    cache24 := congrArg LocalState.layout (resultStored ⟨24,by decide⟩ _ live24)}
  let statementFuel := limits.validation-1
  have statementEq : limits.validation = statementFuel+1 := by
    have reserve := input.machine.resources.executionFuel.2.2.2
    dsimp only [statementFuel];omega
  have postProfile := profile.transport sameExtras
  have numeric := PositiveRootCopyBounds.guarded len count offset entry.allocation.byteSize.bytes within sliceBounds
  have fullNowrap : offset.toNat+len.toNat<2^64 := Nat.lt_of_le_of_lt sliceBounds entry.allocation.byteSize.bytes.toNat_lt
  have fullEq : (offset+len).toNat = offset.toNat+len.toNat := by simp only [UInt64.toNat_add,Nat.mod_eq_of_lt fullNowrap]
  have firstNowrap : offset.toNat+count.toNat<2^64 := by omega
  have firstEq : (offset+count).toNat = offset.toNat+count.toNat := by simp only [UInt64.toNat_add,Nat.mod_eq_of_lt firstNowrap]
  have sourceReady : CurrentCallBoolProtection.WindowReady post call.sourceId offset.toNat len.toNat := by
    have ready := postProfile.source (by rw [input.actual.length];exact positive)
    simpa only [input.actual.length,offsetEq] using ready
  have readReady := sourceReady.subrange offset.toNat count.toNat (Nat.le_refl _) (by omega)
  have writeReady := sourceReady.subrange (offset+count).toNat count.toNat (by omega) (by omega)
  have currentMask : InitMaskCopy.WellFormed entry.allocation.initializationMask := by rw [allocation];exact originalMask
  have currentMaskLen : entry.allocation.initializationMask.len = entry.allocation.byteSize := by rw [allocation];exact originalMaskLen
  have currentMutable : entry.allocation.mutability = .Mut := by rw [allocation];exact originalMutable
  have currentRoom : entry.allocation.len+64<2^64 := by rw [allocation];exact originalRoom
  have prefixInitialized : InitMaskCopy.InitializedOn entry.allocation.initializationMask (Size.ofBytes offset) (Size.ofBytes (offset+count)) :=
    InitMaskInitializedSubrange.subrange _ _ _ _ _ (Nat.le_refl _) (by change (offset+count).toNat≤(offset+len).toNat;omega) initialized
  have bounded : count ≤ (config options (remaining+1) span).projection.maxSizeOfVal.bytes := by
    rw [maximum]
    apply UInt64.le_iff_toNat_le.mpr
    change count.toNat≤9223372036854775807
    omega
  have rawValue : value = Scalar.fromPointer (config options (remaining+1) span).access.runtime.base
      (Pointer.new (Provenance.concrete call.sourceId node.tag) (Size.ofBytes (base+offset))) :=
    congrArg (Scalar.fromPointer (config options (remaining+1) span).access.runtime.base) pointerEq
  have destValue : destinationPointer = Scalar.fromPointer (config options (remaining+1) span).access.runtime.base
      (Pointer.new (Provenance.concrete call.sourceId node.tag) (Size.ofBytes (base+(offset+count)))) :=
    congrArg (Scalar.fromPointer (config options (remaining+1) span).access.runtime.base)
      (congrArg (Pointer.new (Provenance.concrete call.sourceId node.tag)) (congrArg Size.ofBytes (UInt64.add_assoc base offset count)))
  have postLive : post.memory.live.find? (fun row => row.1 == call.sourceId) = some (call.sourceId,entry) := by rw [sameMemory];exact live
  have postCached : post.user.addresses.baseAddr.find? (fun row => row.allocId == call.sourceId) = some ⟨call.sourceId,base⟩ := by rw [sameAddresses];exact cached
  obtain ⟨guardMachine,copied,finalMachine,copyTrace,guardPreserved,copiedLive,copiedSize,copiedLen,copiedTree,copiedBytes,copiedPhysical,finalMemory,finalTracker,finalUser,finalRace,finalFixed,finalActor⟩ :=
    CurrentCallCopyGuardReturn.run options limits remaining span #[] result post value destinationPointer count ready
      statementFuel statementEq default call.sourceId node.tag base offset len entry.kind entry.allocation
      countPositive sliceBounds numeric.2.1 bytes currentMask currentMaskLen prefixInitialized provenanceInput currentRoom currentMutable
      readReady writeReady postLive postCached certificates.1 certificates.2.1 bounded rawValue destValue
  let finalFrame := CurrentCallCopyGuardReturn.returnedFrame options limits remaining span #[] result post value destinationPointer count ready
  have projections := CurrentCallCopyGuardReturn.frame_projections options limits remaining span #[] result post value destinationPointer count ready
  obtain ⟨copyBody,copyIdentity,copyCallee,copyExtra,copyDestination,copyContinuation,copyVarargs,copyLocalsIdentity,copyTrack,copySize,copyLocation,copySlot18,copyKeep⟩ := projections
  let finalEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind := ⟨entry.kind,copied⟩
  obtain ⟨_,_,writeRuntime,writeComplete,writeOrder,writeNodes,writeCapacity,writeOwned,preserveActivity⟩ := certificates
  let readAccess := entry.allocation.extra.performBorrowAccessRange (.concrete node.tag) (Size.ofBytes offset) (Size.ofBytes count)
    .Read held.global.protectedTags .VisitChildrenOfAccessed
  let writeAccess := readAccess.tree.performBorrowAccessRange (.concrete node.tag) (Size.ofBytes (offset+count)) (Size.ofBytes count)
    .Write held.global.protectedTags .VisitChildrenOfAccessed
  obtain ⟨middle,middleNode,returnedNode,returnedEdge,middleEdge,middleAt,returnedAt,middleUnheld,returnedUnheld⟩ := sourceChain
  have qOwned : OwnedOn (S05CompletedAncestryReadMutable.Authority writeAccess.tree completion held.global.protectedTags s.out.source.base.raw.child)
      offset (offset+len) writeAccess.tree.locations := by
    intro position valid positive start stop
    have first := S05CompletedChildReanchor.authority writeAccess.tree completion _ held.global.protectedTags held.global.protectedTags
      child middle returnedNode returnedEdge (by rw [writeNodes];exact returnedAt) (fun _ found => found) returnedUnheld
      (writeOwned position valid positive start stop)
    exact S05CompletedChildReanchor.authority writeAccess.tree completion _ held.global.protectedTags held.global.protectedTags
      middle s.out.source.base.raw.child middleNode middleEdge (by rw [writeNodes];exact middleAt)
      (fun _ found => found) middleUnheld first
  refine ⟨s,finalFrame,finalMachine,finalEntry,held,completion,SuccessfulTrace.append trace (SuccessfulTrace.append tail copyTrace),rfl,
    copyDestination.trans (returnPlace.trans destination),copiedLive,finalTracker,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change DuplicatePrefixBorrowContract.RuntimeFacts copied.extra held.global
    rw [copiedTree];exact writeRuntime
  · change Completes copied.extra completion
    rw [copiedTree];exact writeComplete
  · change ParentTagOrder copied.extra
    rw [copiedTree];exact writeOrder
  · change copied.extra.locations.size = copied.byteSize
    rw [copiedTree,writeCapacity,copiedSize];exact capacity
  · change copied.extra.nodes.size < 65536
    rw [copiedTree,writeNodes];exact short
  · change OwnedOn (S05CompletedAncestryReadMutable.Authority copied.extra completion held.global.protectedTags s.out.source.base.raw.child)
      offset (offset+len) copied.extra.locations
    rw [copiedTree];exact qOwned
  · change GeneralBorrowFreshActiveWithin.ActiveWithin copied.extra s.out.source.base.raw.child .Write offset (offset+len)
    rw [copiedTree];exact preserveActivity _ sourceActivity
  · obtain ⟨qNode,qAt,qTag,qHidden⟩ := sourceNode
    refine ⟨qNode,?_,qTag,qHidden⟩
    change copied.extra.nodes.get s.out.source.base.raw.child = some qNode
    rw [copiedTree,writeNodes];exact qAt

  · let first := CopyHelperClock.advance options remaining span guardMachine
    let second := CopyHelperClock.advance options remaining span first
    have ghostEq := (clock_fields options remaining span second).1.trans
      ((clock_fields options remaining span first).1.trans (clock_fields options remaining span guardMachine).1)
    have shallowEq := (clock_fields options remaining span second).2.1.trans
      ((clock_fields options remaining span first).2.1.trans (clock_fields options remaining span guardMachine).2.1)
    have typesEq := (clock_fields options remaining span second).2.2.trans
      ((clock_fields options remaining span first).2.2.trans (clock_fields options remaining span guardMachine).2.2)
    have finalTypes : finalMachine.user.payload.payload.user.types = machine.user.payload.payload.user.types :=
      (congrArg (fun user => user.payload.payload.user.types) finalUser).trans
        (typesEq.trans (guardPreserved.types.trans sameTypes))
    have finalExtras : finalMachine.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras := by
      rw [finalUser]
      simp only [CopyHelperClock.runtime]
      exact guardPreserved.extras.trans sameExtras
    have finalAddresses : finalMachine.user.addresses = (s.out.machine count).user.addresses := by
      rw [finalUser]
      simp only [CopyHelperClock.addresses]
      exact guardPreserved.addresses.trans (sameAddresses.trans sourceAddresses)
    have finalModel : DuplicatePrefixCallModel.Model options remaining span finalMachine := {model with
      ghostOff := (congrArg (fun user => user.payload.ghost) finalUser).trans (ghostEq.trans (guardPreserved.ghost.trans postGhost))
      shallow := (congrArg (fun user => user.payload.validation) finalUser).trans (shallowEq.trans (guardPreserved.validation.trans postShallow))
      defaultTracker := ⟨held,finalTracker,default⟩
      noDataRace := finalRace.trans postRace
      noBackend := by rw [finalUser];simp only [CopyHelperClock.backend];exact guardPreserved.backend.trans postBackend
      metadata := by rw [finalTypes];exact model.metadata
      fixedScheduler := finalFixed.trans postFixed
      unchecked := by rw [finalUser];simp only [CopyHelperClock.control,TerminatorClock.advance];exact guardPreserved.unchecked.trans postUnchecked
      noGc := by rw [finalUser];simp only [CopyHelperClock.control,TerminatorClock.advance];exact guardPreserved.noGc.trans postNoGc}
    have finalHeap : finalMachine.memory.live = ((s.out.machine count).memory.live.filter (fun row => row.1 != call.sourceId)).push (call.sourceId,finalEntry) := by
      rw [finalMemory]
      change (post.memory.live.filter (fun row => row.1 != call.sourceId)).push (call.sourceId,finalEntry) = _
      rw [sameMemory,sourceMemory]
      exact congrArg (fun memory => memory.live) (MemoryCopyBridge.live_update_twice (s.out.machine count).memory call.sourceId
        {s.entry with allocation := s.entry.allocation.setExtra entry.allocation.extra} finalEntry)
    have different : call.sourceId = call.returnId → s.out.borrowed.child ≠ child := by
      intro same equal
      have bAt := beforeCopyBoolData.present
      rw [beforeCopyBoolData.sameEntry same] at bAt
      have atChild : entry.allocation.extra.nodes.get child = some beforeCopyBoolData.node := by
        simpa only [equal,BorrowTree.nodeAt] using bAt
      have nodeEq : beforeCopyBoolData.node = node := Option.some.inj (atChild.symm.trans nodeAt)
      apply sourceTagFresh node nodeAt
      rw [←nodeEq];exact beforeCopyBoolData.tag
    have endpoints := CurrentCallBoolProtection.endpoints (CurrentCallPush.prepared_input input #[]) {} s.out.source.base.raw positive
    have windowPositive : (UInt64.ofNat call.sourceOffset).toNat < (UInt64.ofNat call.sourceOffset+len).toNat := by
      change offset.toNat < (offset+len).toNat
      omega
    have disjoint : call.sourceId = call.returnId →
        (UInt64.ofNat call.sourceOffset+len).toNat ≤ (UInt64.ofNat call.returnOffset).toNat ∨
        (UInt64.ofNat call.returnOffset+1).toNat ≤ (UInt64.ofNat call.sourceOffset).toNat := by
      intro same
      by_cases left : (UInt64.ofNat call.sourceOffset+len).toNat ≤ (UInt64.ofNat call.returnOffset).toNat
      · exact .inl left
      by_cases after : (UInt64.ofNat call.sourceOffset).toNat ≤ (UInt64.ofNat call.returnOffset).toNat
      · have impossible := endpoints.2.2.2.2.2 same (UInt64.ofNat call.returnOffset) after (by omega)
        have low := endpoints.2.1
        have high := endpoints.2.2.2.1
        omega
      · have earlier := endpoints.2.2.2.2.2 same (UInt64.ofNat call.sourceOffset) (Nat.le_refl _) windowPositive
        exact .inr (by omega)
    have finalBoolJoined := CurrentCallCopiedBoolData.of_copy s machine entry held completion beforeCopyBoolData runtime complete order
      child node nodeAt different within logicalBounds short owned disjoint finalMachine finalEntry
      (by change copied.extra = _
          simpa only [CurrentCallCopiedBoolData.write,CurrentCallCopiedBoolData.read,offset] using copiedTree)
      (by rw [finalMemory]
          change (post.memory.live.filter (fun row => row.1 != call.sourceId)).push (call.sourceId,finalEntry) = _
          rw [sameMemory]) copiedLive
      (by change DuplicatePrefixBorrowContract.RuntimeFacts copied.extra held.global;rw [copiedTree];exact writeRuntime)
      (by change Completes copied.extra completion;rw [copiedTree];exact writeComplete)
      (by change ParentTagOrder copied.extra;rw [copiedTree];exact writeOrder)
      (by change copied.extra.nodes = entry.allocation.extra.nodes;rw [copiedTree];exact writeNodes)
      (by change copied.extra.locations.size = entry.allocation.extra.locations.size;rw [copiedTree];exact writeCapacity)
    have beforeRow : entry = {s.entry with allocation := s.entry.allocation.setExtra entry.allocation.extra} := by
      have expected : machine.memory.live.find? (fun row => row.1 == call.sourceId) =
          some (call.sourceId,{s.entry with allocation := s.entry.allocation.setExtra entry.allocation.extra}) := by
        rw [sourceMemory];exact MemoryCopyBridge.live_lookup_replaced _ _ _
      exact (Prod.mk.inj (Option.some.inj (live.symm.trans expected))).2
    refine {
      boolData := finalBoolJoined
      sourceSize := ?_,sourceLen := ?_,sourceKind := ?_
      model := finalModel,origins := ?_,ready := profile.transport finalExtras,active := finalActor,
      physical := copiedPhysical,storage := ?_,memory := finalHeap,addresses := finalAddresses,
      body := copyBody.trans (resultBody.trans body),identity := copyIdentity.trans (resultIdentity.trans identity),
      callee := copyCallee.trans (resultCallee.trans callee),size := copySize.trans resultSize,
      extra := copyExtra.trans (resultExtra.trans extra),clocks := ?_,
      continuation := copyContinuation.trans (resultContinuation.trans rootContinuation),
      varargs := copyVarargs.trans (resultVarargs.trans rootVarargs),
      immediate := CurrentCallCopyGuardReturn.all_immediate options limits remaining span #[] result post value destinationPointer count ready resultAll,
      zero := ?_,seventeen := ?_,temporaries := ?_}
    · change copied.byteSize = s.entry.allocation.byteSize
      rw [copiedSize,allocation];rfl
    · change copied.len = s.entry.allocation.len
      rw [copiedLen,allocation];rfl
    · change entry.kind = s.entry.kind
      rw [beforeRow]
    · rw [finalTypes];exact origins
    · change copied.len = copied.byteSize.bytes.toNat
      rw [copiedLen,copiedSize];exact bytes
    · exact (congrArg (fun extra => extra.dataRace) (copyExtra.trans resultExtra)).trans clocks
    · rw [copyKeep 0 (by decide),keep 0 (.inl (by decide))];exact rootZero
    · rw [copyKeep 17 (by decide)];exact live17
    · refine ⟨.scalar value,.uninit,.scalar value,.scalar destinationPointer,.scalar (.fromScalarInt (.ofUInt64 count)),?_,?_,?_,?_,?_⟩
      · rw [copyKeep 15 (by decide),keep 15 (.inl (by decide)),slot15];rfl
      · rw [copySlot18];rfl
      · rw [copyKeep 19 (by decide),live19];rfl
      · rw [copyKeep 21 (by decide),live21];rfl
      · rw [copyKeep 24 (by decide),live24];rfl

end
end DuplicatePrefix.CurrentCallAcceptedCopyPrefix
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallAcceptedCopyPrefix.").length != 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved accepted copy prefix dependency {dependency}"
