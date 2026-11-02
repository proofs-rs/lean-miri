import duplicate_prefix.S02WildcardSameDestinationRejectedResult
import duplicate_prefix.S02WildcardReturnSameCountEntry
import duplicate_prefix.S02WildcardReturnSameStep
import duplicate_prefix.GeneralBorrowFreshRootScopedBounds
import duplicate_prefix.GeneralBorrowRawSharedNext
namespace DuplicatePrefix.S02WildcardReturnSameRejectedBody
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.DataStructures
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext GeneralBorrowFreshAnchor
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
attribute [local irreducible] UniValMap.insert
noncomputable section
theorem exposed_construct (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (held : Bool) (offset len : UInt64) (nonzero : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (maximum : BorTag) (bounded : GeneralBorrowFreshRootSupportCutoff.ExposedBound tree maximum) :
    GeneralBorrowFreshRootSupportCutoff.ExposedBound
      (tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag (DedupRangeMap.new (Size.ofBytes len) sharedState) .Frozen held).tree maximum := by
  let rank := GeneralBorrowStructuralHistoryShared.depth tree runtime.formed.toState
  cases GeneralBorrowStructuralHistoryShared.slot tree runtime.formed.toState parent parentNode present room with
  | append noFree accounting fits =>
    let data : GeneralBorrowFreshMetadataChildShared.Input := ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,noFree,accounting,fits,held,offset,len,nonzero,runtime.formed.well,bounds⟩
    change GeneralBorrowFreshRootSupportCutoff.ExposedBound (GeneralBorrowFreshMetadataChildShared.result data) maximum
    rw [GeneralBorrowFreshMetadataChildShared.tree_eq]
    have atEnd : (GeneralBorrowFreshMetadataChildShared.index data).toNat = tree.nodes.data.size := GeneralBorrowFreshMetadataChildShared.at_end data
    have vacant : tree.nodes.get (GeneralBorrowFreshMetadataChildShared.index data) = none := by
      simp only [UniValMap.get,atEnd,Array.getElem?_eq_none (Nat.le_refl _)]
    have stageBound : GeneralBorrowFreshRootSupportCutoff.ExposedBound (GeneralBorrowFreshMetadataChildShared.stage data) maximum := by
      intro query node found flag
      dsimp only [BorrowTree.nodeAt,GeneralBorrowFreshMetadataChildShared.stage,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,data] at found
      exact GeneralBorrowFreshRootScopedBounds.exposed_attach tree _ parent parentNode (sharedNode newTag parent) vacant present rfl maximum bounded query node found flag
    exact GeneralBorrowFreshRootScopedBounds.exposed_sifa (GeneralBorrowFreshMetadataChildShared.stage data) parent .Read maximum stageBound
  | reuse index available valid vacant slack =>
    let data : GeneralBorrowFreshMetadataChildSharedReuse.Input := ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,index,available,valid,vacant,slack,held,offset,len,nonzero,runtime.formed.well,bounds⟩
    change GeneralBorrowFreshRootSupportCutoff.ExposedBound (GeneralBorrowFreshMetadataChildSharedReuse.result data) maximum
    rw [GeneralBorrowFreshMetadataChildSharedReuse.tree_eq]
    have stageBound : GeneralBorrowFreshRootSupportCutoff.ExposedBound (GeneralBorrowFreshMetadataChildSharedReuse.stage data) maximum := by
      intro query node found flag
      dsimp only [BorrowTree.nodeAt,GeneralBorrowFreshMetadataChildSharedReuse.stage,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,data] at found
      exact GeneralBorrowFreshRootScopedBounds.exposed_attach tree index parent parentNode (sharedNode newTag parent) vacant present rfl maximum bounded query node found flag
    exact GeneralBorrowFreshRootScopedBounds.exposed_sifa (GeneralBorrowFreshMetadataChildSharedReuse.stage data) parent .Read maximum stageBound

private theorem exposed_expression (tree : BorrowTree) (tracker : MachineHooks.BorrowState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowRawShared.Input tree tracker.global) (maximum : BorTag)
    (bounded : GeneralBorrowFreshRootSupportCutoff.ExposedBound tree maximum) (held : Bool) :
    GeneralBorrowFreshRootSupportCutoff.ExposedBound
      (GeneralBorrowRawSharedExpression.child tree tracker.global.protectedTags input.parentTag tracker.global.nextPointerTag input.offset input.len .VisitChildrenOfAccessed).tree maximum := by
  obtain ⟨allocated,registeredRuntime,⟨registeredPositive⟩,fresh,unheld⟩ := GeneralBorrowReadTagAllocation.prepare tree tracker.global input.tagRoom runtime input.parent input.selected input.maximum input.offset input.len input.positive
  let registration := GeneralBorrowFnEntryRegistration.advanced tracker.global input.tagRoom
  let read := tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read registration.protectedTags .VisitChildrenOfAccessed
  obtain ⟨contract,afterRuntime,⟨afterPositive⟩⟩ := GeneralBorrowReadRowRange.access tree registration registeredRuntime input.parentTag input.parent input.selected input.maximum input.tagged
    (Size.ofBytes input.offset) (Size.ofBytes input.len) .VisitChildrenOfAccessed input.offset input.len registeredPositive input.distinct input.order input.short (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨node,present⟩ := afterPositive.sourcePresent
  have tag : read.tree.indexOfTag input.parentTag = some input.parent := by unfold BorrowTree.indexOfTag;rw [contract.tags];exact input.tagged
  have freshAfter : GeneralBorrowTagMap.Fresh read.tree.tagMapping tracker.global.nextPointerTag := by rw [contract.tags];exact fresh
  have room : read.tree.nodes.size+1 ≤ 4294967295 := by rw [contract.nodes];exact input.nodeRoom
  have boundAfter : GeneralBorrowFreshRootSupportCutoff.ExposedBound read.tree maximum := by
    intro query value lookup flag
    change read.tree.nodes.get query = some value at lookup
    rw [contract.nodes] at lookup
    exact bounded query value lookup flag
  exact exposed_construct read.tree registration afterRuntime input.parentTag tracker.global.nextPointerTag input.parent node tag present freshAfter room false input.offset input.len
    (by intro zero;have p:=input.positive.positive;rw [zero] at p;contradiction) afterPositive.bounds maximum boundAfter

private theorem exposed_helper (tree : BorrowTree) (tracker : MachineHooks.BorrowState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowRawSharedFnEntry.Input tree tracker.global) (maximum : BorTag)
    (bounded : GeneralBorrowFreshRootSupportCutoff.ExposedBound tree maximum) :
    GeneralBorrowFreshRootSupportCutoff.ExposedBound
      (GeneralBorrowRawSharedFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len) maximum := by
  obtain ⟨allocated,held,pushed,registeredRuntime,⟨registeredPositive⟩,fresh⟩ := GeneralBorrowFnEntryReadRegistration.prepare tree tracker.global ({} : FrameState) ⟨1,by decide⟩ input.tagRoom runtime input.parent input.selected input.maximum input.offset input.len input.positive
  let registration := (GeneralBorrowFnEntryRegistration.registered tracker.global ({} : FrameState) ⟨1,by decide⟩ input.tagRoom).1
  let read := tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read registration.protectedTags .VisitChildrenOfAccessed
  obtain ⟨contract,afterRuntime,⟨afterPositive⟩⟩ := GeneralBorrowReadRowRange.access tree registration registeredRuntime input.parentTag input.parent input.selected input.maximum input.tagged
    (Size.ofBytes input.offset) (Size.ofBytes input.len) .VisitChildrenOfAccessed input.offset input.len registeredPositive input.distinct input.order input.short (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨node,present⟩ := afterPositive.sourcePresent
  have tag : read.tree.indexOfTag input.parentTag = some input.parent := by unfold BorrowTree.indexOfTag;rw [contract.tags];exact input.tagged
  have freshAfter : GeneralBorrowTagMap.Fresh read.tree.tagMapping tracker.global.nextPointerTag := by rw [contract.tags];exact fresh
  have room : read.tree.nodes.size+1 ≤ 4294967295 := by rw [contract.nodes];exact input.nodeRoom
  have boundAfter : GeneralBorrowFreshRootSupportCutoff.ExposedBound read.tree maximum := by
    intro query value lookup flag
    change read.tree.nodes.get query = some value at lookup
    rw [contract.nodes] at lookup
    exact bounded query value lookup flag
  exact exposed_construct read.tree registration afterRuntime input.parentTag tracker.global.nextPointerTag input.parent node tag present freshAfter room true input.offset input.len
    (by intro zero;have p:=input.positive.positive;rw [zero] at p;contradiction) afterPositive.bounds maximum boundAfter

attribute [local irreducible] GeneralBorrowRawSharedExpression.child GeneralBorrowRawSharedFnEntryArgument.finalTree GeneralBorrowRawSharedToLenLiteralLedger.finalTree
/-- The actual shared expression, len-helper FnEntry and release retain every
exposed contributor below the original wildcard return cutoff. -/
theorem literal_exposed (tree : BorrowTree) (tracker : MachineHooks.BorrowState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowRawShared.Input tree tracker.global)
    (shortRoom : tree.nodes.size+2 < 65536) (nodeRoom : tree.nodes.size+2 ≤ 4294967295)
    (tagRoom : tracker.global.nextPointerTag.value.toNat+1 < 18446744073709551615)
    (maximum : BorTag) (bounded : GeneralBorrowFreshRootSupportCutoff.ExposedBound tree maximum) :
    GeneralBorrowFreshRootSupportCutoff.ExposedBound
      (GeneralBorrowRawSharedToLenLiteralLedger.finalTree tree tracker input.parentTag input.offset input.len input.tagRoom) maximum := by
  let expression := (GeneralBorrowRawSharedExpression.child tree tracker.global.protectedTags input.parentTag tracker.global.nextPointerTag input.offset input.len .VisitChildrenOfAccessed).tree
  let next := ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom
  obtain ⟨exprRuntime,capacity,raw,tag,selectedEq,maximumEq,offsetEq,lenEq⟩ := GeneralBorrowRawSharedNext.next_input tree tracker runtime input (by omega) nodeRoom tagRoom
  have exprBound : GeneralBorrowFreshRootSupportCutoff.ExposedBound expression maximum := exposed_expression tree tracker runtime input maximum bounded false
  have exprRuntime : DuplicatePrefixBorrowContract.RuntimeFacts expression next.global := exprRuntime
  have helperBound := exposed_helper expression next exprRuntime raw maximum exprBound
  simp only [tag,offsetEq,lenEq] at helperBound
  let borrowed := GeneralBorrowRawSharedFnEntryArgument.finalTree expression next tracker.global.nextPointerTag input.offset input.len
  let protections := tracker.global.protectedTags.insert next.global.nextPointerTag .StrongProtector
  have frame := GeneralBorrowStructuralReleaseGeometryFrame.release borrowed protections next.global.nextPointerTag
  intro query node present exposed
  unfold GeneralBorrowRawSharedToLenLiteralLedger.finalTree at present
  change (borrowed.releaseProtector next.global.nextPointerTag protections).tree.nodeAt query = some node at present
  rw [frame] at present
  exact helperBound query node present exposed

set_option maxHeartbeats 8000000
/-- Rejected execution from the actual canonical installed call and its generic
current protection packet. This is an internal composition theorem: contract
fronts derive the actual-call equation from the validated initial adapters.
Source provenance does not occur in the body proof. -/
theorem result
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before} {place : MPlaceTy Provenance}
    (pointer : Pointer Provenance) (len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before (.pointer pointer) len place)
    (reference : DuplicatePrefixReferenceInput.Positive before pointer len)
    (currentInput : Before) (destinationInput : DuplicatePrefixReturnPlaceInput.Input currentInput place)
    (fresh : destinationInput.tracker.global.nextPointerTag.value < 18446744073709551615)
    (argumentFrame : CompilerFrameContext.ActualFrame) (owned : FrameState)
    (query selected : UniIndex) (maximum : Option BorTag) (sourceNode : TreeNode)
    (packet : S02WildcardReturnSameCountEntry.Packet options (remaining+1) span limits.retag currentInput place destinationInput
      #[] argumentFrame owned fresh reference.tracker.global.nextPointerTag query selected maximum reference.offset len sourceNode)
    (ownedEq : owned = ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag)
    (sourceSame : sourceNode.tag = reference.tracker.global.nextPointerTag) (initialHidden : sourceNode.isExposed = false)
    (tagDifferent : destinationInput.tracker.global.nextPointerTag ≠ reference.tracker.global.nextPointerTag)
    (sourceId : destinationInput.id = reference.id) (physicalId : destinationInput.id = input.contract.destination.id)
    (sourceDisjoint : (reference.offset+len).toNat ≤ destinationInput.offset.toNat ∨ (destinationInput.offset+1).toNat ≤ reference.offset.toNat)
    (capacity : packet.updated.extra.locations.size = packet.updated.byteSize)
    (nodeReserve : packet.updated.extra.nodes.size+8 < 65536)
    (tagReserve : (TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker destinationInput.tracker fresh)
      destinationInput.tracker.global.nextPointerTag).global.nextPointerTag.value.toNat+7 < 18446744073709551615)
    (mode : destinationInput.tracker.retagMode = .Default)
    (rawUser : currentInput.user = (RawRootInvocation.machine #[] before).user)
    (rawThreads : currentInput.threads = (RawRootInvocation.machine #[] before).threads)
    (rawRace : currentInput.dataRace = (RawRootInvocation.machine #[] before).dataRace)
    (actual : Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
      RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
      #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base (.pointer pointer) len),.Copy (EmptyRootArguments.second count)]
      false (.memory place) (.stop true) ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[]
        (PositiveRootInstalledFrame.installed (RawRootInvocation.root before place input.contract.model.noDataRace)
          (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
            (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag) (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm
          count {} reference.id reference.tracker.global.nextPointerTag destinationInput.id destinationInput.tracker.global.nextPointerTag)
        (S04ProtectUninit.finished currentInput place destinationInput #[] argumentFrame owned fresh packet.tree packet.updated).machine))
    (rejected : count > len/2) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before (.pointer pointer) len count place := by
  let tracker := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker destinationInput.tracker fresh) destinationInput.tracker.global.nextPointerTag
  let borrowFrame := owned.addProtector destinationInput.id destinationInput.tracker.global.nextPointerTag
  let machine := (S04ProtectUninit.finished currentInput place destinationInput #[] argumentFrame owned fresh packet.tree packet.updated).machine
  have rawUser : machine.user = (RawRootInvocation.machine #[] before).user := rawUser
  have rawThreads : machine.threads = (RawRootInvocation.machine #[] before).threads := rawThreads
  have rawRace : machine.dataRace = (RawRootInvocation.machine #[] before).dataRace := rawRace
  let entry := PositiveRootInstalledFrame.installed (RawRootInvocation.root before place input.contract.model.noDataRace)
    (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag) (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm count {} reference.id reference.tracker.global.nextPointerTag destinationInput.id destinationInput.tracker.global.nextPointerTag
  have frameLiteral : entry = PositiveRootInstalledFrame.installed (RawRootInvocation.root before place input.contract.model.noDataRace)
    (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag) (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm count {} reference.id reference.tracker.global.nextPointerTag destinationInput.id destinationInput.tracker.global.nextPointerTag := rfl
  have packetEnabled : machine.borrowTracker = some tracker := rfl
  have packetTracked : entry.extra.borrowTracker = some borrowFrame := by
    change entry.extra.borrowTracker = some (owned.addProtector destinationInput.id destinationInput.tracker.global.nextPointerTag)
    rw [ownedEq];rfl
  let sourceEntry := {destinationInput.entry with allocation := packet.updated}
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag) (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm
  have frameMetadata := PositiveRootInstalledFrame.metadata root adjusted count {} reference.id reference.tracker.global.nextPointerTag destinationInput.id destinationInput.tracker.global.nextPointerTag
  have slots := PositiveRootInstalledFrame.slot_option root (RawRootInvocation.locals before place input.contract.model.noDataRace)
    adjusted count {} reference.id reference.tracker.global.nextPointerTag destinationInput.id destinationInput.tracker.global.nextPointerTag
  have initialSize : entry.locals.size = 25 := by rw [frameLiteral];exact PositiveRootInstalledFrame.size _ _ _ _ _ _ _ _
  have initialBody : entry.body = RootBody.reflected.body.body := by rw [frameLiteral];exact frameMetadata.1
  have initialIdentity : entry.bodyIdentity = RootBody.reflected.body.identity := by rw [frameLiteral];exact frameMetadata.2.1
  have initialCallee : entry.functionInstance = RootBody.reflected.functionInstance := by rw [frameLiteral];exact frameMetadata.2.2.1
  have initialLocation : entry.location = .mir ⟨0,0⟩ := by rw [frameLiteral];exact frameMetadata.2.2.2.2.2.2.2.2
  have initialClocks : entry.extra.dataRace = none := by rw [frameLiteral];exact frameMetadata.2.2.2.2.2.2.1.trans root.noClocks
  have initialAll : CopyHelperCleanup.AllImmediate entry := by
    rw [frameLiteral];exact PositiveRootInstalledFrame.immediate root (RawRootInvocation.locals before place input.contract.model.noDataRace) _ _ _ _ _ _ _
  obtain ⟨rawMemory,rawBorrow,rawRace0,rawAddresses,rawGhost,rawShallow,rawTypes,rawBackend,rawExtras⟩ := RawRootInvocation.preservation #[] before
  have machineGhost : machine.user.payload.ghost = false := by rw [rawUser,rawGhost];exact input.contract.model.ghostOff
  have machineShallow : machine.user.payload.validation = .Shallow := by rw [rawUser,rawShallow];exact input.contract.model.shallow
  have machineUnchecked : ((config options (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false := by
    rw [rawUser,RootZeroInvocationState.raw_control];exact input.contract.model.unchecked
  have machineNoGc : ((config options (remaining+1) span).terminators.getControl machine.user).gcInterval = 0 := by
    rw [rawUser,RootZeroInvocationState.raw_control];exact input.contract.model.noGc
  have machineFixed : machine.threads.fixedScheduling = true := by rw [rawThreads];exact input.contract.model.fixedScheduler
  have validationPositive : 0 < options.limits.validation := by have h:=input.contract.resources.configuredFuel.2.2.2;unfold work at h;omega
  have dynamicPositive : 0 < options.place.dynamicFuel := by have h:=input.contract.resources.dynamicFuel;unfold work at h;omega
  have dispatchPositive : 0 < limits.callDispatch := by have h:=input.contract.resources.executionFuel.1;unfold work at h;omega
  have countNonzero : count ≠ 0 := by
    intro zero
    have h := UInt64.lt_iff_toNat_lt.mp rejected
    rw [zero] at h
    change (len/2).toNat < 0 at h
    omega
  obtain ⟨frame,prefixTrace,shape⟩ := S02SeparateDestinationRejectedPurePrefix.executes_from_installed_locals options limits remaining span
    (DuplicatePrefixCallModel.sourceComparator options remaining span before input.contract.model) input.contract.model.debugOff
    (options.limits.validation-1) (Nat.sub_add_cancel validationPositive).symm entry machine count countNonzero
    initialBody initialIdentity initialCallee initialLocation initialSize adjusted (by intro i;rw [frameLiteral];exact slots i)
    initialClocks initialAll tracker packetEnabled mode machineGhost machineShallow machineUnchecked machineNoGc machineFixed
  let current := RootZeroCompleteState.tick options remaining span machine
  obtain ⟨tickMemory,tickTracker,tickRace,tickThreads,tickAddresses,tickTypes,tickBackend,tickExtras⟩ := S02SeparateDestinationTickLedger.preserved options remaining span machine
  have enabled : current.borrowTracker = some tracker := by rw [tickTracker];exact packetEnabled
  have initialLive : machine.memory.live.find? (fun row => row.1 == destinationInput.id) = some (destinationInput.id,sourceEntry) := MemoryCopyBridge.live_lookup_replaced _ _ _
  have live : current.memory.live.find? (fun row => row.1 == reference.id) = some (reference.id,sourceEntry) := by rw [tickMemory,←sourceId];exact initialLive
  have cached : current.user.addresses.baseAddr.find? (fun row => row.allocId == reference.id) =
      some ⟨reference.id,reference.base⟩ := by
    rw [tickAddresses,rawUser,rawAddresses]
    exact reference.cachedBase
  have types : current.user.payload.payload.user.types = before.user.payload.payload.user.types := by
    rw [tickTypes,rawUser,rawTypes]
  have metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] frame current)).metadata =
      PreparedReflection.actual.runtime := by
    change current.user.payload.payload.user.types.metadata = _
    rw [types]; exact input.contract.model.metadata
  have notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] frame current)).entries.any (·.value.ty == 4) = false := by
    change current.user.payload.payload.user.types.entries.any (·.value.ty == 4) = _
    rw [types]; exact input.slice_not_constructed
  have positive : (0 : UInt64) < len := by
    apply UInt64.lt_iff_toNat_lt.mpr
    have := reference.storage.positive
    exact this
  have nonzero : reference.base+reference.offset ≠ 0 := by
    have h := reference.nonnull
    rw [reference.pointerAddress] at h
    exact h
  have signedFits : len.toNat < 9223372036854775808 := reference.storage.signedSize
  have nodes : sourceEntry.allocation.extra.nodes.size+2 < 65536 := by change packet.updated.extra.nodes.size+2 < 65536;omega
  have nodeRoom : sourceEntry.allocation.extra.nodes.size+2 ≤ 4294967295 := by omega
  have tagRoom : tracker.global.nextPointerTag.value.toNat+1 < 18446744073709551615 := by dsimp only [tracker];omega
  let raw : GeneralBorrowRawShared.Input sourceEntry.allocation.extra tracker.global := {
    parentTag := reference.tracker.global.nextPointerTag,parent := query,selected := selected,maximum := maximum,offset := reference.offset,len := len,
    tagged := packet.sourceTagged,positive := Classical.choice (GeneralBorrowReadRowRange.of_positive _ _ _ _ _ _ _ packet.sourcePositive),
    distinct := packet.distinct,order := by intros;exact packet.order,short := by omega,nodeRoom := by omega,
    tagRoom := by apply UInt64.lt_iff_toNat_lt.mpr;change tracker.global.nextPointerTag.value.toNat < 18446744073709551615;omega }
  have rawTag : raw.parentTag = reference.tracker.global.nextPointerTag := rfl
  have rawParent : raw.parent = query := rfl
  have rawOffset : raw.offset = reference.offset := rfl
  have rawLen : raw.len = len := rfl
  have shortRoom := nodes
  have tagFresh : tracker.global.nextPointerTag.value < 18446744073709551615 := raw.tagRoom
  have body := shape.body.trans initialBody
  have identity := shape.identity.trans initialIdentity
  have callee := shape.callee.trans initialCallee
  have located := shape.location
  have size := shape.size
  have noClocks : frame.extra.dataRace = none := by rw [shape.extra];exact initialClocks
  have sourceCell : frame.locals[1]? = some ⟨.live (.immediate adjusted),some ActualReferenceMetadata.reference⟩ := by rw [shape.slot1];exact slots ⟨1,by decide⟩
  have lenCell := shape.slot11
  have exprCell := shape.slot12
  have immediate := shape.immediate
  have slot0 : frame.locals[0]? = some ⟨.live (.immediate .uninit),none⟩ := by rw [shape.slot0];exact slots ⟨0,by decide⟩
  have slot13 : frame.locals[13]? = some ⟨.live (.immediate .uninit),none⟩ := by rw [shape.keep 13 (by decide)];exact slots ⟨13,by decide⟩
  have slot7 := shape.slot7
  have slot8 := shape.slot8
  have slot9 := shape.slot9
  have slot10 := shape.slot10
  have validSource : (1 : MIR.LocalId) < frame.locals.size := by rw [size]; decide
  have validDest : RootReferenceFacts.destination true < frame.locals.size := by rw [size]; decide
  have valid11 : 11 < frame.locals.size := by rw [size]; decide
  have sourceLive : frame.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config options (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
        (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm) := by
    have h := congrArg LocalState.value (Option.some.inj
      (by simpa [Array.getElem?_eq_getElem validSource] using sourceCell))
    dsimp only [adjusted] at h
    rw [CanonicalConfigFacts.actual_access_runtime options () remaining span,
      CanonicalConfigFacts.actual_access_runtime options () (remaining+1) span] at *
    exact h
  have sourceCached : frame.locals[1].layout = some ActualReferenceMetadata.reference := by
    exact congrArg LocalState.layout (Option.some.inj
      (by simpa [Array.getElem?_eq_getElem validSource] using sourceCell))
  have lenLive : frame.locals[11].value = .live (.immediate .uninit) := by
    exact congrArg LocalState.value (Option.some.inj
      (by simpa [Array.getElem?_eq_getElem valid11] using lenCell))
  have lenUncached : frame.locals[11].layout = none := by
    exact congrArg LocalState.layout (Option.some.inj
      (by simpa [Array.getElem?_eq_getElem valid11] using lenCell))
  have destCellValid : (12 : MIR.LocalId) < frame.locals.size := by rw [size]; decide
  have destLive : frame.locals[RootReferenceFacts.destination true].value = .live (.immediate .uninit) := by
    have h := congrArg LocalState.value (Option.some.inj
      (by simpa [Array.getElem?_eq_getElem destCellValid] using exprCell))
    simpa [RootReferenceFacts.destination] using h
  have destUncached : frame.locals[RootReferenceFacts.destination true].layout = none := by
    have h := congrArg LocalState.layout (Option.some.inj
      (by simpa [Array.getElem?_eq_getElem destCellValid] using exprCell))
    simpa [RootReferenceFacts.destination] using h
  have noClocks' : frame.extra.dataRace = none := noClocks
  have ghost : current.user.payload.ghost = false := by
    rw [RootZeroCompleteState.tick_ghost,rawUser,rawGhost]
    exact input.contract.model.ghostOff
  have shallow : current.user.payload.validation = .Shallow := by
    rw [RootZeroCompleteState.tick_shallow,rawUser,rawShallow]
    exact input.contract.model.shallow
  have race : current.dataRace = none := by
    rw [tickRace,rawRace,rawRace0]; exact input.contract.model.noDataRace
  have backend : current.user.payload.payload.user.backend = .none := by
    rw [tickBackend,rawUser,rawBackend]; exact input.contract.model.noBackend
  have unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl current.user).checkedArithmetic = false := by
    rw [(RootZeroCompleteState.tick_flags options remaining span machine).1,rawUser,RootZeroInvocationState.raw_control]
    exact input.contract.model.unchecked
  have noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl current.user).gcInterval = 0 := by
    rw [(RootZeroCompleteState.tick_flags options remaining span machine).2,rawUser,RootZeroInvocationState.raw_control]
    exact input.contract.model.noGc
  have fixed : current.threads.fixedScheduling = true := by
    rw [tickThreads,rawThreads]
    change before.threads.fixedScheduling = true
    exact input.contract.model.fixedScheduler
  have rawActive : (RawRootInvocation.machine #[] before).threads.activeThread? =
      some {input.contract.thread with topUserRelevantFrame := some 0} := by
    change (CallEntryFacts.cacheTop (CallEntryFacts.freshRoot before).1 0).threads.activeThread? = _
    exact AsMutPushPreserves.active_cache (CallEntryFacts.freshRoot before).1 input.contract.thread
      (by simpa only [CallEntryFacts.freshRoot] using input.contract.active) 0
  have active : current.threads.activeThread? =
      some {input.contract.thread with topUserRelevantFrame := some 0} := by
    rw [tickThreads,rawThreads]; exact rawActive
  let thread := {input.contract.thread with topUserRelevantFrame := some 0}
  have topZero : ({input.contract.thread with topUserRelevantFrame := some 0}).topUserRelevantFrame = some 0 := rfl
  have bothRaw : DuplicatePrefixBorrowAuthorization.Positive sourceEntry.allocation.extra tracker.global.protectedTags (some raw.parent) (some raw.selected) raw.maximum reference.offset len := packet.sourcePositive
  have activityRaw : GeneralBorrowFreshActiveWithin.ActiveWithin sourceEntry.allocation.extra raw.parent .Write reference.offset (reference.offset+len) := packet.sourceActivity
  have cell (n : Fin 25) : n.val < frame.locals.size := by rw [size];exact n.isLt
  have fromSlot (n : Fin 25) (value : LocalState Provenance LocalLayout) (h : frame.locals[n.val]? = some value) :
      frame.locals[n.val]'(cell n) = value := Option.some.inj ((Array.getElem?_eq_getElem (cell n)).symm.trans h)
  obtain ⟨done,post,finalTree,held,child,bodyTrace,location,sizeDone,bodyDone,identityDone,calleeDone,extraDone,
    placeDone,contDone,vaDone,localIdDone,slotFalse,allDone,postMemory,postTracker,modeAfter,runtimeAfter,readAfter,⟨bothAfter⟩,sourceActivity,graph,addressesAfter,typesAfter,extrasAfter,ghostAfter,shallowAfter,raceAfter,backendAfter,
    uncheckedAfter,noGcAfter,fixedAfter,finalThread,finalActive,finalTop,treeLiteral⟩ :=
    GeneralBorrowRawSharedToRejectedLiteralLedgerState.complete options limits remaining span
      input.contract.model.preciseOff input.contract.model.implicitOff input.contract.model.debugOff
      input.contract.model.nullComparator (options.place.dynamicFuel-1) (options.limits.validation-1)
      (Nat.sub_add_cancel dynamicPositive).symm (Nat.sub_add_cancel validationPositive).symm
      reference.base reference.offset len reference.id sourceEntry positive nonzero signedFits #[] frame current
      body identity callee located tracker enabled mode tagFresh reference.tracker.global.nextPointerTag
      packet.runtime raw rawTag rawOffset rawLen capacity validSource validDest sourceLive sourceCached
      destLive destUncached noClocks ghost shallow cached live race metadata notConstructed
      shortRoom nodeRoom tagRoom rfl (limits.callDispatch-1) (Nat.sub_add_cancel dispatchPositive).symm
      (DuplicatePrefixCallModel.sourceComparator options remaining span before input.contract.model)
      valid11 lenLive lenUncached backend unchecked noGc fixed thread active topZero
      count rejected size
      (congrArg LocalState.value (fromSlot ⟨13,by decide⟩ _ slot13))
      (congrArg LocalState.layout (fromSlot ⟨13,by decide⟩ _ slot13))
      (congrArg LocalState.value (fromSlot ⟨0,by decide⟩ _ slot0))
      (congrArg LocalState.layout (fromSlot ⟨0,by decide⟩ _ slot0))
      (congrArg LocalState.value (fromSlot ⟨7,by decide⟩ _ slot7))
      (congrArg LocalState.value (fromSlot ⟨8,by decide⟩ _ slot8))
      (congrArg LocalState.layout (fromSlot ⟨8,by decide⟩ _ slot8))
      (congrArg LocalState.value (fromSlot ⟨9,by decide⟩ _ slot9))
      (congrArg LocalState.layout (fromSlot ⟨9,by decide⟩ _ slot9))
      (congrArg LocalState.value (fromSlot ⟨10,by decide⟩ _ slot10))
      (congrArg LocalState.layout (fromSlot ⟨10,by decide⟩ _ slot10)) immediate bothRaw activityRaw
  have literalEq : finalTree = GeneralBorrowRawSharedToLenLiteralLedger.finalTree sourceEntry.allocation.extra tracker raw.parentTag raw.offset raw.len raw.tagRoom := by
    simpa only [rawTag,rawOffset,rawLen] using treeLiteral
  have childrenDifferent : raw.parent ≠ packet.child := by
    intro same
    change query = packet.child at same
    have oldPresent : packet.updated.extra.nodeAt packet.child = some sourceNode :=
      (congrArg packet.updated.extra.nodeAt same).symm.trans packet.sourcePresent
    have nodeEq : sourceNode = packet.returnNode := Option.some.inj (oldPresent.symm.trans packet.returnPresent)
    exact tagDifferent (packet.returnSame.symm.trans ((congrArg TreeNode.tag nodeEq).symm.trans sourceSame))
  obtain ⟨sourceNode,sourcePresent,sourceNodeTag,sourceParent,sourceHidden,sourceTagged⟩ := graph.oldNodes query sourceNode packet.sourcePresent
  have finalSourceTagged : finalTree.indexOfTag raw.parentTag = some raw.parent := by
    simpa only [rawTag,rawParent,sourceSame] using sourceTagged
  have finalSourceHidden : sourceNode.isExposed = false := sourceHidden.trans initialHidden
  have finalSourcePresent : finalTree.nodeAt raw.parent = some sourceNode := by simpa only [rawParent] using sourcePresent
  obtain ⟨returnActivity,returnNode,returnPresent,returnSame,returnEdge,returnLeaf,returnHidden⟩ :=
    S02SameDestinationRejectedResultLiteralActivity.preserves sourceEntry.allocation.extra tracker reference.id packet.runtime raw nodes nodeRoom tagRoom
      packet.child packet.returnNode packet.returnPresent packet.leaf packet.hidden (Ne.symm childrenDifferent)
      destinationInput.offset (destinationInput.offset+1) packet.returnActivity
  rw [←literalEq] at returnActivity returnPresent
  have returnTagged : finalTree.indexOfTag destinationInput.tracker.global.nextPointerTag = some packet.child := by
    obtain ⟨node,present,tagEq,parentEq,hiddenEq,tagged⟩ := graph.oldNodes packet.child packet.returnNode packet.returnPresent
    rw [←packet.returnSame];exact tagged
  let original := packet.physical
  let destination : S04FinalReturnWildcardInput.Destination post place := {
    pointer := original.pointer,physicalPointer := original.physicalPointer,layout := original.layout,aligned := original.aligned,
    id := original.id,entry := {original.entry with allocation := original.entry.allocation.setExtra finalTree},
    base := original.base,offset := original.offset,capacity := original.capacity,
    live := by rw [postMemory,packet.physicalId,packet.physicalEntry,sourceId];exact MemoryCopyBridge.live_lookup_replaced _ _ _,
    cachedBase := by rw [addressesAfter,tickAddresses];exact original.cachedBase,
    pointerAddress := original.pointerAddress,nonnull := original.nonnull,addressFits := original.addressFits,bounds := original.bounds,
    size := original.size,bytes := original.bytes,mutable := original.mutable,maskValid := original.maskValid,maskLength := original.maskLength,
    pointerBounds := original.pointerBounds,borrowSize := by
      change finalTree.locations.size.bytes = original.capacity
      have oldBorrow := original.borrowSize
      change packet.physical.entry.allocation.extra.locations.size.bytes = original.capacity at oldBorrow
      rw [packet.physicalEntry] at oldBorrow
      exact (congrArg (fun value : Size => value.bytes) graph.capacity).trans oldBorrow,
    wildcard := original.wildcard,mode := by rw [addressesAfter,tickAddresses];exact original.mode,
    exposed := by rw [addressesAfter,tickAddresses];exact original.exposed,
    geometry := by rw [addressesAfter,tickAddresses];exact original.geometry }
  have destinationTree : destination.entry.allocation.extra = finalTree := rfl
  have offsetEq : destination.offset = destinationInput.offset := packet.physicalOffset
  have disjoint : raw.offset.toNat+raw.len.toNat ≤ destinationInput.offset.toNat ∨ (destinationInput.offset+1).toNat ≤ raw.offset.toNat := by
    have stop : (reference.offset+len).toNat = reference.offset.toNat+len.toNat := by
      rw [UInt64.toNat_add,Nat.mod_eq_of_lt];exact Nat.lt_of_le_of_lt packet.sourcePositive.bounds packet.updated.extra.locations.size.bytes.toNat_lt
    simpa only [rawOffset,rawLen,stop] using sourceDisjoint
  obtain ⟨returnPositive⟩ := S02DisjointSharedLenLiteral.destination sourceEntry.allocation.extra tracker reference.id packet.runtime raw nodes nodeRoom tagRoom
    (some packet.child) (some packet.child) (some destinationInput.tracker.global.nextPointerTag) destinationInput.offset 1 disjoint packet.returnPositive
  rw [←literalEq,←graph.protections] at returnPositive
  have sourceOwned : borrowFrame.protectedTags = #[(destination.id,raw.parentTag),(destination.id,destinationInput.tracker.global.nextPointerTag)] := by
    change borrowFrame.protectedTags = #[(packet.physical.id,raw.parentTag),(packet.physical.id,destinationInput.tracker.global.nextPointerTag)]
    rw [packet.physicalId]
    dsimp only [borrowFrame]
    rw [ownedEq]
    change #[(reference.id,reference.tracker.global.nextPointerTag),(destinationInput.id,destinationInput.tracker.global.nextPointerTag)] = #[(destinationInput.id,reference.tracker.global.nextPointerTag),(destinationInput.id,destinationInput.tracker.global.nextPointerTag)]
    simp only [sourceId]
  have finalSourceActivity := S02HiddenLeafActiveRelease.release finalTree held.global runtimeAfter raw.parentTag raw.parent raw.selected raw.maximum
    reference.offset len bothAfter sourceNode finalSourcePresent finalSourceHidden finalSourceTagged graph.distinct graph.order graph.short sourceActivity
    packet.child returnNode returnPresent returnLeaf returnHidden (Ne.symm childrenDifferent) destinationInput.offset (destinationInput.offset+1) returnActivity
  have hiddenFrame := S02SameDestinationHiddenFrame.of_hidden finalTree held.global borrowFrame destination.id destination.id raw.parentTag
    destinationInput.tracker.global.nextPointerTag packet.child returnNode sourceOwned runtimeAfter raw.parent sourceNode finalSourceTagged finalSourcePresent finalSourceHidden returnTagged returnPresent returnHidden
  have finalOrder : GeneralBorrowWildcardParentTagOrder.ParentTagOrder finalTree := by
    rw [literalEq];exact S02SameDestinationRejectedResultOrder.literal sourceEntry.allocation.extra tracker reference.id packet.runtime raw nodes nodeRoom tagRoom packet.order
  have finalExposed : GeneralBorrowFreshRootSupportCutoff.ExposedBound finalTree destinationInput.tracker.global.nextPointerTag := by
    rw [literalEq];exact literal_exposed sourceEntry.allocation.extra tracker packet.runtime raw nodes nodeRoom tagRoom _ packet.exposed
  have finalNotPrimary : ∀ valid : 0<finalTree.roots.size,finalTree.roots[0]≠packet.child := by
    intro valid
    have oldValid : 0<sourceEntry.allocation.extra.roots.size := by simpa only [graph.roots] using valid
    simpa only [graph.roots] using packet.notPrimary oldValid
  have finalExtras : post.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == destination.id) = some (destination.id,⟨none,#[]⟩) := by
    change post.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == packet.physical.id) = _
    rw [packet.physicalId,extrasAfter,tickExtras,rawUser,rawExtras,physicalId];exact input.return_extras
  have valid0 : 0<done.locals.size := by rw [sizeDone];decide
  have cell0 := Option.some.inj ((Array.getElem?_eq_getElem valid0).symm.trans slotFalse)
  have frameTracked : done.extra.borrowTracker = some borrowFrame := by rw [extraDone,shape.extra];exact packetTracked
  have clocksDone : done.extra.dataRace = none := by rw [extraDone];exact noClocks
  have returnPlace : done.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩ := by rw [placeDone,shape.returnPlace,frameLiteral,frameMetadata.2.2.2.2.1];rfl
  have continuation : done.returnContinuation = .stop true := by rw [contDone,shape.continuation,frameLiteral];exact frameMetadata.2.2.2.1
  have varargs : done.vaList = #[] := by rw [vaDone,shape.vaList,frameLiteral,frameMetadata.2.2.2.2.2.1];rfl
  obtain ⟨updated,returnStep,_,_,_⟩ := S02WildcardReturnSameStep.step options limits remaining span done post held borrowFrame postTracker frameTracked
    place destination raw.parentTag raw.parent raw.selected raw.maximum reference.offset len sourceNode finalSourceTagged finalSourcePresent finalSourceHidden bothAfter sourceActivity
    destinationInput.tracker.global.nextPointerTag packet.child returnNode returnTagged returnPresent (returnSame.trans packet.returnSame)
    (returnEdge.trans packet.parentless) returnLeaf returnHidden sourceOwned hiddenFrame runtimeAfter (by simpa only [destinationTree,offsetEq] using returnPositive) graph.distinct finalOrder finalExposed finalNotPrimary graph.short
    (by simpa only [offsetEq] using sourceDisjoint) (by simpa only [destinationTree,offsetEq] using finalSourceActivity) finalThread finalActive raceAfter backendAfter ghostAfter shallowAfter #[] finalExtras (by simp)
    false (options.limits.validation-1) input.contract.model.debugOff (Nat.sub_add_cancel validationPositive).symm
    (bodyDone.trans body) location valid0 (congrArg LocalState.value cell0) (congrArg LocalState.layout cell0) clocksDone returnPlace continuation allDone varargs uncheckedAfter noGcAfter fixedAfter
  let accounted := S04FinalReturnRuleAccounting.machine options remaining span done post
  let sourceReleased := (finalTree.releaseProtector raw.parentTag held.global.protectedTags).tree
  let priorMemory := StackPopRelease.commitTree accounted.memory destination.id destination.entry sourceReleased
  let released := (sourceReleased.releaseProtector destinationInput.tracker.global.nextPointerTag held.global.protectedTags).tree
  let after := S04FinalReturnVariantsInput.afterPop #[] done accounted held borrowFrame priorMemory destination.id destination.entry released (finalThread.topUserRelevantFrame.getD 0)
  let finished := CanonicalCopy.replaceAllocation after destination.id destination.entry.kind updated
  have last : ExecutionMachine.step (config options (remaining+1) span) limits () (Storage.withCurrent #[] done post) = (finished,.ok true) := returnStep
  have trace := SuccessfulTrace.append (SuccessfulTrace.append prefixTrace bodyTrace) (.next last (.refl _))
  let safety : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit := ⟨config options (remaining+1) span,limits,fun _ _ => True⟩
  have entered : CallSafety.IsCallEntry 1 (Storage.withCurrent #[] entry machine) := by simp [CallSafety.IsCallEntry,CallSafety.frameDepth,Storage.withCurrent]
  have exited : CallSafety.pastCallBoundary 1 finished := by change (0:Nat)<1;decide
  have terminal : ExecutionMachine.step (config options (remaining+1) span) limits () finished = (finished,.ok false) := rfl
  exact ⟨Storage.withCurrent #[] entry machine,finished,actual,trace,terminal,rfl,
    SuccessfulTrace.no_errors safety 1 _ finished entered trace exited,SuccessfulTrace.no_ub safety 1 _ finished entered trace exited,
    SuccessfulTraceTerminal.prefix_step_success trace terminal⟩

end
end DuplicatePrefix.S02WildcardReturnSameRejectedBody

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S02WildcardReturnSameRejectedBody." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved wildcard same rejected body dependency {dependency}"
