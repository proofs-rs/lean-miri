import duplicate_prefix.S02WildcardReturnSameRejectedBody
import duplicate_prefix.S02SameDestinationAcceptedGuardLedger
import duplicate_prefix.S02WildcardReturnSameAcceptedPhysical
import duplicate_prefix.S02SameDestinationAcceptedResult
import duplicate_prefix.GeneralBorrowFreshRootScopedBounds
import duplicate_prefix.GeneralBorrowStructuralHistoryMutable
namespace DuplicatePrefix.S02WildcardReturnSameAcceptedBody
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.DataStructures
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
attribute [local irreducible] UniValMap.insert
private theorem exposed_construct (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (held : Bool) (offset len : UInt64) (nonzero : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (maximum : BorTag) (bounded : GeneralBorrowFreshRootSupportCutoff.ExposedBound tree maximum) :
    GeneralBorrowFreshRootSupportCutoff.ExposedBound
      (tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
        (DedupRangeMap.new (Size.ofBytes len) (if held then GeneralBorrowFreshChild.inside else GeneralBorrowFreshDefaultChild.inside)) (.ReservedFrz false) held).tree maximum := by
  let rank := GeneralBorrowStructuralHistoryMutable.depth tree runtime.formed.toState
  cases held
  · cases GeneralBorrowStructuralHistoryMutable.slot tree runtime.formed.toState parent parentNode present room with
    | append noFree accounting fits =>
      let data : GeneralBorrowFreshMetadataChildDefault.Input := ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,noFree,accounting,fits,offset,len,nonzero,runtime.formed.well,bounds⟩
      change GeneralBorrowFreshRootSupportCutoff.ExposedBound (GeneralBorrowFreshMetadataChildDefault.result data) maximum
      rw [GeneralBorrowFreshMetadataChildDefault.tree_eq]
      have atEnd : (GeneralBorrowFreshMetadataChildDefault.index data).toNat = tree.nodes.data.size := GeneralBorrowFreshMetadataChildDefault.at_end data
      have vacant : tree.nodes.get (GeneralBorrowFreshMetadataChildDefault.index data) = none := by
        simp only [UniValMap.get,atEnd,Array.getElem?_eq_none (Nat.le_refl _)]
      have stageBound : GeneralBorrowFreshRootSupportCutoff.ExposedBound (GeneralBorrowFreshMetadataChildDefault.stage data) maximum := by
        intro query node found flag
        dsimp only [BorrowTree.nodeAt,GeneralBorrowFreshMetadataChildDefault.stage,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,data] at found
        exact GeneralBorrowFreshRootScopedBounds.exposed_attach tree _ parent parentNode (GeneralBorrowFreshDefaultChild.child newTag parent) vacant present rfl maximum bounded query node found flag
      exact GeneralBorrowFreshRootScopedBounds.exposed_sifa (GeneralBorrowFreshMetadataChildDefault.stage data) parent .Read maximum stageBound
    | reuse index available valid vacant slack =>
      let data : GeneralBorrowFreshMetadataChildDefaultReuse.Input := ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,index,available,valid,vacant,slack,offset,len,nonzero,runtime.formed.well,bounds⟩
      change GeneralBorrowFreshRootSupportCutoff.ExposedBound (GeneralBorrowFreshMetadataChildDefaultReuse.result data) maximum
      rw [GeneralBorrowFreshMetadataChildDefaultReuse.tree_eq]
      have stageBound : GeneralBorrowFreshRootSupportCutoff.ExposedBound (GeneralBorrowFreshMetadataChildDefaultReuse.stage data) maximum := by
        intro query node found flag
        dsimp only [BorrowTree.nodeAt,GeneralBorrowFreshMetadataChildDefaultReuse.stage,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,data] at found
        exact GeneralBorrowFreshRootScopedBounds.exposed_attach tree index parent parentNode (GeneralBorrowFreshDefaultChild.child newTag parent) vacant present rfl maximum bounded query node found flag
      exact GeneralBorrowFreshRootScopedBounds.exposed_sifa (GeneralBorrowFreshMetadataChildDefaultReuse.stage data) parent .Read maximum stageBound
  · cases GeneralBorrowStructuralHistoryMutable.slot tree runtime.formed.toState parent parentNode present room with
    | append noFree accounting fits =>
      let data : GeneralBorrowFreshMetadataChildMutable.Input := ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,noFree,accounting,fits,offset,len,nonzero,runtime.formed.well,bounds⟩
      change GeneralBorrowFreshRootSupportCutoff.ExposedBound (GeneralBorrowFreshMetadataChildMutable.result data) maximum
      rw [GeneralBorrowFreshMetadataChildMutable.tree_eq]
      have atEnd : (GeneralBorrowFreshMetadataChildMutable.index data).toNat = tree.nodes.data.size := GeneralBorrowFreshMetadataChildMutable.at_end data
      have vacant : tree.nodes.get (GeneralBorrowFreshMetadataChildMutable.index data) = none := by
        simp only [UniValMap.get,atEnd,Array.getElem?_eq_none (Nat.le_refl _)]
      have stageBound : GeneralBorrowFreshRootSupportCutoff.ExposedBound (GeneralBorrowFreshMetadataChildMutable.stage data) maximum := by
        intro query node found flag
        dsimp only [BorrowTree.nodeAt,GeneralBorrowFreshMetadataChildMutable.stage,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,data] at found
        exact GeneralBorrowFreshRootScopedBounds.exposed_attach tree _ parent parentNode (GeneralBorrowFreshChild.child newTag parent) vacant present rfl maximum bounded query node found flag
      exact GeneralBorrowFreshRootScopedBounds.exposed_sifa (GeneralBorrowFreshMetadataChildMutable.stage data) parent .None maximum stageBound
    | reuse index available valid vacant slack =>
      let data : GeneralBorrowFreshMetadataChildMutableReuse.Input := ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,index,available,valid,vacant,slack,offset,len,nonzero,runtime.formed.well,bounds⟩
      change GeneralBorrowFreshRootSupportCutoff.ExposedBound (GeneralBorrowFreshMetadataChildMutableReuse.result data) maximum
      rw [GeneralBorrowFreshMetadataChildMutableReuse.tree_eq]
      have stageBound : GeneralBorrowFreshRootSupportCutoff.ExposedBound (GeneralBorrowFreshMetadataChildMutableReuse.stage data) maximum := by
        intro query node found flag
        dsimp only [BorrowTree.nodeAt,GeneralBorrowFreshMetadataChildMutableReuse.stage,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,data] at found
        exact GeneralBorrowFreshRootScopedBounds.exposed_attach tree index parent parentNode (GeneralBorrowFreshChild.child newTag parent) vacant present rfl maximum bounded query node found flag
      exact GeneralBorrowFreshRootScopedBounds.exposed_sifa (GeneralBorrowFreshMetadataChildMutableReuse.stage data) parent .None maximum stageBound

private theorem exposed_default (tree : BorrowTree) (tracker : MachineHooks.BorrowState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global) (input : GeneralBorrowRawDefault.Input tree tracker.global)
    (maximum : BorTag) (bounded : GeneralBorrowFreshRootSupportCutoff.ExposedBound tree maximum) :
    GeneralBorrowFreshRootSupportCutoff.ExposedBound (GeneralBorrowRawDefaultExpression.child tree tracker.global.protectedTags input.parentTag
      tracker.global.nextPointerTag input.offset input.len .VisitChildrenOfAccessed).tree maximum := by
  obtain ⟨allocated,registeredRuntime,⟨registeredPositive⟩,fresh,_⟩ := GeneralBorrowDefaultTagAllocation.prepare tree tracker.global input.tagRoom runtime input.parent input.selected input.maximum input.offset input.len input.positive
  let registration := GeneralBorrowFnEntryRegistration.advanced tracker.global input.tagRoom
  let read := tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read registration.protectedTags .VisitChildrenOfAccessed
  obtain ⟨contract,afterRuntime,⟨afterPositive⟩⟩ := GeneralBorrowConcreteRowReadRange.access_runtime tree registration registeredRuntime input.parentTag input.parent input.selected input.maximum input.tagged
    (Size.ofBytes input.offset) (Size.ofBytes input.len) .VisitChildrenOfAccessed input.offset input.len registeredPositive input.distinct input.order input.short (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨node,present⟩ := afterPositive.sourcePresent input.parent rfl
  have tag : read.tree.indexOfTag input.parentTag = some input.parent := by unfold BorrowTree.indexOfTag;rw [contract.tags];exact input.tagged
  have freshAfter : GeneralBorrowTagMap.Fresh read.tree.tagMapping tracker.global.nextPointerTag := by rw [contract.tags];exact fresh
  have room : read.tree.nodes.size+1 ≤ 4294967295 := by rw [contract.nodes];exact input.nodeRoom
  have boundAfter : GeneralBorrowFreshRootSupportCutoff.ExposedBound read.tree maximum := by
    intro index node found exposed
    apply bounded index node _ exposed
    change read.tree.nodes.get index = some node at found
    change tree.nodes.get index = some node
    rwa [contract.nodes] at found
  exact exposed_construct read.tree registration afterRuntime input.parentTag tracker.global.nextPointerTag input.parent node tag present freshAfter room false input.offset input.len
    (by intro zero;have p:=input.positive.positive;rw [zero] at p;contradiction) afterPositive.bounds maximum boundAfter

private theorem exposed_helper (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global) (input : GeneralBorrowRawFnEntry.Input tree tracker.global)
    (maximum : BorTag) (bounded : GeneralBorrowFreshRootSupportCutoff.ExposedBound tree maximum) :
    GeneralBorrowFreshRootSupportCutoff.ExposedBound (GeneralBorrowRawFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len) maximum := by
  obtain ⟨allocated,held,frameEq,registeredRuntime,⟨registeredPositive⟩,fresh⟩ := GeneralBorrowFnEntryRegistration.prepare tree tracker.global {} allocation input.tagRoom runtime input.parent input.selected input.maximum input.offset input.len input.positive
  let registration := (GeneralBorrowFnEntryRegistration.registered tracker.global {} allocation input.tagRoom).1
  let read := tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read registration.protectedTags .VisitChildrenOfAccessed
  obtain ⟨contract,afterRuntime,⟨afterPositive⟩⟩ := GeneralBorrowConcreteRowReadRange.access_runtime tree registration registeredRuntime input.parentTag input.parent input.selected input.maximum input.tagged
    (Size.ofBytes input.offset) (Size.ofBytes input.len) .VisitChildrenOfAccessed input.offset input.len registeredPositive input.distinct input.order input.short (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨node,present⟩ := afterPositive.sourcePresent input.parent rfl
  have tag : read.tree.indexOfTag input.parentTag = some input.parent := by unfold BorrowTree.indexOfTag;rw [contract.tags];exact input.tagged
  have freshAfter : GeneralBorrowTagMap.Fresh read.tree.tagMapping tracker.global.nextPointerTag := by rw [contract.tags];exact fresh
  have room : read.tree.nodes.size+1 ≤ 4294967295 := by rw [contract.nodes];exact input.nodeRoom
  have boundAfter : GeneralBorrowFreshRootSupportCutoff.ExposedBound read.tree maximum := by
    intro index node found exposed
    apply bounded index node _ exposed
    change read.tree.nodes.get index = some node at found
    change tree.nodes.get index = some node
    rwa [contract.nodes] at found
  exact exposed_construct read.tree registration afterRuntime input.parentTag tracker.global.nextPointerTag input.parent node tag present freshAfter room true input.offset input.len
    (by intro zero;have p:=input.positive.positive;rw [zero] at p;contradiction) afterPositive.bounds maximum boundAfter


/-- The saved return cutoff and root array survive the two real mutable
constructors, helper release, and physical copy graph on the same allocation. -/
theorem mutable_metadata (original : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (id : AllocId) (base offset len count : UInt64)
    (tracker : MachineHooks.BorrowState) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts original.allocation.extra tracker.global)
    (raw : GeneralBorrowRawDefault.Input original.allocation.extra tracker.global)
    (headroom : original.allocation.extra.nodes.size+2 < 65536) (tagsRoom : tracker.global.nextPointerTag.value.toNat+1 < 18446744073709551615)
    (packet : GeneralBorrowRawAsMutToCopy.Input) (result : Allocation Provenance BorrowTree)
    (connection : S02SameDestinationAcceptedSourceLedger.Connection original machine id base offset len count tracker raw packet result)
    (maximum : BorTag) (bounded : GeneralBorrowFreshRootSupportCutoff.ExposedBound original.allocation.extra maximum) :
    GeneralBorrowFreshRootSupportCutoff.ExposedBound result.extra maximum ∧ result.extra.roots = original.allocation.extra.roots := by
  let tree := original.allocation.extra
  let expr := (GeneralBorrowRawDefaultExpression.child tree tracker.global.protectedTags raw.parentTag tracker.global.nextPointerTag raw.offset raw.len .VisitChildrenOfAccessed).tree
  let advanced := ReferenceBorrowDriver.allocatedTracker tracker raw.tagRoom
  have exprBound := exposed_default tree tracker runtime raw maximum bounded
  obtain ⟨exprRuntime,_,_,next,nextTag,_,_,nextOffset,nextLen⟩ := GeneralBorrowRawDefaultResources.resources tree tracker runtime raw headroom tagsRoom
  have helperBound := exposed_helper expr advanced id exprRuntime next maximum exprBound
  simp only [nextTag,nextOffset,nextLen] at helperBound
  have second := GeneralBorrowRawFnEntryResources.resources expr advanced {} id exprRuntime next
  have helperRoots := second.2.2.2.1
  simp only [nextTag,nextOffset,nextLen] at helperRoots
  obtain ⟨secondFresh,resources⟩ := connection.resources
  have copyNodes : result.extra.nodes = packet.entry.allocation.extra.nodes := by rw [connection.tree];exact GeneralBorrowRawMutableParentRestore.copy_nodes packet
  have copyRoots : result.extra.roots = packet.entry.allocation.extra.roots := by rw [connection.tree];exact GeneralBorrowRawMutablePolicyMetadata.copy_roots packet
  constructor
  · intro index node found exposed
    apply helperBound index node _ exposed
    change result.extra.nodes.get index = some node at found
    rw [copyNodes,resources.treeEq] at found
    exact found
  · obtain ⟨output,actual,_tag,_advanced,_protections,_readDone,_childDone,_runtime,_capacity,_growth,_child,_tagged,roots,_positive⟩ := GeneralBorrowRawDefault.invoke_positive tree tracker.global runtime raw
    have shape := actual
    simp only [GeneralBorrowRawDefault.operation,TypedRetagEmpty.allocate_tag tracker.global raw.tagRoom,Except.bind,Except.pure,bind,pure] at shape
    have outputEq := Except.ok.inj shape
    subst output
    change expr.roots = tree.roots at roots
    rw [copyRoots,resources.treeEq]
    exact helperRoots.trans roots
/-- Accepted execution from the actual canonical installed call and its generic
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
    (modelCurrent : DuplicatePrefixCallModel.Model options (remaining+1) span currentInput)
    (initialRuntime : DuplicatePrefixBorrowContract.RuntimeFacts destinationInput.entry.allocation.extra destinationInput.tracker.global)
    (initialDistinct : destinationInput.entry.allocation.extra.roots.toList.Nodup)
    (initialOrder : GeneralBorrowWildcardParentTagOrder.ParentTagOrder destinationInput.entry.allocation.extra)
    (initialRoom : destinationInput.entry.allocation.extra.nodes.size+1 < 65536)
    (wildcard : destinationInput.pointer.provenance = .wildcard)
    (frameBorrow : argumentFrame.extra.borrowTracker = some owned)
    (storageEq : destinationInput.entry = {reference.entry with allocation := reference.entry.allocation.setExtra destinationInput.entry.allocation.extra})
    (countPositive : (0 : UInt64) < count) (within : count ≤ len/2) :
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
  change sourceEntry.allocation.extra.nodes.size+8 < 65536 at nodeReserve
  change tracker.global.nextPointerTag.value.toNat+7 < 18446744073709551615 at tagReserve
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
  have countNonzero : count ≠ 0 := by intro zero;rw [zero] at countPositive;exact UInt64.lt_irrefl 0 countPositive
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
  have nodes : sourceEntry.allocation.extra.nodes.size+2 < 65536 := by omega
  have nodeRoom : sourceEntry.allocation.extra.nodes.size+2 ≤ 4294967295 := by omega
  have tagRoom : tracker.global.nextPointerTag.value.toNat+1 < 18446744073709551615 := by omega
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
  have slot15 : frame.locals[15]? = some ⟨.dead,none⟩ := by rw [shape.keep 15 (by decide)];exact slots ⟨15,by decide⟩
  have slot16 : frame.locals[16]? = some ⟨.dead,none⟩ := by rw [shape.keep 16 (by decide)];exact slots ⟨16,by decide⟩
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
  obtain ⟨guard,post,guardTree,held,child,acceptedTrace,locationAfter,sizeAfter,bodyAfter,identityAfter,
    calleeAfter,extraAfter,placeAfter,continuationAfter,varargsAfter,localsIdentityAfter,trackAfter,
    zeroAfter,sourceAfter,countAfter,flagAfter,slot15After,slot16After,highAfter,allAfter,
    memoryAfter,trackedAfter,modeAfter,runtimeAfter,readAfter,bothAfter,activityAfter,graphAfter,
    ghostAfter,shallowAfter,raceAfter,addressesAfter,typesAfter,extrasAfter,backendAfter,uncheckedAfter,noGcAfter,
    fixedAfter,finalThread,finalActive,finalTop,treeLiteral⟩ :=
    S02SameDestinationAcceptedGuardLedger.complete options limits remaining span
      input.contract.model.preciseOff input.contract.model.implicitOff input.contract.model.debugOff
      input.contract.model.nullComparator (options.place.dynamicFuel-1) (options.limits.validation-1)
      (Nat.sub_add_cancel dynamicPositive).symm (Nat.sub_add_cancel validationPositive).symm
      reference.base reference.offset len reference.id sourceEntry positive nonzero signedFits #[] frame current
      body identity callee located tracker enabled mode tagFresh reference.tracker.global.nextPointerTag
      packet.runtime raw rawTag rawOffset rawLen capacity validSource validDest sourceLive sourceCached
      destLive destUncached noClocks ghost shallow cached live race metadata notConstructed
      shortRoom nodeRoom tagRoom rfl (limits.callDispatch-1) (Nat.sub_add_cancel dispatchPositive).symm
      (DuplicatePrefixCallModel.sourceComparator options remaining span before input.contract.model)
      valid11 lenLive lenUncached backend unchecked noGc fixed
      {input.contract.thread with topUserRelevantFrame := some 0} active topZero
      count countPositive within size
      (congrArg LocalState.value (fromSlot ⟨13,by decide⟩ _ slot13))
      (congrArg LocalState.layout (fromSlot ⟨13,by decide⟩ _ slot13))
      (congrArg LocalState.value (fromSlot ⟨0,by decide⟩ _ slot0))
      (congrArg LocalState.layout (fromSlot ⟨0,by decide⟩ _ slot0))
      (congrArg LocalState.value (fromSlot ⟨7,by decide⟩ _ slot7))
      (congrArg LocalState.layout (fromSlot ⟨7,by decide⟩ _ slot7))
      (congrArg LocalState.value (fromSlot ⟨15,by decide⟩ _ slot15))
      (congrArg LocalState.layout (fromSlot ⟨15,by decide⟩ _ slot15))
      (congrArg LocalState.value (fromSlot ⟨16,by decide⟩ _ slot16))
      (congrArg LocalState.layout (fromSlot ⟨16,by decide⟩ _ slot16))
      (congrArg LocalState.value (fromSlot ⟨8,by decide⟩ _ slot8))
      (congrArg LocalState.layout (fromSlot ⟨8,by decide⟩ _ slot8))
      (congrArg LocalState.value (fromSlot ⟨9,by decide⟩ _ slot9))
      (congrArg LocalState.layout (fromSlot ⟨9,by decide⟩ _ slot9))
      (congrArg LocalState.value (fromSlot ⟨10,by decide⟩ _ slot10))
      (congrArg LocalState.layout (fromSlot ⟨10,by decide⟩ _ slot10))
      immediate bothRaw activityRaw
  obtain ⟨oldNode,oldPresent,oldTag,oldParent,oldHidden,oldTagged⟩ := graphAfter.oldNodes query sourceNode packet.sourcePresent
  have guardSourceTagged : guardTree.indexOfTag raw.parentTag = some raw.parent := by simpa only [rawTag,rawParent,sourceSame] using oldTagged
  have sourcePresent : guardTree.nodeAt raw.parent = some oldNode := by simpa only [rawParent] using oldPresent
  have sourceHidden : oldNode.isExposed = false := oldHidden.trans initialHidden
  have heldTagRoom : held.global.nextPointerTag.value < 18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    have growth := graphAfter.tagCounter
    have bound : held.global.nextPointerTag.value.toNat < 18446744073709551615 := by omega
    simpa using bound
  let mutableRaw : GeneralBorrowRawDefault.Input guardTree held.global := {
    parentTag := raw.parentTag,parent := raw.parent,selected := raw.selected,maximum := raw.maximum,
    offset := reference.offset,len := len,tagged := guardSourceTagged,positive := Classical.choice bothAfter,
    distinct := graphAfter.distinct,order := graphAfter.order,short := graphAfter.short,
    nodeRoom := by have h:=graphAfter.short;omega,tagRoom := heldTagRoom }
  have headroom : guardTree.nodes.size+2 < 65536 := by have growth:=graphAfter.growth;omega
  have tagsRoom : held.global.nextPointerTag.value.toNat+1 < 18446744073709551615 := by have growth:=graphAfter.tagCounter;omega
  have guardCapacity : guardTree.locations.size = sourceEntry.allocation.byteSize := graphAfter.capacity.trans capacity
  have literalEq : guardTree = GeneralBorrowRawSharedToLenLiteralLedger.finalTree sourceEntry.allocation.extra tracker raw.parentTag raw.offset raw.len raw.tagRoom := by
    simpa only [rawTag,rawTag,rawOffset,rawLen] using treeLiteral
  have guardOrder : GeneralBorrowWildcardParentTagOrder.ParentTagOrder guardTree := by
    rw [literalEq]
    exact S02SameDestinationRejectedResultOrder.literal sourceEntry.allocation.extra tracker reference.id packet.runtime raw nodes nodeRoom tagRoom packet.order
  have guardLive : post.memory.live.find? (fun row => row.1 == reference.id) =
      some (reference.id,{sourceEntry with allocation := sourceEntry.allocation.setExtra guardTree}) := by
    rw [memoryAfter];exact MemoryCopyBridge.live_lookup_replaced _ _ _
  have guardCached : post.user.addresses.baseAddr.find? (fun row => row.allocId == reference.id) = some ⟨reference.id,reference.base⟩ := by rw [addressesAfter];exact cached
  have guardMetadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] guard post)).metadata = PreparedReflection.actual.runtime := by
    change post.user.payload.payload.user.types.metadata = _
    rw [typesAfter];exact metadata
  have guardNotConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] guard post)).entries.any (·.value.ty == 4) = false := by
    change post.user.payload.payload.user.types.entries.any (·.value.ty == 4) = _
    rw [typesAfter];exact notConstructed
  have sourceExtras : post.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == reference.id) = some (reference.id,⟨none,#[]⟩) := by
    rw [extrasAfter,tickExtras,rawUser,rawExtras,←sourceId,physicalId]
    exact input.return_extras
  have currentExtras : currentInput.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == destinationInput.id) = some (destinationInput.id,⟨none,#[]⟩) := by
    change machine.user.payload.payload.user.runtime.extras.allocations.find? _ = _
    rw [rawUser,rawExtras,physicalId];exact input.return_extras
  have oldInitialized : InitMaskCopy.InitializedOn destinationInput.entry.allocation.initializationMask (Size.ofBytes reference.offset) (Size.ofBytes (reference.offset+len)) := by
    rw [storageEq];exact reference.storage.initialized
  have outside : destinationInput.offset.toNat+1 ≤ reference.offset.toNat ∨ (reference.offset+len).toNat ≤ destinationInput.offset.toNat := by
    have stop : (destinationInput.offset+1).toNat = destinationInput.offset.toNat+1 := by
      simp only [UInt64.toNat_add,UInt64.toNat_one];apply Nat.mod_eq_of_lt
      have := destinationInput.bounds;have := destinationInput.capacity.toNat_lt;omega
    simpa only [stop] using sourceDisjoint.symm
  obtain ⟨maskEq,initialized,clearEq⟩ := S02WildcardReturnSameAcceptedPhysical.of_packet limits.retag currentInput modelCurrent place destinationInput
    initialRuntime initialDistinct initialOrder initialRoom fresh wildcard #[] argumentFrame owned frameBorrow #[] currentExtras (by simp)
    reference.tracker.global.nextPointerTag query selected maximum reference.offset len sourceNode packet outside oldInitialized
  obtain ⟨physicalTree,physicalUpdated,protect,_extra,bytes,length,mutable,maskValid,maskLength,_⟩ :=
    S03ReturnWildcardProtectionRawOtherTags.invoke_other_tags limits.retag currentInput modelCurrent place destinationInput initialRuntime initialDistinct initialOrder
      initialRoom fresh wildcard #[] argumentFrame owned frameBorrow #[] currentExtras (by simp)
  have stateEq := (EStateM.Result.ok.inj (protect.symm.trans packet.protect)).2
  have firstLive : (S04ProtectUninit.finished currentInput place destinationInput #[] argumentFrame owned fresh physicalTree physicalUpdated).machine.memory.live.find? (fun row => row.1 == destinationInput.id) = some (destinationInput.id,{destinationInput.entry with allocation := physicalUpdated}) := MemoryCopyBridge.live_lookup_replaced _ _ _
  have secondLive : machine.memory.live.find? (fun row => row.1 == destinationInput.id) = some (destinationInput.id,{destinationInput.entry with allocation := packet.updated}) := MemoryCopyBridge.live_lookup_replaced _ _ _
  have updatedEq : physicalUpdated = packet.updated := by
    rw [stateEq] at firstLive
    exact congrArg (fun row => row.2.allocation) (Option.some.inj (firstLive.symm.trans secondLive))
  rw [updatedEq] at bytes length mutable maskValid maskLength
  have oldStorage := AllocationCopy.set_extra_preserves_storage reference.entry.allocation destinationInput.entry.allocation.extra
  have sizeEq : sourceEntry.allocation.byteSize = reference.entry.allocation.byteSize := by rw [bytes,storageEq];exact oldStorage.1
  have lenEq : sourceEntry.allocation.len = reference.entry.allocation.len := by rw [length,storageEq];exact oldStorage.2.1
  have storage : sourceEntry.allocation.len = sourceEntry.allocation.byteSize.bytes.toNat := by rw [lenEq,sizeEq,reference.bytes,reference.size];rfl
  have storageFits : sourceEntry.allocation.len+64 < 18446744073709551616 := by
    rw [lenEq]
    have member := Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some reference.live)
    exact input.contract.resources.storageRoom (reference.id,reference.entry) member
  have cleared : ProvenanceMap.clear (allocRange (Size.ofBytes destinationInput.offset) (Size.ofBytes 1)) (AllocationCopy.snapshot reference.entry.allocation) (Size.ofBytes 8) reference.entry.allocation.provenanceMap = .ok () sourceEntry.allocation.provenanceMap := by
    rw [storageEq] at clearEq
    simpa only [oldStorage.2.2.2.1,oldStorage.2.2.2.2.2.2] using clearEq
  change sourceEntry.allocation.initializationMask.len = destinationInput.entry.allocation.initializationMask.len at maskLength
  rw [storageEq] at maskLength
  change sourceEntry.allocation.initializationMask.len = reference.entry.allocation.initializationMask.len at maskLength
  have bounds : reference.offset.toNat+len.toNat ≤ sourceEntry.allocation.byteSize.bytes.toNat := by rw [sizeEq,reference.size];exact reference.storage.bounds
  have snapshotLen : (AllocationCopy.snapshot reference.entry.allocation).size = reference.entry.allocation.len := by
    cases reference.entry.allocation
    simp [AllocationCopy.snapshot,Allocation.inspectWithUninitAndPtrOutsideInterpreter,Allocation.len,Pure.pure,Except.pure,Except.toOption,Option.getD]
  have initialFits : reference.entry.allocation.len < 2^64 := by rw [reference.bytes];exact reference.capacity.toNat_lt
  have returnFits : destinationInput.offset.toNat+1 < 2^64 := by have := destinationInput.bounds;have := destinationInput.capacity.toNat_lt;omega
  have endpoint := DuplicatePrefix.source_end (Size.ofBytes destinationInput.offset) 1 (by simpa only [Size.ofBytes,UInt64.toNat_one] using returnFits)
  have direct := S02SameDestinationUninitProvenanceResult.after_clear reference.entry.allocation.provenanceMap sourceEntry.allocation.provenanceMap
    (allocRange (Size.ofBytes destinationInput.offset) (Size.ofBytes 1)) (Size.ofBytes (destinationInput.offset+1))
    (AllocationCopy.snapshot reference.entry.allocation) (by simpa only [snapshotLen] using reference.provenanceMap)
    (by change (1 : UInt64) ≠ 0;decide) endpoint (by simpa only [snapshotLen] using initialFits) cleared
  have currentDirect : S02SameDestinationUninitProvenanceInput.DirectInput sourceEntry.allocation.provenanceMap sourceEntry.allocation.len := by simpa only [snapshotLen,←lenEq] using direct
  have sourceMaskLen : sourceEntry.allocation.initializationMask.len = sourceEntry.allocation.byteSize :=
    maskLength.trans (reference.storage.maskLength.trans (reference.size.symm.trans sizeEq.symm))
  have sumFits : reference.offset.toNat+len.toNat < 2^64 := by have := sourceEntry.allocation.byteSize.bytes.toNat_lt;omega
  have countLe : count.toNat ≤ len.toNat := by
    have h := UInt64.le_iff_toNat_le.mp within
    rw [UInt64.toNat_div] at h
    have := Nat.div_le_self len.toNat 2
    simpa only [show (2 : UInt64).toNat=2 from rfl] using Nat.le_trans h this
  have countEnd : (reference.offset+count).toNat ≤ (reference.offset+len).toNat := by
    simp only [UInt64.toNat_add,Nat.mod_eq_of_lt sumFits,Nat.mod_eq_of_lt (show reference.offset.toNat+count.toNat<2^64 by omega)]
    omega
  have sourceInitialized := S02SameDestinationAcceptedResultJoin.initialized_subrange sourceEntry.allocation.initializationMask
    (Size.ofBytes reference.offset) (Size.ofBytes (reference.offset+len)) (Size.ofBytes (reference.offset+count)) initialized countEnd
  let buffer : LocalAllocation Provenance BorrowTree MiriMemoryKind := {sourceEntry with allocation := sourceEntry.allocation.setExtra guardTree}
  have valid1 : 1 < guard.locals.size := by rw [sizeAfter];decide
  have valid15 : 15 < guard.locals.size := by rw [sizeAfter];decide
  have valid16 : 16 < guard.locals.size := by rw [sizeAfter];decide
  have guardSource : guard.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue (config options (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete reference.id mutableRaw.parentTag) (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm) := by
    have old := congrArg LocalState.value (Option.some.inj ((Array.getElem?_eq_getElem valid1).symm.trans (sourceAfter.trans sourceCell)))
    dsimp only [adjusted] at old
    simpa only [mutableRaw,rawTag,CanonicalConfigFacts.actual_access_runtime] using old
  have guardSourceCache : guard.locals[1].layout = some ActualReferenceMetadata.reference :=
    congrArg LocalState.layout (Option.some.inj ((Array.getElem?_eq_getElem valid1).symm.trans (sourceAfter.trans sourceCell)))
  have guardCell15 := Option.some.inj ((Array.getElem?_eq_getElem valid15).symm.trans slot15After)
  have guardCell16 := Option.some.inj ((Array.getElem?_eq_getElem valid16).symm.trans slot16After)
  have guardTrack : guard.trackCallerArg = none := by rw [trackAfter,shape.track,frameLiteral];rfl
  have relevant : guard.extra.userRelevance > 0 := by
    rw [extraAfter,shape.extra,frameLiteral,PositiveRootInstalledFrame.relevance,PositiveRootInstalledFrame.raw_relevance]
    decide
  have guardClocks : guard.extra.dataRace = none := by rw [extraAfter];exact noClocks
  have guardMode : held.retagMode = .Default := modeAfter.trans mode
  have high : ∀ index,17≤index→index≤24→guard.locals[index]?=some ⟨.dead,none⟩ := by
    intro index lo hi
    rw [highAfter index lo,shape.keep index (by omega),frameLiteral]
    simpa only [show ¬(14=index ∨ 13=index ∨ 6=index ∨ 0=index) from by omega,
      show 2≠index from by omega,show 1≠index from by omega,ite_false] using slots ⟨index,by omega⟩
  have guardSlot2 : guard.locals[2]?=some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩ := by
    rw [countAfter,shape.slot2,frameLiteral];exact slots ⟨2,by decide⟩
  have guardSlot0 : guard.locals[0]?=some ⟨.live (.immediate .uninit),none⟩ := zeroAfter.trans slot0
  have limitPositive : 0 < limits.validation := by have h:=input.contract.resources.executionFuel.2.2.2;unfold work at h;omega
  obtain ⟨ctx⟩ := ActualReferenceContext.exists_context options remaining span input.contract.model.preciseOff input.contract.model.implicitOff
  obtain ⟨copyPacket,copied,done,finalMachine,protectedEq,counterGrowth,sourceMetadata,copyTrace,ready,
    copyMemory,copyLive,copySize,copyLen,copyRuntime,copyPositive,copyActivity,copyTracked,copyAddresses,copyExtras,
    copyBackend,copyGhost,copyShallow,copyRace,copyFixed,copyUnchecked,copyNoGc,connection,physical,copyThread⟩ :=
    S02SameDestinationAcceptedSourceLedger.invoke options limits remaining span ctx input.contract.model.debugOff input.contract.model.nullComparator
      (options.place.dynamicFuel-1) (options.limits.validation-1) (Nat.sub_add_cancel dynamicPositive).symm (Nat.sub_add_cancel validationPositive).symm
      reference.id buffer reference.base reference.offset len raw.parentTag positive nonzero signedFits bounds guard post held trackedAfter guardMode
      mutableRaw.tagRoom runtimeAfter mutableRaw rfl rfl rfl guardCapacity valid15 (congrArg LocalState.value guardCell15) (congrArg LocalState.layout guardCell15)
      guardClocks ghostAfter shallowAfter guardCached guardLive raceAfter guardMetadata guardNotConstructed finalThread finalActive headroom tagsRoom
      input.contract.model.preciseOff input.contract.model.implicitOff (DuplicatePrefixCallModel.sourceComparator options remaining span before input.contract.model)
      (limits.callDispatch-1) (Nat.sub_add_cancel dispatchPositive).symm backendAfter uncheckedAfter noGcAfter fixedAfter finalTop sizeAfter
      (bodyAfter.trans body) (identityAfter.trans identity) (calleeAfter.trans callee) guardTrack relevant allAfter locationAfter
      valid16 (congrArg LocalState.value guardCell16) (congrArg LocalState.layout guardCell16) valid1 guardSource guardSourceCache count countPositive within
      guardSlot2 flagAfter high raw.parent activityAfter guardSlot0 (limits.validation-1) (Nat.sub_add_cancel limitPositive).symm
      storage maskValid sourceMaskLen sourceInitialized currentDirect storageFits mutable sourceExtras
      (CanonicalCopyBound.guarded options () (remaining+1) span len count within)
  have childrenDifferent : raw.parent ≠ packet.child := by
    intro same
    change query = packet.child at same
    have oldPresent : packet.updated.extra.nodeAt packet.child = some sourceNode :=
      (congrArg packet.updated.extra.nodeAt same).symm.trans packet.sourcePresent
    have nodeEq : sourceNode = packet.returnNode := Option.some.inj (oldPresent.symm.trans packet.returnPresent)
    exact tagDifferent (packet.returnSame.symm.trans ((congrArg TreeNode.tag nodeEq).symm.trans sourceSame))
  obtain ⟨guardReturnActivity,guardReturnNode,guardReturnPresent,guardReturnSame,guardReturnEdge,guardReturnLeaf,guardReturnHidden⟩ :=
    S02SameDestinationRejectedResultLiteralActivity.preserves sourceEntry.allocation.extra tracker reference.id packet.runtime raw nodes nodeRoom tagRoom
      packet.child packet.returnNode packet.returnPresent packet.leaf packet.hidden (Ne.symm childrenDifferent)
      destinationInput.offset (destinationInput.offset+1) packet.returnActivity
  rw [←literalEq] at guardReturnActivity guardReturnPresent
  have guardReturnTagged : guardTree.indexOfTag destinationInput.tracker.global.nextPointerTag = some packet.child := by
    obtain ⟨node,present,tagEq,parentEq,hiddenEq,tagged⟩ := graphAfter.oldNodes packet.child packet.returnNode packet.returnPresent
    rw [←packet.returnSame];exact tagged
  have disjoint : raw.offset.toNat+raw.len.toNat ≤ destinationInput.offset.toNat ∨ (destinationInput.offset+1).toNat ≤ raw.offset.toNat := by
    have stop : (reference.offset+len).toNat = reference.offset.toNat+len.toNat := by
      rw [UInt64.toNat_add,Nat.mod_eq_of_lt];exact Nat.lt_of_le_of_lt packet.sourcePositive.bounds packet.updated.extra.locations.size.bytes.toNat_lt
    simpa only [rawOffset,rawLen,stop] using sourceDisjoint
  obtain ⟨guardReturnPositive⟩ := S02DisjointSharedLenLiteral.destination sourceEntry.allocation.extra tracker reference.id packet.runtime raw nodes nodeRoom tagRoom
    (some packet.child) (some packet.child) (some destinationInput.tracker.global.nextPointerTag) destinationInput.offset 1 disjoint packet.returnPositive
  rw [←literalEq,←graphAfter.protections] at guardReturnPositive
  have different : packet.child ≠ raw.parent := Ne.symm childrenDifferent
  obtain ⟨⟨returnPositive⟩,returnActivity,⟨returnNode,returnPresent,returnSame,returnEdge,returnLeaf,returnHidden⟩,currentOrder,currentTags,currentCapacity⟩ :=
    S02SameDestinationAcceptedCopyDestination.current buffer post reference.id reference.base reference.offset len count held runtimeAfter mutableRaw
      headroom tagsRoom guardOrder copyPacket copied connection packet.child packet.child (some destinationInput.tracker.global.nextPointerTag) destinationInput.offset 1
      (by simpa only [mutableRaw,rawOffset,rawLen] using disjoint) guardReturnPositive
      guardReturnNode guardReturnPresent guardReturnLeaf guardReturnHidden different guardReturnActivity
  have finalAddresses : finalMachine.user.addresses = machine.user.addresses := by rw [copyAddresses,addressesAfter];exact tickAddresses
  let original := packet.physical
  have copiedSize : copied.byteSize = original.entry.allocation.byteSize := by
    change copied.byteSize = packet.physical.entry.allocation.byteSize
    rw [packet.physicalEntry];exact copySize
  have copiedLen : copied.len = original.entry.allocation.len := by
    change copied.len = packet.physical.entry.allocation.len
    rw [packet.physicalEntry];exact copyLen
  let destination : S04FinalReturnWildcardInput.Destination finalMachine place := {
    pointer := original.pointer,physicalPointer := original.physicalPointer,layout := original.layout,aligned := original.aligned,
    id := original.id,entry := ⟨original.entry.kind,copied⟩,base := original.base,offset := original.offset,capacity := original.capacity,
    live := by rw [packet.physicalId,packet.physicalEntry,sourceId];exact copyLive,
    cachedBase := by rw [finalAddresses];exact original.cachedBase,
    pointerAddress := original.pointerAddress,nonnull := original.nonnull,addressFits := original.addressFits,bounds := original.bounds,
    size := copiedSize.trans original.size,
    bytes := copiedLen.trans original.bytes,
    mutable := physical.mutable,maskValid := physical.maskValid,
    maskLength := physical.maskLength.trans (copiedSize.trans original.size),
    pointerBounds := physical.pointerBounds,
    borrowSize := by
      change copied.extra.locations.size.bytes = original.capacity
      have oldBorrow := original.borrowSize
      rw [packet.physicalEntry] at oldBorrow
      exact (congrArg (fun value : Size => value.bytes) (currentCapacity.trans graphAfter.capacity)).trans oldBorrow,
    wildcard := original.wildcard,mode := by rw [finalAddresses];exact original.mode,
    exposed := by rw [finalAddresses];exact original.exposed,geometry := by rw [finalAddresses,copiedSize];exact original.geometry }
  have offsetEq : destination.offset = destinationInput.offset := packet.physicalOffset
  have guardExposed : GeneralBorrowFreshRootSupportCutoff.ExposedBound guardTree destinationInput.tracker.global.nextPointerTag := by
    rw [literalEq]
    exact S02WildcardReturnSameRejectedBody.literal_exposed sourceEntry.allocation.extra tracker packet.runtime raw nodes nodeRoom tagRoom _ packet.exposed
  obtain ⟨finalExposed,copyRoots⟩ := mutable_metadata buffer post reference.id reference.base reference.offset len count held runtimeAfter mutableRaw headroom tagsRoom copyPacket copied connection _ guardExposed
  have finalNotPrimary : ∀ valid : 0<copied.extra.roots.size,copied.extra.roots[0]≠packet.child := by
    intro valid
    have roots : copied.extra.roots = sourceEntry.allocation.extra.roots := copyRoots.trans graphAfter.roots
    have oldValid : 0<sourceEntry.allocation.extra.roots.size := by simpa only [roots] using valid
    simpa only [roots] using packet.notPrimary oldValid
  obtain ⟨sourceNode,sourceNodePresent,sourceNodeTag,sourceNodeExposure⟩ := sourceMetadata.oldNode oldNode sourcePresent
  have copiedHidden : sourceNode.isExposed = false := sourceNodeExposure.trans sourceHidden
  have copiedTagged : copied.extra.indexOfTag raw.parentTag = some raw.parent := by
    apply sourceMetadata.tagged oldNode sourcePresent
    exact (oldTag.trans sourceSame).trans rawTag.symm
  have sourceOwned : borrowFrame.protectedTags = #[(destination.id,raw.parentTag),(destination.id,destinationInput.tracker.global.nextPointerTag)] := by
    change borrowFrame.protectedTags = #[(packet.physical.id,raw.parentTag),(packet.physical.id,destinationInput.tracker.global.nextPointerTag)]
    rw [packet.physicalId]
    dsimp only [borrowFrame]
    rw [ownedEq]
    change #[(reference.id,reference.tracker.global.nextPointerTag),(destinationInput.id,destinationInput.tracker.global.nextPointerTag)] = #[(destinationInput.id,reference.tracker.global.nextPointerTag),(destinationInput.id,destinationInput.tracker.global.nextPointerTag)]
    simp only [sourceId]
  have currentReturnTagged := currentTags destinationInput.tracker.global.nextPointerTag packet.child guardReturnTagged
  have hiddenFrame := S02SameDestinationHiddenFrame.of_hidden copied.extra (GeneralBorrowRawAsMutToCopy.held copyPacket).global borrowFrame
    destination.id destination.id raw.parentTag destinationInput.tracker.global.nextPointerTag packet.child returnNode sourceOwned copyRuntime raw.parent sourceNode
    copiedTagged sourceNodePresent copiedHidden currentReturnTagged returnPresent returnHidden
  obtain ⟨sourcePositive⟩ := copyPositive
  have afterSourceActivity := S02HiddenLeafActiveRelease.release copied.extra (GeneralBorrowRawAsMutToCopy.held copyPacket).global copyRuntime raw.parentTag
    raw.parent copyPacket.selected copyPacket.maximum reference.offset len sourcePositive sourceNode sourceNodePresent copiedHidden copiedTagged
    sourceMetadata.distinct (fun _ _ => currentOrder) sourceMetadata.short copyActivity packet.child returnNode returnPresent returnLeaf returnHidden
    different destinationInput.offset (destinationInput.offset+1) returnActivity
  have frameTracked : done.extra.borrowTracker = some borrowFrame := by rw [ready.extra,extraAfter,shape.extra];exact packetTracked
  have donePlace : done.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩ := by
    rw [ready.destination,placeAfter,shape.returnPlace,frameLiteral,frameMetadata.2.2.2.2.1];rfl
  have doneClocks : done.extra.dataRace = none := by rw [ready.extra];exact guardClocks
  have valid0 : (0 : MIR.LocalId) < done.locals.size := by rw [ready.size];decide
  have cell0 := Option.some.inj ((Array.getElem?_eq_getElem valid0).symm.trans ready.output)
  have finalExtras : finalMachine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == destination.id) = some (destination.id,⟨none,#[]⟩) := by
    change finalMachine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == packet.physical.id) = some (packet.physical.id,⟨none,#[]⟩)
    rw [packet.physicalId,copyExtras,sourceId];exact sourceExtras
  let copyActiveThread := Classical.choose copyThread
  have copyActive : finalMachine.threads.activeThread? = some copyActiveThread := Classical.choose_spec copyThread
  obtain ⟨updated,returnStep,_,_,_⟩ := S02WildcardReturnSameStep.step options limits remaining span done finalMachine
    (GeneralBorrowRawAsMutToCopy.held copyPacket) borrowFrame copyTracked frameTracked place destination raw.parentTag raw.parent
    copyPacket.selected copyPacket.maximum reference.offset len sourceNode copiedTagged sourceNodePresent copiedHidden sourcePositive copyActivity
    destinationInput.tracker.global.nextPointerTag packet.child returnNode currentReturnTagged returnPresent (returnSame.trans (guardReturnSame.trans packet.returnSame))
    (returnEdge.trans (guardReturnEdge.trans packet.parentless)) returnLeaf returnHidden sourceOwned hiddenFrame copyRuntime (by simpa only [offsetEq] using returnPositive)
    sourceMetadata.distinct currentOrder finalExposed finalNotPrimary sourceMetadata.short
    (by change (reference.offset+len).toNat ≤ packet.physical.offset.toNat ∨ (packet.physical.offset+1).toNat ≤ reference.offset.toNat
        rw [packet.physicalOffset];exact sourceDisjoint) (by simpa only [offsetEq] using afterSourceActivity) copyActiveThread copyActive copyRace copyBackend copyGhost copyShallow
    #[] finalExtras (by simp) true (options.limits.validation-1) input.contract.model.debugOff (Nat.sub_add_cancel validationPositive).symm
    (ready.body.trans (bodyAfter.trans body)) ready.location valid0 (congrArg LocalState.value cell0) (congrArg LocalState.layout cell0) doneClocks donePlace
    (by rw [ready.continuation,continuationAfter,shape.continuation,frameLiteral];exact frameMetadata.2.2.2.1) ready.immediate
    (by rw [ready.varargs,varargsAfter,shape.vaList,frameLiteral,frameMetadata.2.2.2.2.2.1];rfl) copyUnchecked copyNoGc copyFixed
  let accounted := S04FinalReturnRuleAccounting.machine options remaining span done finalMachine
  let sourceReleased := (copied.extra.releaseProtector raw.parentTag (GeneralBorrowRawAsMutToCopy.held copyPacket).global.protectedTags).tree
  let priorMemory := StackPopRelease.commitTree accounted.memory destination.id destination.entry sourceReleased
  let released := (sourceReleased.releaseProtector destinationInput.tracker.global.nextPointerTag (GeneralBorrowRawAsMutToCopy.held copyPacket).global.protectedTags).tree
  let after := S04FinalReturnVariantsInput.afterPop #[] done accounted (GeneralBorrowRawAsMutToCopy.held copyPacket) borrowFrame
    priorMemory destination.id destination.entry released (copyActiveThread.topUserRelevantFrame.getD 0)
  let finished := CanonicalCopy.replaceAllocation after destination.id destination.entry.kind updated
  have last : ExecutionMachine.step (config options (remaining+1) span) limits () (Storage.withCurrent #[] done finalMachine) = (finished,.ok true) := returnStep
  have trace := SuccessfulTrace.append (SuccessfulTrace.append prefixTrace acceptedTrace) (SuccessfulTrace.append copyTrace (.next last (.refl _)))
  let safety : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit := ⟨config options (remaining+1) span,limits,fun _ _ => True⟩
  have entered : CallSafety.IsCallEntry 1 (Storage.withCurrent #[] entry machine) := by simp [CallSafety.IsCallEntry,CallSafety.frameDepth,Storage.withCurrent]
  have exited : CallSafety.pastCallBoundary 1 finished := by change (0:Nat)<1;decide
  have terminal : ExecutionMachine.step (config options (remaining+1) span) limits () finished = (finished,.ok false) := rfl
  exact ⟨Storage.withCurrent #[] entry machine,finished,actual,trace,terminal,rfl,
    SuccessfulTrace.no_errors safety 1 _ _ entered trace exited,SuccessfulTrace.no_ub safety 1 _ _ entered trace exited,
    SuccessfulTraceTerminal.prefix_step_success trace terminal⟩

end
end DuplicatePrefix.S02WildcardReturnSameAcceptedBody
