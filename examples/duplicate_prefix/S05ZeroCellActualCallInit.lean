import duplicate_prefix.S05ZeroCellActualCallParameters
import duplicate_prefix.GenericAsMutPtrArgumentCopy
import duplicate_prefix.RawRootInvocation
import duplicate_prefix.ScopedFrame
import duplicate_prefix.PositiveRootArgumentProperties
import duplicate_prefix.RootEntryTail
import duplicate_prefix.ProtectorInsertion
import duplicate_prefix.StackPopRelease
import Init.Internal.Order.While

/-! Exact initialization of one closed len=2/count=1 call. The metadata-span
and null-comparison conditions are explicit. All machine data are retained;
only the actual six-node Read/child operation is computed locally. The final
existential allocation is derived from the actual bool-destination component.
No Contract, operation-success premise, execution suffix or NoUB claim is added. -/

namespace DuplicatePrefix.S05ZeroCellActualCallInit.PureTree
open Miri Miri.ABI Miri.Memory Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open S05ZeroCellTypedGeneratedPrefix
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option cbv.maxSteps 1000000
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

def raw : BorrowTree := S05ZeroCellJointPacket.sourceEntry.allocation.extra
def held : ProtectedTags := ({} : ProtectedTags).insert (tag 8) .StrongProtector
def read := raw.performBorrowAccessRange (.concrete (tag 6)) Size.ZERO
  (Size.ofBytes 2) .Read held .VisitChildrenOfAccessed
def child := read.tree.newChild Size.ZERO (.concrete (tag 6)) (tag 8)
  (DedupRangeMap.new (Size.ofBytes 2) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true

theorem read_complete : read.status = .Completed := by cbv

theorem child_complete : child.outcome = .ok () := by cbv

end DuplicatePrefix.S05ZeroCellActualCallInit.PureTree


namespace DuplicatePrefix.S05ZeroCellActualCallInit
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts RootFrameData EmptyRootArguments ActualReferenceContext PositiveRootArguments
open S05ZeroCellActualCallParameters S05ZeroCellJointPacket
open S05ZeroCellTypedGeneratedPrefix (tag)
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

private def global : GlobalState :=
  {nextPointerTag := tag 8,rootPointerTags := #[(sourceId,tag 1),(destinationId,tag 7)]}
private def tracker (mode : RetagPolicy.RetagMode) : MachineHooks.BorrowState := ⟨global,mode⟩
private theorem fresh : global.nextPointerTag.value < 18446744073709551615 := by decide +kernel
private theorem debug : options.place.debugAssertions = false := rfl
private theorem dynamic : options.place.dynamicFuel = remaining+1 := rfl
private theorem validation : options.limits.validation = remaining+1 := rfl

/-- Local composition for this raw generated tree. The entire machine remains
an abstract variable; only live, address and profile fields are read. -/
private theorem copy_argument (span : PreparedContracts.FixedSpanQuery)
    (ctx : Context options remaining span) (cmp : ProjectionMetadataFacts.NullComparator)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (enabled : machine.borrowTracker = some (tracker .FnEntry))
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (valid : 1 < frame.locals.size) (old : Immediate Provenance)
    (live : frame.locals[1].value = .live (.immediate old))
    (cached : frame.locals[1].layout = some ActualReferenceMetadata.reference)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == sourceId) = some ⟨sourceId,4096⟩)
    (present : machine.memory.live.find? (fun row => row.1 == sourceId) = some (sourceId,sourceEntry))
    (race : machine.dataRace = none)
    (metadata : machine.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (notConstructed : machine.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false) :
    let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      sourcePointer 2 ActualReferenceMetadata.reference).imm
    let copied := GenericAsMutPtrArgumentCopy.copiedFrame frame 1 value valid
    let changed := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine machine (tracker .FnEntry) fresh)
      (ReferenceBorrowDriver.allocatedTracker (tracker .FnEntry) fresh) (tag 8) with
      memory := RetagEntry.updatedMemory machine.memory sourceId sourceEntry PureTree.child.tree}
    (ExecutionMachine.callHooks (config options (remaining+1) span) limits).copyAllowTransmute ()
      ⟨.immediate value,ActualReferenceMetadata.reference⟩
      (LocalPlaces.localRuntimePlace frames.size frame 1 ActualReferenceMetadata.reference).stackView
      (Storage.withCurrent frames frame machine) =
    .ok () (Storage.withCurrent frames
      {(TypedBorrowSteps.registeredFrame copied borrowFrame sourceId (tag 8)) with
        locals := copied.locals.set 1
          {value := .live (.immediate (RetagReferencePlace.sliceValue
            (config options remaining span).access.runtime.base
            (Pointer.new (.concrete sourceId (tag 8)) (Size.ofBytes 4096)) 2 ActualReferenceMetadata.reference).imm),
           layout := (copied.locals[1]'(by simpa [copied,GenericAsMutPtrArgumentCopy.copiedFrame] using valid)).layout}
          (by simpa [copied,GenericAsMutPtrArgumentCopy.copiedFrame] using valid)} changed) := by
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    sourcePointer 2 ActualReferenceMetadata.reference).imm
  let copied := GenericAsMutPtrArgumentCopy.copiedFrame frame 1 value valid
  have postValid : 1 < copied.locals.size := by simpa [copied,GenericAsMutPtrArgumentCopy.copiedFrame] using valid
  have postLive : copied.locals[1].value = .live (.immediate value) := by simp [copied,GenericAsMutPtrArgumentCopy.copiedFrame]
  have postCached : copied.locals[1].layout = some ActualReferenceMetadata.reference := by
    simpa only [copied,GenericAsMutPtrArgumentCopy.copiedFrame,Array.getElem_set_self] using cached
  have info := RootReferenceInfo.facts options remaining span ctx false
  have readDone : (sourceEntry.allocation.extra.performBorrowAccessRange (.concrete (tag 6))
      (Size.ofBytes 0) (Size.ofBytes 2) .Read
      (TypedBorrowSteps.registeredGlobal (tracker .FnEntry) (tag 8)).protectedTags .VisitChildrenOfAccessed).status = .Completed :=
    PureTree.read_complete
  have childDone : PureTree.read.tree.newChild (Size.ofBytes 0) (.concrete (tag 6)) (tag 8)
      (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes 2) GeneralBorrowFreshChild.inside)
      ChildBorrow.fnEntryPolicy.outsidePermission true = ⟨PureTree.child.tree,.ok ()⟩ :=
    GeneralBorrowFreshReborrowStages.child_complete PureTree.child PureTree.child_complete
  have checked := ProtectedReferenceValidator.positive options remaining span ctx debug cmp remaining remaining dynamic
    ActualReferenceMetadata.reference .Mut .FnEntry ChildBorrow.fnEntryPolicy GeneralBorrowFreshChild.inside
    rfl (by decide +kernel) (ChildBorrow.mutable_fn_entry_initial_location true) (by decide +kernel)
    info.shape info.pointeeQuery info.unpin info.unsafeUnpin info.frozen info.dereference
    info.sized info.readable "&mut [u8]" info.named info.classified
    sourceId sourceEntry 4096 0 2 (tag 6) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) frames copied machine (tracker .FnEntry) enabled rfl borrowFrame frameBorrow fresh
    1 postValid postLive postCached ghost shallow cachedAddress present race PureTree.read.tree PureTree.child.tree
    rfl readDone childDone metadata notConstructed
  apply ReferenceArgumentCopy.copy_with_nested_validation options limits remaining span debug frames frame machine
    1 old value valid live cached noClocks ghost shallow
    (LocalPlaces.localRuntimePlace frames.size frame 1 ActualReferenceMetadata.reference).stackView (by simp) _
  rw [validation]
  exact checked

/-- Frame data after the two actual argument passes, before destination setup. -/
def argumentFrame (span : PreparedContracts.FixedSpanQuery) : RootFrame :=
  let raw := RawRootInvocation.root before place profile.2.2.2.1
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete sourceId (tag 8)) (Size.ofBytes 4096)) 2 ActualReferenceMetadata.reference).imm
  RootArgumentsTwo.result (PositiveRootArguments.firstDone raw adjusted {} sourceId (tag 8)) 1

def argumentMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser :=
  let raw := RawRootInvocation.machine #[] before
  {raw with
    memory := RetagEntry.updatedMemory raw.memory sourceId sourceEntry PureTree.child.tree
    borrowTracker := some ⟨TypedRetagGeneric.protectedGlobal global fresh,.Default⟩}

/-- Explicit installed state. `updated` is the allocation returned by the
existing actual bool-destination protection/uninitialization component, rather
than a quoted state or a replacement interpreter operation. -/
def installed (span : PreparedContracts.FixedSpanQuery) (updated : Allocation Provenance BorrowTree) : RootState :=
  let next : MachineHooks.BorrowState := ⟨TypedRetagGeneric.protectedGlobal global fresh,.Default⟩
  let owned := ({} : FrameState).addProtector sourceId (tag 8)
  let changed := {(argumentFrame span).frame with location := FrameLocation.unwinding ⟨601⟩}
  let borrowed := ReturnProtection.borrowedState #[] changed owned argumentMachine next (by decide +kernel)
    destinationId destinationEntry (PhysicalMachineWrite.slotTree (tag 7) next.global.nextPointerTag 1 false)
  Storage.withCurrent #[]
    (CallEntryFacts.doneRootFrame {TypedBorrowSteps.registeredFrame changed owned destinationId next.global.nextPointerTag with location := .unwinding ⟨559⟩})
    (CanonicalCopy.replaceAllocation borrowed destinationId destinationEntry.kind updated).machine

/-- This exact closed call initializes normally. Only independent metadata
comparison/span facts remain explicit; no Contract or access-success premise is
assumed. The returned state is the source-composed installed frame. -/
theorem init_ok_with_slot (span : PreparedContracts.FixedSpanQuery) (cmp : ProjectionMetadataFacts.NullComparator) :
    ∃ updated : Allocation Provenance BorrowTree,
      initializationResult span = .ok () (installed span updated) ∧ (installed span updated).stack.frames.size = 1 ∧
      updated.extra = PhysicalMachineWrite.slotTree (tag 7) (tag 9) 1 true ∧
      updated.byteSize = Size.ofBytes 1 ∧ updated.len = 1 ∧
      updated.initializationMask = InitMask.new (Size.ofBytes 1) false ∧
      updated.provenanceMap = ProvenanceMap.new ∧
      AllocationCopy.snapshot updated = AllocationCopy.snapshot destinationEntry.allocation ∧
      updated.mutability = .Mut := by
  obtain ⟨ctx⟩ := ActualReferenceContext.exists_context options remaining span rfl rfl
  obtain ⟨retagCtx⟩ := ActualRetagContext.exists_context options (remaining+1) span rfl rfl
  obtain ⟨ghostBefore,shallowBefore,alignmentBefore,raceBefore,backendBefore,fixedBefore,uncheckedBefore,gcBefore⟩ := profile
  let root := RawRootInvocation.root before place raceBefore
  let machine := RawRootInvocation.machine #[] before
  obtain ⟨memoryEq,trackedEq,raceEq,addressesEq,ghostEq,validationEq,typesEq,backendEq,extrasEq⟩ :=
    RawRootInvocation.preservation #[] before
  have tracked : machine.borrowTracker = some (tracker .Default) := trackedEq.trans rfl
  have frameBorrow : root.frame.extra.borrowTracker = some ({} : FrameState) :=
    RawRootInvocation.frame_borrow before place raceBefore (tracker .Default) (by rfl)
  have srcLive : machine.memory.live.find? (fun row => row.1 == sourceId) = some (sourceId,sourceEntry) := by rw [memoryEq]; exact source_present
  have srcCached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == sourceId) = some ⟨sourceId,4096⟩ := by rw [addressesEq]; exact source_cached
  have slotLive : machine.memory.live.find? (fun row => row.1 == destinationId) = some (destinationId,destinationEntry) := by rw [memoryEq]; exact destination_present
  have slotCached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == destinationId) = some ⟨destinationId,8192⟩ := by rw [addressesEq]; exact destination_cached
  have slotExtras : machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == destinationId) = some (destinationId,⟨none,#[]⟩) := by rw [extrasEq]; exact destination_extras
  have ghost : machine.user.payload.ghost = false := ghostEq.trans ghostBefore
  have shallow : machine.user.payload.validation = .Shallow := validationEq.trans shallowBefore
  have race : machine.dataRace = none := raceEq.trans raceBefore
  have backend : machine.user.payload.payload.user.backend = .none := backendEq.trans backendBefore
  have metadata : machine.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime := by rw [typesEq]; exact current_metadata
  have notConstructed : machine.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false := by
    rw [typesEq,canonical_types]
    decide +kernel
  have slots (i : Fin 25) : (root.frame.locals[i.val]'(root.valid i)) = ⟨.dead,none⟩ := by
    have rows := congrArg (fun rows : Array (LocalState Provenance LocalLayout) => rows[i.val]?)
      (RawRootInvocation.locals before place raceBefore)
    have row : root.frame.locals[i.val]? = some (⟨.dead,none⟩ : LocalState Provenance LocalLayout) := by
      simpa only [Array.getElem?_replicate,i.isLt,↓reduceIte] using rows
    exact Option.some.inj ((Array.getElem?_eq_getElem (root.valid i)).symm.trans row)
  let l1 := firstLive root
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base sourcePointer 2 ActualReferenceMetadata.reference).imm
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete sourceId (tag 8)) (Size.ofBytes 4096)) 2 ActualReferenceMetadata.reference).imm
  let d1 := firstDone root adjusted {} sourceId (tag 8)
  let argsFrame := RootArgumentsTwo.result d1 1
  let entered := ScopedFrame.entered machine (tracker .Default) .FnEntry
  let next : MachineHooks.BorrowState := ⟨TypedRetagGeneric.protectedGlobal global fresh,.Default⟩
  let fnMachine := {entered with
    memory := RetagEntry.updatedMemory machine.memory sourceId sourceEntry PureTree.child.tree
    borrowTracker := some ⟨next.global,.FnEntry⟩}
  let argsMachine := {machine with
    memory := RetagEntry.updatedMemory machine.memory sourceId sourceEntry PureTree.child.tree
    borrowTracker := some next}
  have live1 : (l1.frame.locals[1]'(l1.valid i1)).value = .live (.immediate .uninit) := by simp [l1,firstLive,live,write,i1]
  have cached1 : (l1.frame.locals[1]'(l1.valid i1)).layout = some ActualReferenceMetadata.reference := by
    simp [l1,firstLive,firstCache,live,write,cache,LocalOperands.cachedLayoutFrame,i1]
  have copyRaw := copy_argument span ctx cmp #[] l1.frame entered rfl {} frameBorrow
    (l1.valid i1) .uninit live1 cached1 l1.noClocks ghost shallow srcCached srcLive race metadata notConstructed
  have copy1 : (ExecutionMachine.callHooks (config options (remaining+1) span) limits).copyAllowTransmute ()
      ⟨.immediate value,ActualReferenceMetadata.reference⟩
      (LocalPlaces.localRuntimePlace 0 l1.frame 1 ActualReferenceMetadata.reference).stackView
      (Storage.withCurrent #[] l1.frame entered) = .ok () (Storage.withCurrent #[] d1.frame fnMachine) := by
    simpa [value,adjusted,d1,fnMachine,l1,next,tracker,global,entered,ScopedFrame.entered,GenericAsMutPtrArgumentCopy.copiedFrame,
      PositiveRootArguments.firstDone,protectedRoot,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,
      TypedBorrowSteps.registeredMachine,TypedBorrowSteps.registeredTracker,TypedBorrowSteps.registeredGlobal,
      ReferenceBorrowDriver.allocatedMachine,ReferenceBorrowDriver.allocatedTracker,TypedRetagGeneric.protectedGlobal,
      TypedRetagGeneric.allocatedGlobal,firstLive,firstCache,live,write,cache,LocalOperands.cachedLayoutFrame,atSpan,i1,i2,root.size] using copyRaw
  have dead1 : (root.frame.locals[1]'(root.valid i1)).value = .dead := congrArg LocalState.value (slots i1)
  have cache1 : (root.frame.locals[1]'(root.valid i1)).layout = none := congrArg LocalState.layout (slots i1)
  have dead2 : (d1.frame.locals[2]'(d1.valid i2)).value = .dead := by
    simpa [d1,PositiveRootArguments.firstDone,protectedRoot,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,
      firstLive,firstCache,live,write,cache,LocalOperands.cachedLayoutFrame,atSpan,i1,i2,root.size] using congrArg LocalState.value (slots i2)
  have cache2 : (d1.frame.locals[2]'(d1.valid i2)).layout = none := by
    simpa [d1,PositiveRootArguments.firstDone,protectedRoot,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,
      firstLive,firstCache,live,write,cache,LocalOperands.cachedLayoutFrame,atSpan,i1,i2,root.size] using congrArg LocalState.layout (slots i2)
  have body := RootArgumentsTwo.body options limits remaining span debug remaining validation #[] root d1 entered fnMachine value 1
    dead1 cache1 dead2 cache2 ghost shallow ghost shallow copy1
  have scopeResult := ScopedFrame.changed_state
    (RootCallCore.argumentBody (ExecutionMachine.callHooks (config options (remaining+1) span) limits)
      ⟨.immediate value,ActualReferenceMetadata.reference⟩ (second 1))
    (Storage.withCurrent #[] root.frame machine) (Storage.withCurrent #[] argsFrame.frame fnMachine)
    (tracker .Default) ⟨next.global,.FnEntry⟩ .FnEntry (2,2) tracked rfl body
  have arguments : (ExecutionMachine.callHooks (config options (remaining+1) span) limits).withRetagMode () .FnEntry
      (RootCallCore.argumentBody (ExecutionMachine.callHooks (config options (remaining+1) span) limits)
        ⟨.immediate value,ActualReferenceMetadata.reference⟩ (second 1))
      (Storage.withCurrent #[] root.frame machine) = .ok (2,2) (Storage.withCurrent #[] argsFrame.frame argsMachine) := by
    change MachineHooks.withRetagMode .FnEntry
      (RootCallCore.argumentBody (ExecutionMachine.callHooks (config options (remaining+1) span) limits)
        ⟨.immediate value,ActualReferenceMetadata.reference⟩ (second 1))
      (Storage.withCurrent #[] root.frame machine) = _
    simpa [argsMachine,fnMachine,entered,ScopedFrame.entered,tracker,next,Storage.withCurrent] using scopeResult
  let owned := ({} : FrameState).addProtector sourceId (tag 8)
  have slotAfter : argsMachine.memory.live.find? (fun row => row.1 == destinationId) = some (destinationId,destinationEntry) :=
    StackPopRelease.lookup_commit_other machine.memory sourceId destinationId sourceEntry destinationEntry PureTree.child.tree distinct_ids.symm slotLive
  have freeAfter : next.global.protectedTags.contains (tag 7) = false := by decide +kernel
  have untouched (i : Fin 25) (n1 : i.val ≠ 1) (n2 : i.val ≠ 2) :
      (argsFrame.frame.locals[i.val]'(argsFrame.valid i)).value = .dead := by
    rw [PositiveRootArgumentProperties.untouched root adjusted {} sourceId (tag 8) 1 i n1 n2]
    exact congrArg LocalState.value (slots i)
  obtain ⟨updated,tail,props⟩ := RootEntryTail.actual_tail options limits (remaining+1) span retagCtx place rfl
    #[] argsFrame.frame owned argsMachine next rfl rfl (by decide +kernel)
    destinationId destinationEntry 8192 (tag 7) rfl rfl slotCached destination_tree rfl slotAfter race
    (by decide +kernel) freeAfter rfl rfl rfl rfl backend slotExtras ghost argsFrame.body argsFrame.size
    (untouched ⟨0,by decide⟩ (by decide) (by decide))
    (untouched ⟨6,by decide⟩ (by decide) (by decide))
    (untouched ⟨13,by decide⟩ (by decide) (by decide))
    (untouched ⟨14,by decide⟩ (by decide) (by decide))
    argsFrame.noClocks argsFrame.identity argsFrame.callee
  refine ⟨updated,?_,rfl,props⟩
  rw [initializationResult_exact]
  change Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
    RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
    #[.Copy ⟨.immediate value,ActualReferenceMetadata.reference⟩,.Copy (second 1)] false (.memory place) (.stop true)
    ⟨⟨#[]⟩,before⟩ = .ok () (installed span updated)
  rw [RootCallCore.actual_entry_eq]
  let thread : Miri.Concurrency.ThreadRecord :=
    {Miri.Concurrency.ThreadRecord.initial (some [109,97,105,110]) none with
      originSpanToken := PreparedReflection.actual.dummySpan.id}
  have threadActive : before.threads.activeThread? = some thread := rfl
  have push := CallEntryFacts.actual_call_hooks_push_raw options () (remaining+1) span limits debug
    (⟨⟨#[]⟩,before⟩ : RootState) (.memory place) _ threadActive (by rfl)
  have getFrame := CallEntryLocals.get_frame options limits (remaining+1) span #[] root.frame machine
  have setFrame := CallEntryLocals.set_frame options limits (remaining+1) span #[] root.frame root.frame machine
  have control := RawRootInvocation.control before place raceBefore
  have preamble : root.frame.location = .unwinding ⟨559⟩ := control.1
  have unchanged : {root.frame with trackCallerArg := none} = root.frame := by rw [←control.2.1]
  unfold CallEntryFacts.config at push
  unfold RootCallCore.core
  simp only [bind,EStateM.bind]
  rw [push,RawRootInvocation.raw_eq #[] before place raceBefore]
  simp only []
  rw [getFrame]
  simp only [EStateM.bind,preamble,pure,EStateM.pure]
  simp only [preamble] at unchanged
  rw [unchanged,setFrame]
  simp only []
  rw [arguments]
  simp only []
  exact tail

/-- Retained initialization API; the stronger export additionally carries the
actual destination allocation's post-initialization resource facts. -/
theorem init_ok (span : PreparedContracts.FixedSpanQuery) (cmp : ProjectionMetadataFacts.NullComparator) :
    ∃ updated : Allocation Provenance BorrowTree,
      initializationResult span = .ok () (installed span updated) ∧ (installed span updated).stack.frames.size = 1 := by
  obtain ⟨updated,init,depth,_⟩ := init_ok_with_slot span cmp
  exact ⟨updated,init,depth⟩

theorem installed_destination (span : PreparedContracts.FixedSpanQuery) (updated : Allocation Provenance BorrowTree) :
    (installed span updated).machine.memory.live.find? (fun row => row.1 == destinationId) =
      some (destinationId,⟨destinationEntry.kind,updated⟩) := by
  unfold installed
  exact CanonicalCopy.replace_lookup _ _ _ _

/-- Determinism transfers the exact destination resources to any existing
initialization prefix using this same installed-state expression. -/
theorem slot_of_initialization (span : PreparedContracts.FixedSpanQuery)
    (cmp : ProjectionMetadataFacts.NullComparator) (updated : Allocation Provenance BorrowTree)
    (initialization : initializationResult span = .ok () (installed span updated)) :
    updated.extra = PhysicalMachineWrite.slotTree (tag 7) (tag 9) 1 true ∧
    updated.byteSize = Size.ofBytes 1 ∧ updated.len = 1 ∧
    updated.initializationMask = InitMask.new (Size.ofBytes 1) false ∧
    updated.provenanceMap = ProvenanceMap.new ∧
    AllocationCopy.snapshot updated = AllocationCopy.snapshot destinationEntry.allocation ∧
    updated.mutability = .Mut := by
  obtain ⟨other,initialized,_,properties⟩ := init_ok_with_slot span cmp
  have states : installed span updated = installed span other := by
    exact EStateM.Result.ok.inj (initialization.symm.trans initialized) |>.2
  have lookup := congrArg (fun state : RootState => state.machine.memory.live.find? (fun row => row.1 == destinationId)) states
  rw [installed_destination,installed_destination] at lookup
  have same : updated = other := congrArg (fun row : AllocId × LocalAllocation Provenance BorrowTree MiriMemoryKind => row.2.allocation) (Option.some.inj lookup)
  rw [same]
  exact properties

end
end DuplicatePrefix.S05ZeroCellActualCallInit
