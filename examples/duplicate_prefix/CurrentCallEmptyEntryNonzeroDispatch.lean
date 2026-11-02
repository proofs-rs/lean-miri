import duplicate_prefix.CurrentCallEmptyEntryNonzeroDispatchState
import duplicate_prefix.CurrentCallEmptyEntryNonzeroDispatchRuntime
import duplicate_prefix.CurrentCallEmptyEntryNonzeroBody
import duplicate_prefix.CurrentCallEmptyEntryNonzeroBodyNonlive
import duplicate_prefix.CurrentCallEmptyEntryNonzeroBodyMiss
import duplicate_prefix.S03NonliveProtectorLedger
namespace DuplicatePrefix.CurrentCallEmptyEntryNonzeroDispatch
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.TreeBorrows Miri.Interpreter
open RootFrameData EmptyRootArguments TypedBorrowSteps ReferenceBorrowDriver
open CandidateStableCallOwnership CandidateCurrentJointCall CanonicalConfigFacts ActualReferenceContext
open CurrentCallEmptyTypedEntry CurrentCallEmptyEntryBool CurrentCallEmptyEntryFrame
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency true
set_option backward.dsimp.instances false

variable {options limits remaining span before tracker argument place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument 0 place call data}

/-- Exact two-helper heap effect, constructed internally by the live branch. -/
structure LiveHeap (out : CurrentCallEmptyEntryRoot.Output input #[]) (count : UInt64) (post : Before) where
  id : AllocId
  allocation : out.effect.allocation=some id
  entry : LocalAllocation Provenance BorrowTree MiriMemoryKind
  live : (CurrentCallEmptyEntryNonzeroDispatchState.machine out count).memory.live.find? (fun row=>row.1==id)=some (id,entry)
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra (CurrentCallEmptyEntryNonzeroDispatchState.held out).global
  fresh : (CurrentCallEmptyEntryNonzeroDispatchState.held out).global.nextPointerTag.value<18446744073709551615
  room : entry.allocation.extra.nodes.size+2≤4294967295
  first : EmptyForestSharedPool.Input entry.allocation.extra tracker.global.nextPointerTag (CurrentCallEmptyEntryNonzeroDispatchState.held out).global.nextPointerTag
  memory : post.memory=RetagEntry.updatedMemory (CurrentCallEmptyEntryNonzeroDispatchState.machine out count).memory id entry
    (S03EmptyNextLenInput.form entry.allocation.extra (CurrentCallEmptyEntryNonzeroDispatchState.held out).global runtime tracker.global.nextPointerTag first fresh room).after

structure BodyResult (out : CurrentCallEmptyEntryRoot.Output input #[]) (count : UInt64)
    (result : CompilerFrameContext.ActualFrame) (post : Before) : Prop where
  trace : SuccessfulTrace.Trace (config options (remaining+1) span) limits
    (Storage.withCurrent #[] (CurrentCallEmptyEntryNonzeroDispatchState.frame out count) (CurrentCallEmptyEntryNonzeroDispatchState.machine out count)) (Storage.withCurrent #[] result post)
  body : result.body=RootBody.reflected.body.body
  identity : result.bodyIdentity=RootBody.reflected.body.identity
  callee : result.functionInstance=RootBody.reflected.functionInstance
  size : result.locals.size=25
  location : result.location=.mir ⟨10,0⟩
  value : result.locals[0]?=some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩
  destination : result.returnPlace=CurrentCallArguments.destination place
  extra : result.extra=(CurrentCallEmptyEntryNonzeroDispatchState.frame out count).extra
  continuation : result.returnContinuation=(CurrentCallEmptyEntryNonzeroDispatchState.frame out count).returnContinuation
  varargs : result.vaList=(CurrentCallEmptyEntryNonzeroDispatchState.frame out count).vaList
  immediate : CopyHelperCleanup.AllImmediate result
  model : DuplicatePrefixCallModel.Model options remaining span post
  origins : DuplicatePrefixTypeCacheOrigins.Origins post.user.payload.payload.user.types
  ready : CurrentCallBoolProtection.ProfileMemoryReadiness post call
  addresses : post.user.addresses=(CurrentCallEmptyEntryNonzeroDispatchState.machine out count).user.addresses
  types : post.user.payload.payload.user.types=(CurrentCallEmptyEntryNonzeroDispatchState.machine out count).user.payload.payload.user.types
  extras : post.user.payload.payload.user.runtime.extras=(CurrentCallEmptyEntryNonzeroDispatchState.machine out count).user.payload.payload.user.runtime.extras
  active : ∃ thread,post.threads.activeThread?=some thread
  tracked : ∃ current,post.borrowTracker=some current ∧ current.retagMode=(CurrentCallEmptyEntryNonzeroDispatchState.held out).retagMode ∧
    current.global={ (CurrentCallEmptyEntryNonzeroDispatchState.held out).global with nextPointerTag:=current.global.nextPointerTag} ∧
    current.global.protectedTags=(CurrentCallEmptyEntryNonzeroDispatchState.held out).global.protectedTags ∧
    current.global.nextPointerTag.value.toNat=(CurrentCallEmptyEntryNonzeroDispatchState.held out).global.nextPointerTag.value.toNat+2
  heap : post.memory=(CurrentCallEmptyEntryNonzeroDispatchState.machine out count).memory ∨ Nonempty (LiveHeap out count post)

private theorem finish (out : CurrentCallEmptyEntryRoot.Output input #[]) (count : UInt64)
    (facts : CurrentCallEmptyEntryRoot.Facts out count)
    (result : CompilerFrameContext.ActualFrame) (post : Before) (current : MachineHooks.BorrowState)
    (trace : SuccessfulTrace.Trace (config options (remaining+1) span) limits
      (Storage.withCurrent #[] (CurrentCallEmptyEntryNonzeroDispatchState.frame out count) (CurrentCallEmptyEntryNonzeroDispatchState.machine out count)) (Storage.withCurrent #[] result post))
    (body : result.body=(CurrentCallEmptyEntryNonzeroDispatchState.frame out count).body) (identity : result.bodyIdentity=(CurrentCallEmptyEntryNonzeroDispatchState.frame out count).bodyIdentity)
    (callee : result.functionInstance=(CurrentCallEmptyEntryNonzeroDispatchState.frame out count).functionInstance) (extra : result.extra=(CurrentCallEmptyEntryNonzeroDispatchState.frame out count).extra)
    (destination : result.returnPlace=(CurrentCallEmptyEntryNonzeroDispatchState.frame out count).returnPlace)
    (continuation : result.returnContinuation=(CurrentCallEmptyEntryNonzeroDispatchState.frame out count).returnContinuation)
    (varargs : result.vaList=(CurrentCallEmptyEntryNonzeroDispatchState.frame out count).vaList) (size : result.locals.size=25) (location : result.location=.mir ⟨10,0⟩)
    (value : result.locals[0]?=some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩)
    (immediate : CopyHelperCleanup.AllImmediate result)
    (tracked : post.borrowTracker=some current) (mode : current.retagMode=(CurrentCallEmptyEntryNonzeroDispatchState.held out).retagMode)
    (global : current.global={ (CurrentCallEmptyEntryNonzeroDispatchState.held out).global with nextPointerTag:=current.global.nextPointerTag})
    (table : current.global.protectedTags=(CurrentCallEmptyEntryNonzeroDispatchState.held out).global.protectedTags)
    (counter : current.global.nextPointerTag.value.toNat=(CurrentCallEmptyEntryNonzeroDispatchState.held out).global.nextPointerTag.value.toNat+2)
    (ghost : post.user.payload.ghost=false) (shallow : post.user.payload.validation=.Shallow) (race : post.dataRace=none)
    (fixed : post.threads.fixedScheduling=true)
    (unchecked : ((config options (remaining+1) span).terminators.getControl post.user).checkedArithmetic=false)
    (noGc : ((config options (remaining+1) span).terminators.getControl post.user).gcInterval=0)
    (addresses : post.user.addresses=(CurrentCallEmptyEntryNonzeroDispatchState.machine out count).user.addresses)
    (types : post.user.payload.payload.user.types=(CurrentCallEmptyEntryNonzeroDispatchState.machine out count).user.payload.payload.user.types)
    (backend : post.user.payload.payload.user.backend=(CurrentCallEmptyEntryNonzeroDispatchState.machine out count).user.payload.payload.user.backend)
    (extras : post.user.payload.payload.user.runtime.extras=(CurrentCallEmptyEntryNonzeroDispatchState.machine out count).user.payload.payload.user.runtime.extras)
    (active : ∃ thread,post.threads.activeThread?=some thread)
    (heap : post.memory=(CurrentCallEmptyEntryNonzeroDispatchState.machine out count).memory ∨ Nonempty (LiveHeap out count post)) : BodyResult out count result post := by
  have initial := CurrentCallEmptyEntryNonzeroDispatchState.model out count
  obtain ⟨old,oldTracked,oldMode⟩ := initial.defaultTracker
  have equal : old=CurrentCallEmptyEntryNonzeroDispatchState.held out := Option.some.inj (oldTracked.symm.trans (CurrentCallEmptyEntryNonzeroDispatchState.tracked out count))
  subst old
  have model : DuplicatePrefixCallModel.Model options remaining span post := {
    initial with
    ghostOff := ghost
    shallow := shallow
    defaultTracker := ⟨current,tracked,mode.trans oldMode⟩
    noDataRace := race
    noBackend := backend.trans initial.noBackend
    metadata := by rw [types];exact initial.metadata
    fixedScheduler := fixed
    unchecked := unchecked
    noGc := noGc }
  have initialReady : CurrentCallBoolProtection.ProfileMemoryReadiness (CurrentCallEmptyEntryNonzeroDispatchState.machine out count) call := by
    obtain ⟨_,_,_,_,_,_,_,_,ready,_,_,_,_,_,_⟩ := facts
    exact ready
  have control := installed_control out.firstDone count (CurrentCallEmptyEntryRoot.sourceBorrow out.effect {})
    out.physical.id (CurrentCallEmptyEntryNonzeroDispatchState.sourceTracker out).global.nextPointerTag
  exact ⟨trace,body.trans control.1,identity.trans control.2.1,callee.trans control.2.2.1,size,location,value,
    destination.trans (CurrentCallEmptyEntryNonzeroDispatchState.destination out count facts),extra,continuation,varargs,immediate,model,
    by rw [types];exact CurrentCallEmptyEntryNonzeroDispatchState.origins out count facts,
    initialReady.transport extras,addresses,types,extras,active,⟨current,tracked,mode,global,table,counter⟩,heap⟩

private theorem protectors_below (out : CurrentCallEmptyEntryRoot.Output input #[]) (count : UInt64)
    (facts : CurrentCallEmptyEntryRoot.Facts out count) :
    ∀ row∈(CurrentCallEmptyEntryNonzeroDispatchState.held out).global.protectedTags.entries,row.1.value.toNat<(CurrentCallEmptyEntryNonzeroDispatchState.held out).global.nextPointerTag.value.toNat := by
  obtain ⟨_,_,_,_,_,_,_,runtime,_,_,_,_,_,_,_⟩ := facts
  exact runtime.below.protectors

private theorem current_memory (out : CurrentCallEmptyEntryRoot.Output input #[]) (count : UInt64) :
    let original := (CurrentCallEmptyEntryNonzeroDispatchState.sourceMachine out).memory
    (CurrentCallEmptyEntryNonzeroDispatchState.machine out count).memory=
      {original with live := (original.live.filter (fun row=>row.1!=out.physical.id)).push (out.physical.id,{out.physical.entry with allocation:=out.updated})} := by
  exact MemoryCopyBridge.live_update_twice (CurrentCallEmptyEntryNonzeroDispatchState.sourceMachine out).memory out.physical.id
    {out.physical.entry with allocation:=out.physical.entry.allocation.setExtra out.certificate.output.child.tree}
    {out.physical.entry with allocation:=out.updated}

private theorem lookup_replace (memory : MemoryState Provenance BorrowTree MiriMemoryKind) (id : AllocId)
    (old next : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (live : memory.live.find? (fun row=>row.1==id)=some (id,old)) (size : next.allocation.byteSize=old.allocation.byteSize) :
    GlobalAddressLiveErrorExclusion.lookup {memory with live:=(memory.live.filter (fun row=>row.1!=id)).push (id,next)}=
      GlobalAddressLiveErrorExclusion.lookup memory := by
  let final : MemoryState Provenance BorrowTree MiriMemoryKind := {memory with live:=(memory.live.filter (fun row=>row.1!=id)).push (id,next)}
  have found : final.live.find? (fun row=>row.1==id)=some (id,next) := MemoryCopyBridge.live_lookup_replaced memory id next
  have other (query : AllocId) (different : query≠id) :
      final.live.find? (fun row=>row.1==query)=memory.live.find? (fun row=>row.1==query) := by
    change ((memory.live.filter (fun row=>row.1!=id)).push (id,next)).find? _=_
    rw [Array.find?_push,Array.find?_filter]
    have predicate : (fun row : AllocId×LocalAllocation Provenance BorrowTree MiriMemoryKind =>
        decide ((row.1!=id)=true ∧ (row.1==query)=true))=(fun row=>row.1==query) := by
      funext row
      by_cases hit : row.1=query
      · simp [hit,different]
      · simp [hit]
    rw [predicate]
    cases memory.live.find? (fun row=>row.1==query) <;> simp [Ne.symm different]
  have anySame (query : AllocId) : final.live.any (fun row=>row.1==query)=memory.live.any (fun row=>row.1==query) := by
    by_cases same : query=id
    · subst query
      have before : memory.live.any (fun row=>row.1==id)=true := Array.any_eq_true'.mpr
        ⟨(id,old),Array.mem_of_find?_eq_some live,by simp⟩
      have after : final.live.any (fun row=>row.1==id)=true := Array.any_eq_true'.mpr
        ⟨(id,next),Array.mem_of_find?_eq_some found,by simp⟩
      exact after.trans before.symm
    · change ((memory.live.filter (fun row=>row.1!=id)).push (id,next)).any _=_
      rw [Array.any_push,Array.any_filter]
      have predicate : (fun row : AllocId×LocalAllocation Provenance BorrowTree MiriMemoryKind =>
          (row.1!=id) && (row.1==query))=(fun row=>row.1==query) := by
        funext row
        by_cases hit : row.1=query
        · simp [hit,same]
        · simp [hit]
      rw [predicate]
      simp [Ne.symm same]
  change GlobalAddressLiveErrorExclusion.lookup final=GlobalAddressLiveErrorExclusion.lookup memory
  unfold GlobalAddressLiveErrorExclusion.lookup
  congr 1
  · funext query
    by_cases same : query=id
    · subst query
      rw [MemoryCopyBridge.live_alloc_info final id next found,MemoryCopyBridge.live_alloc_info memory id old live]
      simp only [size,Except.toOption,Option.map_some]
    · unfold MemoryState.getAllocInfo
      rw [other query same]
      rfl
  · funext query
    unfold MemoryState.isAllocLive
    rw [anySame]

private theorem bool_lookup (out : CurrentCallEmptyEntryRoot.Output input #[]) (count : UInt64)
    (facts : CurrentCallEmptyEntryRoot.Facts out count) :
    GlobalAddressLiveErrorExclusion.lookup (CurrentCallEmptyEntryNonzeroDispatchState.machine out count).memory=GlobalAddressLiveErrorExclusion.lookup (CurrentCallEmptyEntryNonzeroDispatchState.sourceMachine out).memory := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,bytes,_,_,_⟩ := facts
  rw [current_memory]
  exact lookup_replace (CurrentCallEmptyEntryNonzeroDispatchState.sourceMachine out).memory out.physical.id out.physical.entry
    {out.physical.entry with allocation:=out.updated} out.physical.live bytes

private theorem integer_case (out : CurrentCallEmptyEntryRoot.Output input #[]) (count : UInt64)
    (facts : CurrentCallEmptyEntryRoot.Facts out count) (stackReady : CurrentCallPush.StackReadiness before #[])
    (nonzero : count≠0) (address : UInt64) (nonnull : address≠0)
    (representation : adjusted out.effect remaining span=(RetagReferencePlace.integerSliceValue address 0 ActualReferenceMetadata.reference).imm) :
    ∃ result post,BodyResult out count result post := by
  obtain ⟨dynamicEq,validationEq,dispatchEq,tagRoom⟩ := CurrentCallEmptyEntryNonzeroDispatchState.budgets out
  have fresh : (CurrentCallEmptyEntryNonzeroDispatchState.held out).global.nextPointerTag.value<18446744073709551615 :=
    UInt64.lt_iff_toNat_lt.mpr (by change (CurrentCallEmptyEntryNonzeroDispatchState.held out).global.nextPointerTag.value.toNat<18446744073709551615;omega)
  have nextRoom : (CurrentCallEmptyEntryNonzeroDispatchState.held out).global.nextPointerTag.value.toNat+1<18446744073709551615 := by omega
  have raw : (CurrentCallEmptyEntryNonzeroDispatchState.root input).frame.locals=Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout) :=
    RootEntryFrame.raw_locals _ _ _
  obtain ⟨thread,active,top⟩ := CurrentCallEmptyEntryNonzeroDispatchState.active out count stackReady
  obtain ⟨result,post,current,trace,body,identity,callee,extra,destination,continuation,varargs,localsIdentity,size,location,value,immediate,
    memory,tracked,mode,global,counter,ghost,shallow,race,fixed,unchecked,noGc,addresses,types,backend,extras,activeFinal⟩ :=
    CurrentCallEmptyEntryNonzeroBody.integer_from_installed out.effect limits remaining span (CurrentCallEmptyEntryNonzeroDispatchState.root input) out.firstDone raw
      (CurrentCallEmptyEntryNonzeroDispatchState.copied out count facts) (CurrentCallEmptyEntryRoot.sourceBorrow out.effect {}) out.physical.id
      (CurrentCallEmptyEntryNonzeroDispatchState.sourceTracker out).global.nextPointerTag (CurrentCallEmptyEntryNonzeroDispatchState.machine out count) (CurrentCallEmptyEntryNonzeroDispatchState.model out count) (CurrentCallEmptyEntryNonzeroDispatchState.origins out count facts)
      (CurrentCallEmptyEntryNonzeroDispatchState.held out) (CurrentCallEmptyEntryNonzeroDispatchState.tracked out count) address count nonnull nonzero representation fresh
      (options.place.dynamicFuel-1) (options.limits.validation-1) (limits.callDispatch-1)
      dynamicEq validationEq dispatchEq nextRoom thread active top
  refine ⟨result,post,finish out count facts result post current trace body identity callee extra destination continuation varargs
    size location value immediate tracked mode global ?_ counter ghost shallow race fixed unchecked noGc addresses types backend extras activeFinal (.inl memory)⟩
  rw [global]

private theorem miss_case (out : CurrentCallEmptyEntryRoot.Output input #[]) (count : UInt64)
    (facts : CurrentCallEmptyEntryRoot.Facts out count) (stackReady : CurrentCallPush.StackReadiness before #[])
    (nonzero : count≠0) (address : UInt64) (nonnull : address≠0)
    (representation : adjusted out.effect remaining span=(RetagReferencePlace.sliceValue (config options (remaining+1) span).access.runtime.base
      (Pointer.new .wildcard (Size.ofBytes address)) 0 ActualReferenceMetadata.reference).imm)
    (addressMode : (CurrentCallEmptyEntryNonzeroDispatchState.machine out count).user.addresses.provenanceMode≠.strict)
    (miss : (CurrentCallEmptyEntryNonzeroDispatchState.machine out count).user.addresses.allocIdFromAddr address 0
      (GlobalAddressLiveErrorExclusion.lookup (CurrentCallEmptyEntryNonzeroDispatchState.machine out count).memory)=.ok none) :
    ∃ result post,BodyResult out count result post := by
  obtain ⟨dynamicEq,validationEq,dispatchEq,tagRoom⟩ := CurrentCallEmptyEntryNonzeroDispatchState.budgets out
  have fresh : (CurrentCallEmptyEntryNonzeroDispatchState.held out).global.nextPointerTag.value<18446744073709551615 :=
    UInt64.lt_iff_toNat_lt.mpr (by change (CurrentCallEmptyEntryNonzeroDispatchState.held out).global.nextPointerTag.value.toNat<18446744073709551615;omega)
  have nextRoom : (CurrentCallEmptyEntryNonzeroDispatchState.held out).global.nextPointerTag.value.toNat+1<18446744073709551615 := by omega
  have raw : (CurrentCallEmptyEntryNonzeroDispatchState.root input).frame.locals=Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout) :=
    RootEntryFrame.raw_locals _ _ _
  obtain ⟨thread,active,top⟩ := CurrentCallEmptyEntryNonzeroDispatchState.active out count stackReady
  obtain ⟨result,post,current,trace,body,identity,callee,extra,destination,continuation,varargs,localsIdentity,size,location,value,immediate,
    memory,tracked,mode,global,counter,ghost,shallow,race,fixed,unchecked,noGc,addresses,types,backend,extras,activeFinal⟩ :=
    CurrentCallEmptyEntryNonzeroBodyMiss.miss_from_installed out.effect limits remaining span (CurrentCallEmptyEntryNonzeroDispatchState.root input) out.firstDone raw
      (CurrentCallEmptyEntryNonzeroDispatchState.copied out count facts) (CurrentCallEmptyEntryRoot.sourceBorrow out.effect {}) out.physical.id
      (CurrentCallEmptyEntryNonzeroDispatchState.sourceTracker out).global.nextPointerTag (CurrentCallEmptyEntryNonzeroDispatchState.machine out count) (CurrentCallEmptyEntryNonzeroDispatchState.model out count) (CurrentCallEmptyEntryNonzeroDispatchState.origins out count facts)
      (CurrentCallEmptyEntryNonzeroDispatchState.held out) (CurrentCallEmptyEntryNonzeroDispatchState.tracked out count) address count nonnull nonzero representation fresh addressMode miss
      (options.place.dynamicFuel-1) (options.limits.validation-1) (limits.callDispatch-1)
      dynamicEq validationEq dispatchEq nextRoom thread active top
  refine ⟨result,post,finish out count facts result post current trace body identity callee extra destination continuation varargs
    size location value immediate tracked mode global ?_ counter ghost shallow race fixed unchecked noGc addresses types backend extras activeFinal (.inl memory)⟩
  rw [global]

private theorem nonlive_case (out : CurrentCallEmptyEntryRoot.Output input #[]) (count : UInt64)
    (facts : CurrentCallEmptyEntryRoot.Facts out count) (stackReady : CurrentCallPush.StackReadiness before #[])
    (nonzero : count≠0) (id : AllocId) (base offset : UInt64) (nonnull : base+offset≠0)
    (representation : adjusted out.effect remaining span=(RetagReferencePlace.sliceValue (config options (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm)
    (metadataTag : Option BorTag)
    (metadata : DuplicatePrefixEmptyReferenceInput.Metadata (CurrentCallEmptyEntryNonzeroDispatchState.machine out count).memory id metadataTag)
    (absent : (CurrentCallEmptyEntryNonzeroDispatchState.machine out count).memory.live.find? (fun row=>row.1==id)=none)
    (cached : (CurrentCallEmptyEntryNonzeroDispatchState.machine out count).user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩)
    (protectorsBelow : ∀ row∈(CurrentCallEmptyEntryNonzeroDispatchState.held out).global.protectedTags.entries,
      row.1.value.toNat<(CurrentCallEmptyEntryNonzeroDispatchState.held out).global.nextPointerTag.value.toNat) :
    ∃ result post,BodyResult out count result post := by
  obtain ⟨dynamicEq,validationEq,dispatchEq,tagRoom⟩ := CurrentCallEmptyEntryNonzeroDispatchState.budgets out
  have fresh : (CurrentCallEmptyEntryNonzeroDispatchState.held out).global.nextPointerTag.value<18446744073709551615 :=
    UInt64.lt_iff_toNat_lt.mpr (by change (CurrentCallEmptyEntryNonzeroDispatchState.held out).global.nextPointerTag.value.toNat<18446744073709551615;omega)
  have nextRoom : (CurrentCallEmptyEntryNonzeroDispatchState.held out).global.nextPointerTag.value.toNat+1<18446744073709551615 := by omega
  have raw : (CurrentCallEmptyEntryNonzeroDispatchState.root input).frame.locals=Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout) :=
    RootEntryFrame.raw_locals _ _ _
  obtain ⟨thread,active,top⟩ := CurrentCallEmptyEntryNonzeroDispatchState.active out count stackReady
  obtain ⟨result,post,current,trace,body,identity,callee,extra,destination,continuation,varargs,localsIdentity,size,location,value,immediate,
    memory,tracked,mode,global,counter,ghost,shallow,race,fixed,unchecked,noGc,addresses,types,backend,extras,activeFinal⟩ :=
    CurrentCallEmptyEntryNonzeroBodyNonlive.nonlive_from_installed out.effect limits remaining span (CurrentCallEmptyEntryNonzeroDispatchState.root input) out.firstDone raw
      (CurrentCallEmptyEntryNonzeroDispatchState.copied out count facts) (CurrentCallEmptyEntryRoot.sourceBorrow out.effect {}) out.physical.id
      (CurrentCallEmptyEntryNonzeroDispatchState.sourceTracker out).global.nextPointerTag (CurrentCallEmptyEntryNonzeroDispatchState.machine out count) (CurrentCallEmptyEntryNonzeroDispatchState.model out count) (CurrentCallEmptyEntryNonzeroDispatchState.origins out count facts)
      (CurrentCallEmptyEntryNonzeroDispatchState.held out) (CurrentCallEmptyEntryNonzeroDispatchState.tracked out count)
      tracker.global.nextPointerTag id metadataTag base offset count nonnull nonzero representation metadata absent cached
      (by rw [CurrentCallEmptyEntryNonzeroDispatchState.counter];omega) tagRoom protectorsBelow fresh
      (options.place.dynamicFuel-1) (options.limits.validation-1) (limits.callDispatch-1)
      dynamicEq validationEq dispatchEq nextRoom thread active top
  refine ⟨result,post,finish out count facts result post current trace body identity callee extra destination continuation varargs
    size location value immediate tracked mode global ?_ counter ghost shallow race fixed unchecked noGc addresses types backend extras activeFinal (.inl memory)⟩
  rw [global]

private theorem live_case (out : CurrentCallEmptyEntryRoot.Output input #[]) (count : UInt64)
    (facts : CurrentCallEmptyEntryRoot.Facts out count) (stackReady : CurrentCallPush.StackReadiness before #[])
    (nonzero : count≠0) (id : AllocId) (allocated : out.effect.allocation=some id)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (live : (CurrentCallEmptyEntryNonzeroDispatchState.machine out count).memory.live.find? (fun row=>row.1==id)=some (id,entry))
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra (CurrentCallEmptyEntryNonzeroDispatchState.held out).global)
    (room : entry.allocation.extra.nodes.size+2≤4294967295)
    (parent : UniIndex) (parentNode : TreeNode)
    (tagged : entry.allocation.extra.indexOfTag tracker.global.nextPointerTag=some parent)
    (present : entry.allocation.extra.nodes.get parent=some parentNode)
    (base offset : UInt64) (nonnull : base+offset≠0)
    (representation : adjusted out.effect remaining span=(RetagReferencePlace.sliceValue (config options (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm)
    (cached : (CurrentCallEmptyEntryNonzeroDispatchState.machine out count).user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩) :
    ∃ result post,BodyResult out count result post := by
  obtain ⟨dynamicEq,validationEq,dispatchEq,tagRoom⟩ := CurrentCallEmptyEntryNonzeroDispatchState.budgets out
  have fresh : (CurrentCallEmptyEntryNonzeroDispatchState.held out).global.nextPointerTag.value<18446744073709551615 :=
    UInt64.lt_iff_toNat_lt.mpr (by change (CurrentCallEmptyEntryNonzeroDispatchState.held out).global.nextPointerTag.value.toNat<18446744073709551615;omega)
  have nextRoom : (CurrentCallEmptyEntryNonzeroDispatchState.held out).global.nextPointerTag.value.toNat+1<18446744073709551615 := by omega
  have raw : (CurrentCallEmptyEntryNonzeroDispatchState.root input).frame.locals=Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout) := RootEntryFrame.raw_locals _ _ _
  have mappingFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping (CurrentCallEmptyEntryNonzeroDispatchState.held out).global.nextPointerTag := by
    intro row member
    exact GeneralBorrowForestTagHighWater.different _ _ (runtime.below.mapping row member)
  have accounting := runtime.formed.allocator.accounting
  have fits : entry.allocation.extra.tagMapping.mapping.size≤4294967295 := by
    unfold GeneralBorrowFreshStagePool.Accounting at accounting
    omega
  let first := EmptyForestSharedPool.factory entry.allocation.extra tracker.global.nextPointerTag (CurrentCallEmptyEntryNonzeroDispatchState.held out).global.nextPointerTag
    parent parentNode (Classical.choice runtime.formed.depth) tagged present mappingFresh runtime.formed.allocator.pool
    accounting fits (DuplicatePrefixBorrowContract.vacant_clean runtime)
  obtain ⟨thread,active,top⟩ := CurrentCallEmptyEntryNonzeroDispatchState.active out count stackReady
  obtain ⟨result,post,tree,current,treeEq,trace,body,identity,callee,extra,destination,continuation,varargs,localsIdentity,size,location,value,immediate,
    sourceLive,memory,tracked,mode,⟨fresh2,currentEq⟩,ghost,shallow,race,fixed,unchecked,noGc,addresses,types,backend,extras,activeFinal⟩ :=
    CurrentCallEmptyEntryNonzeroBody.live_from_installed out.effect limits remaining span (CurrentCallEmptyEntryNonzeroDispatchState.root input) out.firstDone raw
      (CurrentCallEmptyEntryNonzeroDispatchState.copied out count facts) (CurrentCallEmptyEntryRoot.sourceBorrow out.effect {}) out.physical.id
      (CurrentCallEmptyEntryNonzeroDispatchState.sourceTracker out).global.nextPointerTag (CurrentCallEmptyEntryNonzeroDispatchState.machine out count) (CurrentCallEmptyEntryNonzeroDispatchState.model out count) (CurrentCallEmptyEntryNonzeroDispatchState.origins out count facts)
      (CurrentCallEmptyEntryNonzeroDispatchState.held out) (CurrentCallEmptyEntryNonzeroDispatchState.tracked out count) tracker.global.nextPointerTag (CurrentCallEmptyEntryNonzeroDispatchState.held out).global.nextPointerTag
      id entry base offset count nonnull nonzero representation first rfl fresh cached live runtime
      (options.place.dynamicFuel-1) (options.limits.validation-1) (limits.callDispatch-1)
      dynamicEq validationEq dispatchEq nextRoom room thread active top
  let expression := allocatedTracker (CurrentCallEmptyEntryNonzeroDispatchState.held out) fresh
  have firstStep : expression.global.nextPointerTag.value.toNat=(CurrentCallEmptyEntryNonzeroDispatchState.held out).global.nextPointerTag.value.toNat+1 :=
    GenericFunctionEntryNumerics.successor_value (CurrentCallEmptyEntryNonzeroDispatchState.held out).global.nextPointerTag fresh
  have secondStep := GenericFunctionEntryNumerics.successor_value expression.global.nextPointerTag fresh2
  have below : ∀ row∈expression.global.protectedTags.entries,row.1.value.toNat<expression.global.nextPointerTag.value.toNat := by
    intro row member
    have original := runtime.below.protectors row member
    omega
  have global : current.global={ (CurrentCallEmptyEntryNonzeroDispatchState.held out).global with nextPointerTag:=current.global.nextPointerTag} := by
    rw [currentEq,S03NonliveProtectorLedger.global expression fresh2 id below]
    rfl
  have table : current.global.protectedTags=(CurrentCallEmptyEntryNonzeroDispatchState.held out).global.protectedTags := by
    rw [currentEq,S03NonliveProtectorLedger.global expression fresh2 id below]
    rfl
  have counter : current.global.nextPointerTag.value.toNat=(CurrentCallEmptyEntryNonzeroDispatchState.held out).global.nextPointerTag.value.toNat+2 := by
    rw [currentEq]
    change (TypedRetagEmpty.successorTag expression.global.nextPointerTag fresh2).value.toNat=_
    rw [secondStep]
    omega
  have heap : Nonempty (LiveHeap out count post) := by
    refine ⟨⟨id,allocated,entry,live,runtime,fresh,room,first,?_⟩⟩
    rw [treeEq] at memory
    exact memory
  exact ⟨result,post,finish out count facts result post current trace body identity callee extra destination continuation varargs
    size location value immediate tracked mode global table counter ghost shallow race fixed unchecked noGc addresses types backend extras activeFinal (.inr heap)⟩

private theorem none_case (out : CurrentCallEmptyEntryRoot.Output input #[]) (count : UInt64)
    (facts : CurrentCallEmptyEntryRoot.Facts out count) (stackReady : CurrentCallPush.StackReadiness before #[])
    (nonzero : count≠0) (absent : out.effect.allocation=none) : ∃ result post,BodyResult out count result post := by
  cases effectEq : out.effect with
  | integer address =>
    have nonnull : address≠0 := (CurrentCallEmptyTypedEntryInteger.empty_candidate input).1
    apply integer_case out count facts stackReady nonzero address nonnull
    unfold adjusted
    rw [effectEq]
    rfl
  | miss address missing =>
    have candidate := CurrentCallEmptyTypedEntryInteger.empty_candidate input
    change address≠0 ∧ DuplicatePrefixEmptyReferenceInput.Wildcard
      (DuplicatePrefixCallSpecification.imageContext options before tracker) before.memory before.user.addresses at candidate
    apply miss_case out count facts stackReady nonzero address candidate.1
    · unfold adjusted
      rw [effectEq]
      simp only [Effect.output,Effect.allocation,DuplicatePrefixSliceArgument.rawValue,CanonicalConfigFacts.actual_access_runtime]
    · rw [CurrentCallEmptyEntryNonzeroDispatchState.addresses]
      exact candidate.2.nonstrict
    · have memory : (CurrentCallEmptyEntryNonzeroDispatchState.sourceMachine out).memory=before.memory := by
        unfold CurrentCallEmptyEntryNonzeroDispatchState.sourceMachine afterArgumentsMachine
        rw [effectEq]
        rfl
      rw [CurrentCallEmptyEntryNonzeroDispatchState.addresses,bool_lookup out count facts,memory]
      exact missing
  | concreteLive | concreteNonlive | concreteImage | wildcardLive | wildcardNonlive | wildcardImage =>
    simp only [effectEq,Effect.allocation] at absent
    cases absent

private theorem allocated_case (out : CurrentCallEmptyEntryRoot.Output input #[]) (count : UInt64)
    (facts : CurrentCallEmptyEntryRoot.Facts out count) (stackReady : CurrentCallPush.StackReadiness before #[])
    (nonzero : count≠0) (id : AllocId) (allocated : out.effect.allocation=some id)
    (source : (∃ metadataTag,DuplicatePrefixEmptyReferenceInput.Metadata (CurrentCallEmptyEntryNonzeroDispatchState.machine out count).memory id metadataTag ∧
        (CurrentCallEmptyEntryNonzeroDispatchState.machine out count).memory.live.find? (fun row=>row.1==id)=none) ∨
      ∃ entry,(CurrentCallEmptyEntryNonzeroDispatchState.machine out count).memory.live.find? (fun row=>row.1==id)=some (id,entry) ∧
        DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra (CurrentCallEmptyEntryNonzeroDispatchState.held out).global ∧
        entry.allocation.extra.nodes.size+2≤4294967295 ∧
        ∃ index node,entry.allocation.extra.indexOfTag tracker.global.nextPointerTag=some index ∧ entry.allocation.extra.nodeAt index=some node) :
    ∃ result post,BodyResult out count result post := by
  obtain ⟨base,cached⟩ := CurrentCallEmptyEntryNonzeroDispatchRuntime.cached_source input out count id allocated
  let offset := DuplicatePrefixSliceArgument.address argument-base
  have bits : base+offset=DuplicatePrefixSliceArgument.address argument := by
    rw [UInt64.add_comm]
    exact UInt64.sub_add_cancel _ _
  have nonnull : DuplicatePrefixSliceArgument.address argument≠0 := by
    have candidate := (CurrentCallEmptyTypedEntryInteger.empty_candidate input).1
    cases argument <;> exact candidate
  have representation : adjusted out.effect remaining span=(RetagReferencePlace.sliceValue (config options (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm := by
    unfold adjusted Effect.output
    rw [allocated]
    simp only [DuplicatePrefixSliceArgument.rawValue]
    rw [bits]
    simp only [CanonicalConfigFacts.actual_access_runtime]
  rw [←bits] at nonnull
  rcases source with ⟨metadataTag,metadata,absent⟩ | ⟨entry,live,runtime,room,index,node,tagged,present⟩
  · exact nonlive_case out count facts stackReady nonzero id base offset nonnull representation metadataTag metadata absent cached
      (protectors_below out count facts)
  · exact live_case out count facts stackReady nonzero id allocated entry live runtime room index node tagged present base offset
      nonnull representation cached

/-- The actual empty-entry output reaches Return false for every nonzero
count. Every source case is derived from the SAME original invocation. -/
theorem from_entry (out : CurrentCallEmptyEntryRoot.Output input #[]) (count : UInt64)
    (facts : CurrentCallEmptyEntryRoot.Facts out count) (stackReady : CurrentCallPush.StackReadiness before #[])
    (nonzero : count≠0) : ∃ result post,BodyResult out count result post := by
  cases allocated : out.effect.allocation with
  | none => exact none_case out count facts stackReady nonzero allocated
  | some id =>
    exact allocated_case out count facts stackReady nonzero id allocated
      (CurrentCallEmptyEntryNonzeroDispatchRuntime.source input out count facts id allocated)

/-- ORIGINAL empty-source admission and physical stack/profile readiness
construct entry internally, then execute Shared, len and the rejecting body.
Release, the final Bool store and whole-call Result are separate consumers. -/
theorem invoke
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument 0 place call data)
    (stackReady : CurrentCallPush.StackReadiness before #[])
    (memoryReady : CurrentCallBoolProtection.ProfileMemoryReadiness before call)
    (count : UInt64) (nonzero : count≠0) :
    ∃ out : CurrentCallEmptyEntryRoot.Output input #[],∃ _facts : CurrentCallEmptyEntryRoot.Facts out count,
      ∃ result post,BodyResult out count result post := by
  obtain ⟨out,facts⟩ := CurrentCallEmptyEntryRoot.complete input #[] stackReady memoryReady count
  obtain ⟨result,post,body⟩ := from_entry out count facts stackReady nonzero
  exact ⟨out,facts,result,post,body⟩


end
end DuplicatePrefix.CurrentCallEmptyEntryNonzeroDispatch

open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallEmptyEntryNonzeroDispatch" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved original nonzero dispatcher dependency {dependency}"
