import duplicate_prefix.GlobalEmptyReferenceContext
import duplicate_prefix.ActualConcreteEmptyReference
import duplicate_prefix.WildcardLazyGlobalResolve
import duplicate_prefix.WildcardHitPoolRoot

namespace DuplicatePrefix.WildcardGlobalEmptyReferenceReborrow
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Input Miri.Interpreter Miri.TreeBorrows Miri.DataStructures
open TypedRetagEntry CanonicalConfigFacts ActualReferenceContext ActualReferenceMetadata TypedBorrowSteps
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

open Lean Elab in
elab "global_zero_insert" : term => do
  let names := (← getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".TypedBorrowSteps.zero_insert_steps" then some name else none
  let [name] := names | throwError "expected original zero insertion proof"
  Lean.Meta.mkConstWithFreshMVarLevels name

def materialized (options : EvalConfigurationCore.Options) (state : RootState)
    (id : AllocId) (root : BorTag) (source : Allocation CtfeProvenance Unit)
    (converted : Allocation Provenance Unit) : RootState :=
  {state with machine := (GlobalDataOnlyMaterialize.cached (GlobalDataOnlyActualConfig.extras options)
    state.machine id .global (converted.mapExtra (fun _ => BorrowTree.new root source.byteSize)))}

def rootSlot (root : BorTag) (size : Size) : WildcardHitPoolRoot.Slot (BorrowTree.new root size) :=
  .append rfl rfl (by change 1 ≤ 4294967295;decide)

def finalTree (root tag : BorTag) (size : Size) : BorrowTree := (rootSlot root size).after tag

def completed (options : EvalConfigurationCore.Options) (state : RootState)
    (id : AllocId) (root tag : BorTag) (source : Allocation CtfeProvenance Unit)
    (converted : Allocation Provenance Unit) : RootState :=
  let cached := materialized options state id root source converted
  {cached with machine := {cached.machine with memory := (RetagEntry.updatedMemory cached.machine.memory id
    ⟨.machine .global,converted.mapExtra (fun _ => BorrowTree.new root source.byteSize)⟩
    (finalTree root tag source.byteSize))}}

theorem reborrow (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (actualPointers : ctx.pointers = GlobalDataOnlyActualConfig.pointers PreparedReflection.actual.compiler
      PreparedReflection.actual.image (Machine.leaves PreparedReflection.actual.prepared options.place.debugAssertions) ())
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker)
    (id : AllocId) (root tag : BorTag) (base offset : UInt64)
    (source : Allocation CtfeProvenance Unit)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (addressMode : machine.user.addresses.provenanceMode ≠ .strict)
    (geometry : WildcardGeneralHitReborrow.Geometry machine.user.addresses.intToPtrMap (base+offset) base id source.byteSize)
    (exposed : machine.user.addresses.exposed.contains id = true)
    (allocLive : machine.memory.isAllocLive id = true)
    (distinct : root ≠ tag) (rootCached : tracker.global.rootTag? id = some root)
    (supported : GlobalSupportedImage.Supported source PreparedReflection.actual.compiler.runtime.target
      machine.memory tracker.global.rootPointerTags machine.user.addresses.baseAddr)
    (race : machine.dataRace = none)
    (noExtras : (machine.user.payload.payload.user.runtime.extras.allocations.any (fun row => row.1 == id)) = false)
    (absent : machine.memory.live.find? (fun row => row.1 == id) = none)
    (noFunction : machine.memory.hasFunctionPointer id = false)
    (noVaList : machine.memory.hasVaListId id = false)
    (descriptor : machine.memory.findGlobal? id = some
      ⟨id,.memory,source.byteSize,source.align,source.mutability,some (.memory source)⟩) :
    let h := adapted options remaining span ctx.pointers
    let place := RetagReferencePlace.slicePlace
      (Pointer.new .wildcard (Size.ofBytes (base+offset))) 0 pointee
    ∃ converted : Allocation Provenance Unit,
      GlobalAllocationAttributes.Attributes source converted ∧
      TypedRetag.reborrow h options.limits.retag place Size.ZERO ChildBorrow.fnEntryPolicy tag
        (Storage.withCurrent frames frame machine) =
        .ok (some (.concrete id tag))
          (completed options (registeredState frames frame borrowFrame machine tracker id tag)
            id root tag source converted) := by
  let h := adapted options remaining span ctx.pointers
  let place := RetagReferencePlace.slicePlace
    (Pointer.new .wildcard (Size.ofBytes (base+offset))) 0 pointee
  let registered := registeredState frames frame borrowFrame machine tracker id tag
  have info := GlobalDataOnlyMaterialize.alloc_info machine id source absent noFunction noVaList descriptor
  have ensure := GlobalDataOnlyActualConfig.ensure_success options () remaining span registered
    (registeredTracker tracker tag) id root source supported rfl rootCached race noExtras absent descriptor
  obtain ⟨converted,facts,ensure⟩ := ensure
  refine ⟨converted,facts,?_⟩
  have check : h.checkPtrAccess place.mplace.ptr Size.ZERO (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames frame machine) := by
    rw [ctx.source.check]
    exact RetagPointerChecks.check_pointer_zero (config options remaining span).access place.mplace.ptr _
  have resolve : h.resolveAllocation place.mplace.ptr (Storage.withCurrent frames frame machine) =
      .ok (some ⟨id,Size.ofBytes offset,.wildcard⟩) (Storage.withCurrent frames frame machine) := by
    rw [ctx.source.resolve]
    have known : (machine.memory.getAllocInfo id).toOption.map (·.size) = some source.byteSize := by
      simp only [info,Except.toOption,Option.map_some]
    have result := WildcardLazyGlobalResolve.resolve ctx.pointers (Storage.withCurrent frames frame machine)
      (base+offset) base id source.byteSize geometry ctx.arithmetic addressMode exposed cachedAddress allocLive known
    have relative : (base+offset)-base=offset := by rw [UInt64.add_comm base offset,UInt64.add_sub_cancel]
    rw [relative] at result
    exact result
  have log : h.logCreation = (fun _ _ _ _ _ => pure ()) := ctx.source.log
  have queries := reference_queries options remaining span ctx.pointers
  have inside := TypedRetagPolicyFields.inside_for_policy h options.limits.retag place Size.ZERO
    ChildBorrow.fnEntryPolicy ChildBorrow.fnEntryLocation
    (ChildBorrow.mutable_fn_entry_initial_location true) ctx.source.precise queries.freeze
  have ensureWiring : h.ensureTreeExtra = (config options remaining span).retag.ensureTreeExtra := by
    rw [ctx.source.ensure,actualPointers,GlobalDataOnlyActualConfig.actual_ensure]
  change TypedRetag.reborrow h options.limits.retag place Size.ZERO ChildBorrow.fnEntryPolicy tag
    (Storage.withCurrent frames frame machine) = _
  unfold TypedRetag.reborrow
  simp only [log,check,resolve,
    bind,EStateM.bind,pure,EStateM.pure,ChildBorrow.fnEntryPolicy]
  rw [current_frame_pushed (Storage.withCurrent frames frame machine) frames frame rfl]
  simp only [frameBorrow,bind,EStateM.bind,pure,EStateM.pure]
  unfold_typed ".TypedRetag.tracker"
  simp only [get,getThe,MonadStateOf.get,EStateM.get,Storage.withCurrent,enabled,
    bind,EStateM.bind,pure,EStateM.pure]
  simp only [GlobalState.addProtector,FrameState.addProtector,modify,modifyGet,
    MonadStateOf.modifyGet,EStateM.modifyGet,MachineHooks.setCurrentFrame,
    get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
    set,EStateM.set,Storage.withCurrent,Array.isEmpty_push,Array.pop_push,
    Bool.false_eq_true,↓reduceIte]
  unfold_typed ".TypedRetag.checked"
  simp only [info,bind,EStateM.bind,pure,EStateM.pure]
  have sameKind : (AllocationKind.liveData != .liveData) = false := rfl
  simp only [sameKind,Bool.false_eq_true,↓reduceIte]
  erw [inside]
  simp only [bind,EStateM.bind,pure,EStateM.pure]
  rw [ensureWiring]
  erw [ensure]
  simp only [bind,EStateM.bind,pure,EStateM.pure]
  let entry : LocalAllocation Provenance BorrowTree MiriMemoryKind :=
    ⟨.machine .global,converted.mapExtra (fun _ => BorrowTree.new root source.byteSize)⟩
  have present : (materialized options registered id root source converted).machine.memory.live.find?
      (fun row => row.1 == id) = some (id,entry) := by
    exact MemoryCopyBridge.live_lookup_replaced registered.machine.memory id entry
  have child : entry.allocation.extra.newChild (Size.ofBytes offset) (.wildcard) tag
      (DedupRangeMap.new Size.ZERO ChildBorrow.fnEntryLocation) ChildBorrow.fnEntryPolicy.outsidePermission
      ChildBorrow.fnEntryPolicy.protector.isSome =
        ⟨finalTree root tag source.byteSize,.ok ()⟩ := by
    have fresh : GeneralBorrowTagMap.Fresh (BorrowTree.new root source.byteSize).tagMapping tag := by
      intro row member
      change row ∈ (#[(root,(⟨0⟩ : UniIndex))] : Array (BorTag × UniIndex)) at member
      have equal : row = (root,(⟨0⟩ : UniIndex)) := by simpa only [Array.mem_singleton] using member
      rw [equal]
      exact distinct
    exact (rootSlot root source.byteSize).child tag fresh offset
  have result := global_zero_insert h (materialized options registered id root source converted)
    id entry offset (.wildcard) tag ChildBorrow.fnEntryLocation ChildBorrow.fnEntryPolicy
    (finalTree root tag source.byteSize) present child
  exact result
end
end DuplicatePrefix.WildcardGlobalEmptyReferenceReborrow
