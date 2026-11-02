import duplicate_prefix.CurrentCallEmptyMaterializedBorrow
import duplicate_prefix.ActualConcreteEmptyReference
import duplicate_prefix.WildcardLazyGlobalResolve
import duplicate_prefix.WildcardHitPoolRoot

namespace DuplicatePrefix.CurrentCallEmptyMaterializedWildcard
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Input Miri.Interpreter Miri.TreeBorrows Miri.DataStructures
open TypedRetagEntry CanonicalConfigFacts ActualReferenceContext ActualReferenceMetadata TypedBorrowSteps
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

def rootSlot (root : BorTag) (size : Size) : WildcardHitPoolRoot.Slot (BorrowTree.new root size) :=
  .append rfl rfl (by change 1 ≤ 4294967295;decide)

def finalTree (root tag : BorTag) (size : Size) : BorrowTree := (rootSlot root size).after tag

theorem reborrow (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (actualPointers : ctx.pointers = GlobalDataOnlyActualConfig.pointers PreparedReflection.actual.compiler
      PreparedReflection.actual.image (Machine.leaves PreparedReflection.actual.prepared options.place.debugAssertions) ())
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker)
    (id : AllocId) (root tag : BorTag) (base offset : UInt64)
    (info : AllocationInfo) (infoEq : machine.memory.getAllocInfo id=.ok info) (dataKind : info.kind=.liveData)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (addressMode : machine.user.addresses.provenanceMode ≠ .strict)
    (geometry : WildcardGeneralHitReborrow.Geometry machine.user.addresses.intToPtrMap (base+offset) base id info.size)
    (exposed : machine.user.addresses.exposed.contains id = true)
    (allocLive : machine.memory.isAllocLive id = true)
    (distinct : root ≠ tag)
    (after : RootState) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (capacity : Size)
    (ensure : (config options remaining span).retag.ensureTreeExtra id
      (registeredState frames frame borrowFrame machine tracker id tag)=.ok () after)
    (present : after.machine.memory.live.find? (fun row=>row.1==id)=some (id,entry))
    (rootShape : entry.allocation.extra=BorrowTree.new root capacity) :
    let h:=adapted options remaining span ctx.pointers
    let place:=RetagReferencePlace.slicePlace (Pointer.new .wildcard (Size.ofBytes (base+offset))) 0 pointee
    TypedRetag.reborrow h options.limits.retag place Size.ZERO ChildBorrow.fnEntryPolicy tag
      (Storage.withCurrent frames frame machine)=
      .ok (some (.concrete id tag)) (CurrentCallEmptyMaterializedBorrow.completed after id entry (finalTree root tag capacity)) := by
  let h := adapted options remaining span ctx.pointers
  let place := RetagReferencePlace.slicePlace
    (Pointer.new .wildcard (Size.ofBytes (base+offset))) 0 pointee
  let registered := registeredState frames frame borrowFrame machine tracker id tag
  have check : h.checkPtrAccess place.mplace.ptr Size.ZERO (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames frame machine) := by
    rw [ctx.source.check]
    exact RetagPointerChecks.check_pointer_zero (config options remaining span).access place.mplace.ptr _
  have resolve : h.resolveAllocation place.mplace.ptr (Storage.withCurrent frames frame machine) =
      .ok (some ⟨id,Size.ofBytes offset,.wildcard⟩) (Storage.withCurrent frames frame machine) := by
    rw [ctx.source.resolve]
    have known : (machine.memory.getAllocInfo id).toOption.map (·.size) = some info.size := by
      simp only [infoEq,Except.toOption,Option.map_some]
    have result := WildcardLazyGlobalResolve.resolve ctx.pointers (Storage.withCurrent frames frame machine)
      (base+offset) base id info.size geometry ctx.arithmetic addressMode exposed cachedAddress allocLive known
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
  simp only [frameBorrow,EStateM.bind]
  unfold_typed ".TypedRetag.tracker"
  simp only [get,getThe,MonadStateOf.get,EStateM.get,Storage.withCurrent,enabled,
    bind,EStateM.bind,pure,EStateM.pure]
  simp only [GlobalState.addProtector,FrameState.addProtector,modify,modifyGet,
    MonadStateOf.modifyGet,EStateM.modifyGet,MachineHooks.setCurrentFrame,
    get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,
    set,EStateM.set,Array.isEmpty_push,Array.pop_push,
    Bool.false_eq_true,↓reduceIte]
  unfold_typed ".TypedRetag.checked"
  simp only [infoEq,pure,EStateM.pure]
  have sameKind : (info.kind != .liveData) = false := by rw [dataKind];rfl
  simp only [sameKind,Bool.false_eq_true,↓reduceIte]
  erw [inside]
  simp only [EStateM.bind,pure,EStateM.pure]
  rw [ensureWiring]
  erw [ensure]
  have child : entry.allocation.extra.newChild (Size.ofBytes offset) (.wildcard) tag
      (DedupRangeMap.new Size.ZERO ChildBorrow.fnEntryLocation) ChildBorrow.fnEntryPolicy.outsidePermission
      ChildBorrow.fnEntryPolicy.protector.isSome =
        ⟨finalTree root tag capacity,.ok ()⟩ := by
    rw [rootShape]
    have fresh : GeneralBorrowTagMap.Fresh (BorrowTree.new root capacity).tagMapping tag := by
      intro row member
      change row ∈ (#[(root,(⟨0⟩ : UniIndex))] : Array (BorTag × UniIndex)) at member
      have equal : row = (root,(⟨0⟩ : UniIndex)) := by simpa only [Array.mem_singleton] using member
      rw [equal]
      exact distinct
    exact (rootSlot root capacity).child tag fresh offset
  have result := current_empty_zero_insert h after
    id entry offset (.wildcard) tag ChildBorrow.fnEntryLocation ChildBorrow.fnEntryPolicy
    (finalTree root tag capacity) present child
  exact result
end
end DuplicatePrefix.CurrentCallEmptyMaterializedWildcard

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "CurrentCallEmptyMaterializedWildcard.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved materialized-empty dependency {name}: {dependency}"
