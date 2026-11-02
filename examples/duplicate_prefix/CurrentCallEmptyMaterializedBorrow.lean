import duplicate_prefix.GlobalEmptyReferenceContext
import duplicate_prefix.ActualConcreteEmptyReference

namespace DuplicatePrefix.CurrentCallEmptyMaterializedBorrow
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Input Miri.Interpreter Miri.TreeBorrows Miri.DataStructures
open TypedRetagEntry CanonicalConfigFacts ActualReferenceContext ActualReferenceMetadata TypedBorrowSteps
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

open Lean Elab in
elab "current_empty_zero_insert" : term => do
  let names := (← getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".TypedBorrowSteps.zero_insert_steps" then some name else none
  let [name] := names | throwError "expected original zero insertion proof"
  Lean.Meta.mkConstWithFreshMVarLevels name

/-- The real post-ensure machine is retained in full. Only its selected
allocation receives the zero-byte child; caches/counters/tape are not reset. -/
def completed (after : RootState) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (tree : BorrowTree) : RootState :=
  {after with machine:={after.machine with memory:=RetagEntry.updatedMemory after.machine.memory id entry tree}}

/-- Immediate consumer of the actual finite ensure producer. Its equation is
an internal derived step, never an OrdinaryInput field. No source family,
mutability, initialization, Supported image, or cached relocation targets. -/
theorem reborrow (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (actualPointers : ctx.pointers = GlobalDataOnlyActualConfig.pointers PreparedReflection.actual.compiler
      PreparedReflection.actual.image (Machine.leaves PreparedReflection.actual.prepared options.place.debugAssertions) ())
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker)
    (id : AllocId) (root tag : BorTag) (base offset : UInt64)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (distinct : root ≠ tag)
    (info : AllocationInfo) (infoEq : machine.memory.getAllocInfo id=.ok info) (dataKind : info.kind=.liveData)
    (after : RootState) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (capacity : UInt64)
    (ensure : (config options remaining span).retag.ensureTreeExtra id
      (registeredState frames frame borrowFrame machine tracker id tag)=.ok () after)
    (present : after.machine.memory.live.find? (fun row=>row.1==id)=some (id,entry))
    (rootShape : entry.allocation.extra=BorrowTree.new root (Size.ofBytes capacity)) :
    let h:=adapted options remaining span ctx.pointers
    let place:=RetagReferencePlace.slicePlace (Pointer.new (.concrete id root) (Size.ofBytes (base+offset))) 0 pointee
    TypedRetag.reborrow h options.limits.retag place Size.ZERO ChildBorrow.fnEntryPolicy tag
      (Storage.withCurrent frames frame machine)=
      .ok (some (.concrete id tag)) (completed after id entry (TypedRetagConcreteEmpty.lazyTree root tag capacity)) := by
  let h := adapted options remaining span ctx.pointers
  let place := RetagReferencePlace.slicePlace
    (Pointer.new (.concrete id root) (Size.ofBytes (base+offset))) 0 pointee
  let registered := registeredState frames frame borrowFrame machine tracker id tag
  have check : h.checkPtrAccess place.mplace.ptr Size.ZERO (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames frame machine) := by
    rw [ctx.source.check]
    exact RetagPointerChecks.check_pointer_zero (config options remaining span).access place.mplace.ptr _
  have resolve : h.resolveAllocation place.mplace.ptr (Storage.withCurrent frames frame machine) =
      .ok (some ⟨id,Size.ofBytes offset,.concrete root⟩) (Storage.withCurrent frames frame machine) := by
    rw [ctx.source.resolve]
    exact RetagPointerChecks.resolve_allocation_cached ctx.pointers
      (Storage.withCurrent frames frame machine) id root base offset ctx.arithmetic cachedAddress
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
  have child : entry.allocation.extra.newChild (Size.ofBytes offset) (.concrete root) tag
      (DedupRangeMap.new Size.ZERO ChildBorrow.fnEntryLocation) ChildBorrow.fnEntryPolicy.outsidePermission
      ChildBorrow.fnEntryPolicy.protector.isSome =
        ⟨TypedRetagConcreteEmpty.lazyTree root tag capacity,.ok ()⟩ := by
    rw [rootShape]
    exact ChildConstructor.new_child_zero_exact root tag distinct capacity offset
  have result := current_empty_zero_insert h after
    id entry offset (.concrete root) tag ChildBorrow.fnEntryLocation ChildBorrow.fnEntryPolicy
    (TypedRetagConcreteEmpty.lazyTree root tag capacity) present child
  exact result
end
end DuplicatePrefix.CurrentCallEmptyMaterializedBorrow

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "CurrentCallEmptyMaterializedBorrow.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved materialized-empty dependency {name}: {dependency}"
