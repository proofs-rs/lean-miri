import duplicate_prefix.CurrentCallEmptyMaterializedPointer
import duplicate_prefix.CurrentCallEmptyValidateOfRetag
import duplicate_prefix.ReferenceArgumentCopy
import duplicate_prefix.ConcreteEmptyReferenceArgumentCopy
import duplicate_prefix.CurrentCallConversionMaterialize
namespace DuplicatePrefix.CurrentCallEmptyMaterializedCopy
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext ActualReferenceMetadata TypedBorrowSteps ReferenceBorrowDriver
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
/-- Exact real ensure output, retaining every converter state change. -/
def materialized (registered : RootState) (after : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (id : AllocId) (root : BorTag) (converted : Allocation Provenance Unit) : RootState:=
  {registered with machine:=(CurrentCallConversionMaterialize.installed after id .global
    (converted.mapExtra (fun _=>BorrowTree.new root converted.byteSize)))}

/-- Actual CURRENT concrete zero-reference copy after the finite ensure step.
The consumer derives its installed live row internally. Readonly/uninitialized
source storage and arbitrary converter cache/counter changes are permitted;
no source family, Supported image or post-copy state is an input condition. -/
theorem concrete (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (actualPointers : ctx.pointers=GlobalDataOnlyActualConfig.pointers PreparedReflection.actual.compiler
      PreparedReflection.actual.image (Machine.leaves PreparedReflection.actual.prepared options.place.debugAssertions) ())
    (debug : options.place.debugAssertions=false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (dynamicEq : options.place.dynamicFuel=dynamicFuel+1) (validationEq : options.limits.validation=validityFuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : MIR.LocalId) (valid : localId<frame.locals.size) (old : Immediate Provenance)
    (live : frame.locals[localId].value=.live (.immediate old)) (cached : frame.locals[localId].layout=some reference)
    (noClocks : frame.extra.dataRace=none) (ghost : machine.user.payload.ghost=false) (shallow : machine.user.payload.validation=.Shallow)
    (borrow : FrameState) (frameBorrow : frame.extra.borrowTracker=some borrow)
    (global : GlobalState) (enabled : machine.borrowTracker=some ⟨global,.FnEntry⟩)
    (fresh : global.nextPointerTag.value<18446744073709551615)
    (id : AllocId) (root : BorTag) (base offset : UInt64) (nonnull : base+offset≠0)
    (cachedBase : machine.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩)
    (distinct : root≠global.nextPointerTag)
    (info : AllocationInfo) (infoEq : machine.memory.getAllocInfo id=.ok info) (dataKind : info.kind=.liveData)
    (converted : Allocation Provenance Unit) (after : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (afterGhost : after.user.payload.ghost=true)
    (metadata : machine.user.payload.payload.user.types.metadata=PreparedReflection.actual.runtime)
    (notConstructed : machine.user.payload.payload.user.types.entries.any (·.value.ty==4)=false)
    (view : RuntimeStackPlace Provenance)
    (destination : view.toRuntimePlace=LocalPlaces.localRuntimePlace frames.size frame localId reference)
    (ensure :
      let value:=(RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete id root) (Size.ofBytes (base+offset))) 0 reference).imm
      let copied:=ConcreteEmptyReferenceArgumentCopy.copiedFrame frame localId value valid
      let active:={machine with user:={machine.user with payload:={machine.user.payload with ghost:=true}}}
      let registered:=registeredState frames copied borrow (allocatedMachine active ⟨global,.FnEntry⟩ fresh)
        (allocatedTracker ⟨global,.FnEntry⟩ fresh) id global.nextPointerTag
      (config options remaining span).retag.ensureTreeExtra id registered=.ok () (materialized registered after id root converted)) :
    let value:=(RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id root) (Size.ofBytes (base+offset))) 0 reference).imm
    let updated:=(RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes (base+offset))) 0 reference).imm
    let copied:=ConcreteEmptyReferenceArgumentCopy.copiedFrame frame localId value valid
    let afterFrame:=registeredFrame copied borrow id global.nextPointerTag
    let final:=CurrentCallEmptyMaterializedBorrow.completed
      (materialized (registeredState frames copied borrow
        (allocatedMachine {machine with user:={machine.user with payload:={machine.user.payload with ghost:=true}}} ⟨global,.FnEntry⟩ fresh)
        (allocatedTracker ⟨global,.FnEntry⟩ fresh) id global.nextPointerTag) after id root converted)
      id ⟨.machine .global,converted.mapExtra (fun _=>BorrowTree.new root converted.byteSize)⟩
      (TypedRetagConcreteEmpty.lazyTree root global.nextPointerTag converted.byteSize.bytes)
    (ExecutionMachine.callHooks (config options (remaining+1) span) limits).copyAllowTransmute ()
      ⟨.immediate value,reference⟩ view (Storage.withCurrent frames frame machine)=
      .ok () (Storage.withCurrent frames {afterFrame with locals:=(afterFrame.locals.set localId
        {value:=.live (.immediate updated),layout:=(afterFrame.locals[localId]'(by simpa [afterFrame,copied,ConcreteEmptyReferenceArgumentCopy.copiedFrame,registeredFrame,TypedRetagEntry.frameWithBorrow] using valid)).layout}
        (by simpa [afterFrame,copied,ConcreteEmptyReferenceArgumentCopy.copiedFrame,registeredFrame,TypedRetagEntry.frameWithBorrow] using valid))}
        {final.machine with user:={final.machine.user with payload:={final.machine.user.payload with ghost:=false}}}) := by
  dsimp only
  let value:=(RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id root) (Size.ofBytes (base+offset))) 0 reference).imm
  let copied:=ConcreteEmptyReferenceArgumentCopy.copiedFrame frame localId value valid
  let active:={machine with user:={machine.user with payload:={machine.user.payload with ghost:=true}}}
  let registered:=registeredState frames copied borrow (allocatedMachine active ⟨global,.FnEntry⟩ fresh)
    (allocatedTracker ⟨global,.FnEntry⟩ fresh) id global.nextPointerTag
  let installed:=materialized registered after id root converted
  let entry : LocalAllocation Provenance BorrowTree MiriMemoryKind:=⟨.machine .global,converted.mapExtra (fun _=>BorrowTree.new root converted.byteSize)⟩
  let final:=CurrentCallEmptyMaterializedBorrow.completed installed id entry (TypedRetagConcreteEmpty.lazyTree root global.nextPointerTag converted.byteSize.bytes)
  let afterFrame:=registeredFrame copied borrow id global.nextPointerTag
  have present : installed.machine.memory.live.find? (fun row=>row.1==id)=some (id,entry):=
    MemoryCopyBridge.live_lookup_replaced after.memory id entry
  have postValid : localId<copied.locals.size:=by simpa only [copied,ConcreteEmptyReferenceArgumentCopy.copiedFrame,Array.size_set] using valid
  have postLive : copied.locals[localId].value=.live (.immediate value):=by simp [copied,ConcreteEmptyReferenceArgumentCopy.copiedFrame]
  have postCached : copied.locals[localId].layout=some reference:=by simpa only [copied,ConcreteEmptyReferenceArgumentCopy.copiedFrame,Array.getElem_set_self] using cached
  have driver:=CurrentCallEmptyMaterializedPointer.retag_pointer options remaining span ctx actualPointers cmp dynamicFuel dynamicEq
    frames copied borrow frameBorrow active ⟨global,.FnEntry⟩ enabled fresh id root base offset cachedBase distinct info infoEq dataKind installed entry converted.byteSize.bytes
    ensure present rfl metadata notConstructed
  have afterState : final=Storage.withCurrent frames afterFrame final.machine:=rfl
  change _=EStateM.Result.ok _ final at driver
  rw [afterState] at driver
  have checked:=CurrentCallEmptyValidateOfRetag.validate_runtime options remaining span ctx debug cmp dynamicFuel validityFuel dynamicEq
    id root global base offset nonnull frames copied machine localId postValid postLive postCached ghost shallow enabled afterFrame final.machine rfl rfl afterGhost driver metadata notConstructed
  apply ReferenceArgumentCopy.copy_with_nested_validation options limits remaining span debug frames frame machine localId old value valid live cached noClocks ghost shallow view destination _
  rw [validationEq]
  exact checked
end
end DuplicatePrefix.CurrentCallEmptyMaterializedCopy
