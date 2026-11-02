import duplicate_prefix.CurrentCallOrdinaryEmptyCurrentState
import duplicate_prefix.CurrentCallOrdinarySameAllocationBool
import duplicate_prefix.CurrentCallConversionBoolPhase
namespace DuplicatePrefix.CurrentCallOrdinaryEmptyCurrentSameBool
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CurrentCallResourceNormalization CandidateCurrentJointCall CurrentCallOrdinaryInput CanonicalConfigFacts ActualReferenceContext ActualReferenceMetadata
open RootFrameData EmptyRootArguments TypedBorrowSteps ReferenceBorrowDriver
open CurrentCallOrdinaryEmptyCurrentState
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section
variable {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits} {remaining : Nat}
    {span : PreparedContracts.FixedSpanQuery} {before : Before} {argument : DuplicatePrefixSliceArgument.Argument}
    {place : MPlaceTy Provenance}
    (input : OrdinaryInput options limits remaining span before argument 0 place)
    (id : AllocId) (pointer : Pointer Provenance) (root : BorTag)
    (source : Allocation CtfeProvenance Unit)
    (externStatic : Miri.MIR.DefId→MachineAddress.M MiriMemoryKind CurrentCallConversionFiniteFold.Control (Pointer Provenance))
    (tail : List AllocId) (finalAddresses : Miri.Memory.AllocAddresses.GlobalAddressState) (finalTape : ExecutionChoices.Tape)
    (result : CurrentCallConversionFiniteFold.Result source PreparedReflection.actual.compiler.runtime.target.base
      (CurrentCallConversionActualEnsure.hooks options).address externStatic
      (CurrentCallOrdinaryEmptyCurrentCopy.registered input id pointer).machine
      (CurrentCallOrdinaryEmptyCurrentCopy.nextTracker input) tail (addressCharge before) 15 finalAddresses finalTape)
    (tree : BorrowTree)


theorem concrete
    (same : id=input.returnFamily.allocation)
    (latent : LatentRole before input.tracker input.returnFamily input.returnOffset 1 input.returnCapacity false)
    (current : CurrentPayload before id source)
    (cachedRoot : input.tracker.global.rootTag? id=some root)
    (base offset : UInt64)
    (cachedBase : before.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩)
    (older : root.value.toNat<input.tracker.global.nextPointerTag.value.toNat) :
    let qtree:=TypedRetagConcreteEmpty.lazyTree root input.tracker.global.nextPointerTag result.converted.byteSize.bytes
    let post:=closed options result.machine id root result.converted qtree result.global input.tracker.retagMode
    Nonempty (CurrentCallMaterializedRootBoolFrame.Packet post ⟨result.global,input.tracker.retagMode⟩ input.returnFamily result.converted qtree input.returnOffset place) := by
  dsimp only
  have data:=CurrentCallOrdinarySameAllocationBool.physical_data input latent source (by simpa only [same] using current)
    root (by simpa only [same] using cachedRoot) base (by simpa only [same] using cachedBase) result.converted result.attributes result.wellFormed
  have old : root.value<input.tracker.global.nextPointerTag.value:=by simpa only [UInt64.lt_iff_toNat_lt] using older
  apply CurrentCallMaterializedRootBoolFrame.concrete_zero _ _ input.returnFamily root input.tracker.global.nextPointerTag result.converted base input.returnOffset offset place data old
    (root_below input id pointer root source externStatic tail finalAddresses finalTape result older)
    (protectors input id pointer source externStatic tail finalAddresses finalTape result)
    (by change input.tracker.global.nextPointerTag.value.toNat<result.global.nextPointerTag.value.toNat;have h:=advanced input id pointer source externStatic tail finalAddresses finalTape result;omega)
    (held input id pointer source externStatic tail finalAddresses finalTape result) (.machine .global)
  · simpa only [←same] using live input id pointer root source externStatic tail finalAddresses finalTape result (TypedRetagConcreteEmpty.lazyTree root input.tracker.global.nextPointerTag result.converted.byteSize.bytes)
  · simpa only [←same] using CurrentCallOrdinaryEmptyCurrentState.base input id pointer root source externStatic tail finalAddresses finalTape result (TypedRetagConcreteEmpty.lazyTree root input.tracker.global.nextPointerTag result.converted.byteSize.bytes) base cachedBase
  · simpa only [←same] using registry input id pointer root source externStatic tail finalAddresses finalTape result (TypedRetagConcreteEmpty.lazyTree root input.tracker.global.nextPointerTag result.converted.byteSize.bytes)
  · simpa only [←same] using root_cache input id pointer root source externStatic tail finalAddresses finalTape result cachedRoot

theorem wildcard
    (same : id=input.returnFamily.allocation)
    (latent : LatentRole before input.tracker input.returnFamily input.returnOffset 1 input.returnCapacity false)
    (current : CurrentPayload before id source)
    (cachedRoot : input.tracker.global.rootTag? id=some root)
    (base offset : UInt64)
    (cachedBase : before.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩)
    (older : root.value.toNat<input.tracker.global.nextPointerTag.value.toNat) :
    let qtree:=CurrentCallEmptyMaterializedWildcard.finalTree root input.tracker.global.nextPointerTag result.converted.byteSize
    let post:=closed options result.machine id root result.converted qtree result.global input.tracker.retagMode
    Nonempty (CurrentCallMaterializedRootBoolFrame.Packet post ⟨result.global,input.tracker.retagMode⟩ input.returnFamily result.converted qtree input.returnOffset place) := by
  dsimp only
  have data:=CurrentCallOrdinarySameAllocationBool.physical_data input latent source (by simpa only [same] using current)
    root (by simpa only [same] using cachedRoot) base (by simpa only [same] using cachedBase) result.converted result.attributes result.wellFormed
  have old : root.value<input.tracker.global.nextPointerTag.value:=by simpa only [UInt64.lt_iff_toNat_lt] using older
  apply CurrentCallMaterializedRootBoolFrame.wildcard_zero _ _ input.returnFamily root input.tracker.global.nextPointerTag result.converted base input.returnOffset offset place data old
    (root_below input id pointer root source externStatic tail finalAddresses finalTape result older)
    (protectors input id pointer source externStatic tail finalAddresses finalTape result)
    (by change input.tracker.global.nextPointerTag.value.toNat<result.global.nextPointerTag.value.toNat;have h:=advanced input id pointer source externStatic tail finalAddresses finalTape result;omega)
    (held input id pointer source externStatic tail finalAddresses finalTape result) (.machine .global)
  · simpa only [←same] using live input id pointer root source externStatic tail finalAddresses finalTape result (CurrentCallEmptyMaterializedWildcard.finalTree root input.tracker.global.nextPointerTag result.converted.byteSize)
  · simpa only [←same] using CurrentCallOrdinaryEmptyCurrentState.base input id pointer root source externStatic tail finalAddresses finalTape result (CurrentCallEmptyMaterializedWildcard.finalTree root input.tracker.global.nextPointerTag result.converted.byteSize) base cachedBase
  · simpa only [←same] using registry input id pointer root source externStatic tail finalAddresses finalTape result (CurrentCallEmptyMaterializedWildcard.finalTree root input.tracker.global.nextPointerTag result.converted.byteSize)
  · simpa only [←same] using root_cache input id pointer root source externStatic tail finalAddresses finalTape result cachedRoot


def normalized {post tracker family converted qtree offset place}
    (P : CurrentCallMaterializedRootBoolFrame.Packet post tracker family converted qtree offset place) :
    UniformWindow post tracker (CurrentCallMaterializedRootBoolFrame.identities family P.completion) 0
      P.physical.id P.physical.offset.toNat 1 .ret := {
  loan:=P.window.loan,pointer:=P.window.pointer,allocation:=P.window.allocation,precise:=P.window.precise
  loanAt:=P.window.loanAt,pointerAt:=P.window.pointerAt,pointerId:=by rw [P.physicalId];exact P.window.pointerId
  present:=by rw [P.physicalId];exact P.window.present
  preciseAt:=by rw [P.physicalId];exact P.window.preciseAt
  binding:=P.window.binding,issued:=by rw [P.physicalId];exact P.window.issued,parents:=P.window.parents
  window:=by intro byte hit;apply P.window.window;simpa only [P.physicalId,P.physicalOffset] using hit}

def live_data {post tracker family converted qtree offset place}
    (P : CurrentCallMaterializedRootBoolFrame.Packet post tracker family converted qtree offset place)
    (frame : CompilerFrameContext.ActualFrame) (borrow : FrameState)
    (model : DuplicatePrefixCallModel.Model options remaining span post)
    (enabled : post.borrowTracker=some tracker) (frameBorrow : frame.extra.borrowTracker=some borrow)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (short : qtree.nodes.size+1<65536) :
    CurrentCallConversionBoolPhase.LiveData post tracker frame borrow place := {
  data:=CurrentCallMaterializedRootBoolFrame.identities family P.completion,owner:=0,physical:=P.physical,window:=normalized P,enabled:=enabled,frameBorrow:=frameBorrow
  pointer:=by change P.physical.pointer=P.window.pointer.value;rw [P.physicalPointer,P.pointer];rfl
  allocation:=P.physicalAllocation.trans P.allocation.symm
  runtime:=by change DuplicatePrefixBorrowContract.RuntimeFacts P.window.allocation.extra tracker.global;rw [P.allocation];exact P.runtime
  binding:=by simpa only [P.physicalOffset] using P.binding
  distinct:=by change P.window.allocation.extra.roots.toList.Nodup;rw [P.allocation];exact P.distinct
  fresh:=fresh,short:=by change P.window.allocation.extra.nodes.size+1<65536;rw [P.allocation];exact short
  ghost:=model.ghostOff,race:=model.noDataRace,backend:=model.noBackend
  ready:=by simpa only [P.physicalOffset] using P.ready}

end
end DuplicatePrefix.CurrentCallOrdinaryEmptyCurrentSameBool
