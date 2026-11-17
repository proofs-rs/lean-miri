import duplicate_prefix.CurrentCallOrdinaryInput
import duplicate_prefix.CurrentCallEmptyReturnWindow
namespace DuplicatePrefix.CurrentCallOrdinaryReturnLive
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CurrentCallOrdinaryInput CurrentCallSpatialCover
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section
/-- The live branch of the initial Bool backing supplies the operational
return-only window from its declared current family satisfaction. No source
family, whole completion, initialization bit or operation result is added. -/
structure Packet {options limits remaining span before argument len place}
    (input : OrdinaryInput options limits remaining span before argument len place) where
  physical : CandidateCurrentBoolUninitWrite.PhysicalWindow before place
  data : Identities
  B : UniformWindow before input.tracker data 0 physical.id physical.offset.toNat 1 .ret
  pointer : physical.pointer=B.pointer.value
  allocation : physical.entry.allocation=B.allocation
  binding : CandidateCallBindings.WindowBinding before physical.pointer physical.id physical.offset.toNat 1
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra input.tracker.global
  distinct : B.allocation.extra.roots.toList.Nodup
  ready : CurrentCallBoolProtection.WindowReady before physical.id physical.offset.toNat 1
  tagRoom : input.tracker.global.nextPointerTag.value.toNat+6<18446744073709551615
  nodeRoom : B.allocation.extra.nodes.size+1<65536
  dynamicPositive : 0<options.place.dynamicFuel
  validationPositive : 0<options.limits.validation
  dispatchPositive : 0<limits.callDispatch
  familyPointer : physical.pointer=input.returnFamily.value
  familyId : physical.id=input.returnFamily.allocation
  familyOffset : physical.offset=input.returnOffset

theorem form {options limits remaining span before argument len place}
    (input : OrdinaryInput options limits remaining span before argument len place)
    (liveRole : LiveRole before input.tracker input.returnFamily input.returnOffset 1 input.returnCapacity false) :
    Nonempty (Packet input) := by
  obtain ⟨entry,live,size,physical,cap,owned⟩:=liveRole
  obtain ⟨base,cached,range,address,nonnull,representation⟩:=input.returnRepresentation
  have bounds : input.returnOffset.toNat+1≤input.returnCapacity.toNat:=by
    have bound:=physical.2.2.1
    rw [size] at bound
    exact bound
  have bytes : entry.allocation.len=input.returnCapacity.toNat:=by rw [physical.1.1,size];rfl
  have binding : CandidateCallBindings.WindowBinding before input.returnFamily.value input.returnFamily.allocation input.returnOffset.toNat 1:=by
    refine ⟨entry,base,live,cached,physical.1.1,?_,?_,address,nonnull,?_⟩
    · rw [bytes];exact range
    · rw [bytes];exact bounds
    · cases provenance : input.returnFamily.value.provenance with
      | concrete id tag=>
        rw [provenance] at representation
        exact representation.1
      | wildcard=>
        rw [provenance] at representation
        simpa only [size] using representation
  have member : (input.returnFamily.allocation,entry)∈before.memory.live.toList:=Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live)
  have runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra input.tracker.global:=
    ⟨input.runtime.formed _ member,input.runtime.coherent _ member,input.runtime.possible _ member,input.resources.tagsBelow _ member⟩
  have order:=input.runtime.parent_order input.returnFamily.allocation entry live
  have distinct:=input.runtime.roots _ member
  obtain ⟨data,B,pointerB,allocationB,_,_,_,_⟩:=CurrentCallEmptyReturnWindow.current input.assignment input.returnOccurrence place input.returnFamily entry input.returnOffset.toNat
    ⟨input.returnBound,input.returnActual,input.returnLayout,owned⟩ input.returnEncoding live binding cap runtime order distinct
  have pointerAddress : input.returnFamily.value.offset.bytes=base+input.returnOffset:=by
    apply UInt64.toNat_inj.mp
    rw [address,UInt64.toNat_add,Nat.mod_eq_of_lt (by omega)]
  let P : CandidateCurrentBoolUninitWrite.PhysicalWindow before place:={
    pointer:=input.returnFamily.value,physicalPointer:=input.returnEncoding,layout:=input.returnLayout,aligned:=input.returnAligned,
    id:=input.returnFamily.allocation,entry:=entry,base:=base,offset:=input.returnOffset,capacity:=input.returnCapacity,
    live:=live,cachedBase:=cached,pointerAddress:=pointerAddress,bounds:=bounds,size:=size,bytes:=bytes,
    mutable:=physical.2.1,maskValid:=physical.1.2.1,maskLength:=physical.1.2.2.1.trans size,provenanceMap:=physical.1.2.2.2}
  have work : 64≤DuplicatePrefixCallSpecification.work before len:=by unfold DuplicatePrefixCallSpecification.work;omega
  refine ⟨{
    physical:=P
    data:=data
    B:=B
    pointer:=pointerB.symm
    allocation:=allocationB.symm
    binding:=binding
    runtime:=by rw [allocationB];exact runtime
    distinct:=by rw [allocationB];exact distinct
    ready:=input.returnReady ⟨entry,live⟩
    tagRoom:=by have room:=input.resources.tagRoom;omega
    nodeRoom:=by rw [allocationB];have room : entry.allocation.extra.nodes.size+16<65536:=input.resources.nodeRoom _ member;omega
    dynamicPositive:=by have fuel:=input.resources.dynamicFuel;omega
    validationPositive:=by have fuel:=input.resources.configuredFuel.2.2.2;omega
    dispatchPositive:=by have fuel:=input.resources.executionFuel.1;omega
    familyPointer:=rfl
    familyId:=rfl
    familyOffset:=rfl}⟩

end
end DuplicatePrefix.CurrentCallOrdinaryReturnLive
