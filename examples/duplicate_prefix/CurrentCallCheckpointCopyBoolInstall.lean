import duplicate_prefix.CurrentCallCheckpointBoolInstall
import duplicate_prefix.CurrentCallResourceCopyInstall
import duplicate_prefix.S02SameDestinationAcceptedCopyPhysical
namespace DuplicatePrefix.CurrentCallCheckpointCopyBoolInstall
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CurrentCallPostEntryCheckpoint GeneralRangeMapOrigins S05CompletedAncestryReadMutable
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- Actual copy bytes may change while the Bool bank and original destination
licence survive a locations-only borrow-tree update. -/
theorem install {before tracker place} (old : Return before tracker place)
    (post : Before) (updated : Allocation Provenance BorrowTree)
    (live : post.memory.live.find? (fun row=>row.1==old.id)=some (old.id,{old.physical.entry with allocation:=updated}))
    (addresses : post.user.addresses=before.user.addresses)
    (extras : post.user.payload.payload.user.runtime.extras=before.user.payload.payload.user.runtime.extras)
    (length : updated.len=old.window.allocation.len) (bytes : updated.byteSize=old.window.allocation.byteSize)
    (shape : updated.extra={old.window.allocation.extra with locations:=updated.extra.locations})
    (capacity : updated.extra.locations.size=old.window.allocation.extra.locations.size)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts updated.extra tracker.global)
    (physical : S02SameDestinationAcceptedCopyPhysical.Physical updated)
    (owned : OwnedOn (Authority updated.extra old.window.precise.completion tracker.global.protectedTags old.window.pointer.grant)
      old.physical.offset (old.physical.offset+1) updated.extra.locations)
    (activity : GeneralBorrowFreshActiveWithin.ActiveWithin updated.extra old.window.pointer.grant .Write old.physical.offset (old.physical.offset+1)) :
    ∃current : Return post tracker place,current.id=old.id ∧current.offset=old.offset ∧current.window.pointer=old.window.pointer ∧
      current.original=old.original ∧current.window.allocation=updated ∧current.window.precise=old.window.precise ∧current.node=old.node := by
  have present : Present (ActualWorld post) old.id updated:=by
    simp only [Present,ActualWorld,Array.toList_map]
    exact List.mem_map.mpr ⟨_,Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live),rfl⟩
  have parents : ParentInterpretation updated.extra old.window.precise.completion:=by
    rw [shape]
    exact CurrentCallCheckpointSharedBoolFrame.parents_locations _ _ old.window.parents _
  have endSmall : old.physical.offset.toNat+1<2^64:=by
    exact Nat.lt_of_le_of_lt old.physical.bounds old.physical.capacity.toNat_lt
  have endEq : (old.physical.offset+1).toNat=old.physical.offset.toNat+1:=by
    rw [UInt64.toNat_add,UInt64.toNat_one,Nat.mod_eq_of_lt endSmall]
  obtain ⟨Q,loan,pointer,allocation,precise⟩:=CurrentCallResourceCopyInstall.window old.window rfl post updated present length bytes shape capacity runtime parents
    old.physical.offset 1 old.physicalOffset rfl (by rw [endEq];omega) endEq owned
  have metadata : ∀query previous,old.window.allocation.extra.nodes.get query=some previous→∃changed,
      updated.extra.nodes.get query=some changed ∧changed.tag=previous.tag ∧changed.parent=previous.parent ∧changed.isExposed=previous.isExposed ∧
        changed.defaultInitialPermission=previous.defaultInitialPermission:=by
    intro query previous found
    exact ⟨previous,by rw [shape];exact found,rfl,rfl,rfl,rfl⟩
  have issued:=CurrentCallAllocationLicense.spatial old.originalIssued post tracker updated present rfl length bytes capacity
    (by intro position root found;rw [shape];exact found) metadata old.window.precise.completion (by intro query origin edge;exact edge)
  have originalBinding : PointerBinds updated old.original:=by
    obtain ⟨node,nodeAt,mapped,provenance⟩:=old.originalBinding
    exact ⟨node,by rw [shape];exact nodeAt,by rw [shape];exact mapped,provenance⟩
  have size : updated.byteSize=Size.ofBytes old.physical.capacity:=
    bytes.trans ((congrArg Allocation.byteSize old.physicalAllocation.symm).trans old.physical.size)
  have len : updated.len=old.physical.capacity.toNat:=
    length.trans ((congrArg Allocation.len old.physicalAllocation.symm).trans old.physical.bytes)
  let scalar : CurrentCallBoolScalarWrite.Window post place:={old.physical with
    entry:={old.physical.entry with allocation:=updated}
    live:=by rw [old.physicalId];exact live
    cachedBase:=by rw [addresses];exact old.physical.cachedBase
    size:=size,bytes:=len,mutable:=physical.mutable,maskValid:=physical.maskValid
    maskLength:=physical.maskLength.trans size,pointerBounds:=physical.pointerBounds}
  have binding : CandidateCallBindings.WindowBinding post old.physical.pointer old.id old.offset 1:=by
    obtain ⟨entry,base,oldLive,cached,byteLength,room,bounds,address,nonnull,provenance⟩:=old.binding
    have oldPhysical:=old.physical.live
    rw [old.physicalId] at oldPhysical
    have same : entry=old.physical.entry:=congrArg Prod.snd (Option.some.inj (oldLive.symm.trans oldPhysical))
    rw [same,old.physicalAllocation] at byteLength room bounds provenance
    refine ⟨{old.physical.entry with allocation:=updated},base,live,?_,?_,?_,?_,address,nonnull,?_⟩
    · rw [addresses];exact cached
    · rw [length,bytes];exact byteLength
    · rw [length];exact room
    · rw [length];exact bounds
    · rw [addresses,bytes];exact provenance
  let current : Return post tracker place:={
    data:=old.data,owner:=old.owner,id:=old.id,offset:=old.offset,window:=Q,physical:=scalar,
    physicalId:=old.physicalId,physicalOffset:=old.physicalOffset,
    physicalAllocation:=by change updated=Q.allocation;exact allocation.symm,
    binding:=binding,original:=old.original,originalId:=old.originalId,originalPointer:=old.originalPointer,
    originalIssued:=by rw [allocation,precise];exact issued,
    originalBinding:=by rw [allocation];exact originalBinding,
    edge:=by rw [pointer,precise];exact old.edge,
    runtime:=by rw [allocation];exact runtime,
    distinct:=by rw [allocation,shape];exact old.distinct,
    short:=by rw [allocation,shape];exact old.short,
    node:=old.node,nodeAt:=by rw [allocation,pointer,shape];exact old.nodeAt,
    leaf:=old.leaf,hidden:=old.hidden,
    activity:=by rw [allocation,pointer];exact activity,
    profile:=CurrentCallBoolProtection.WindowReady.transport old.profile extras}
  exact ⟨current,rfl,rfl,pointer,rfl,allocation,precise,rfl⟩
end
end DuplicatePrefix.CurrentCallCheckpointCopyBoolInstall
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointCopyBoolInstall" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved copied Bool installation dependency {dependency}"
