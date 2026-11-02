import duplicate_prefix.CurrentCallAllocationLicense
import duplicate_prefix.CurrentCallBoolTreeWindow
import duplicate_prefix.CurrentCallBoolProtection

namespace DuplicatePrefix.CurrentCallLiveBoolTransport
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentBoolUninitWrite CurrentCallResourceNormalization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- Preserving the selected cached root suffices for an unchanged allocation's
licence. No complete cache or global-state equality is required. -/
theorem spatial {before oldTracker id allocation C grant}
    (old : SpatialDelegation before oldTracker id allocation C grant)
    (after : Before) (next : MachineHooks.BorrowState)
    (present : Present (ActualWorld after) id allocation)
    (rootHit : ∀tag,oldTracker.global.rootTag? id=some tag→next.global.rootTag? id=some tag) :
    SpatialDelegation after next id allocation C grant := by
  obtain ⟨root,rootAt,parent,permission,cached⟩:=old.capability.rootNode
  have rootEq : next.global.rootTag? id=oldTracker.global.rootTag? id:=
    (rootHit root.tag cached).trans cached.symm
  exact CurrentCallAllocationLicense.spatial old after next allocation present rootEq rfl rfl rfl
    (fun _ _ found=>found) (fun _ node found=>⟨node,found,rfl,rfl,rfl,rfl⟩) C (fun _ _ edge=>edge)

private theorem live_id {memory : MemoryState Provenance BorrowTree MiriMemoryKind} {oldId newId : AllocId}
    {entry : LocalAllocation Provenance BorrowTree MiriMemoryKind} (equal : oldId=newId)
    (live : memory.live.find? (fun row=>row.1==oldId)=some (oldId,entry)) :
    memory.live.find? (fun row=>row.1==newId)=some (newId,entry):=by cases equal;exact live

/-- Only the selected physical pointer's wildcard query is framed. It is the
ORIGINAL destination pointer, which may differ from a protected child's bits. -/
def WildcardQuery (after : Before) {before place} (physical : PhysicalWindow before place) : Prop :=
  physical.pointer.provenance=.wildcard→
    after.user.addresses.provenanceMode≠Miri.Memory.AllocAddresses.ProvenanceMode.strict ∧
    after.user.addresses.exposed.contains physical.id=true ∧
    WildcardGeneralHitReborrow.Geometry after.user.addresses.intToPtrMap physical.pointer.offset.bytes physical.base physical.id physical.entry.allocation.byteSize

structure Result {before oldTracker data owner id offset place}
    (W : UniformWindow before oldTracker data owner id offset 1 .ret)
    (oldPhysical : PhysicalWindow before place) (after : Before) (next : MachineHooks.BorrowState) where
  window : UniformWindow after next data owner id offset 1 .ret
  loan : window.loan=W.loan
  pointer : window.pointer=W.pointer
  allocation : window.allocation=W.allocation
  precise : window.precise=W.precise
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts window.allocation.extra next.global
  physical : PhysicalWindow after place
  physicalPointer : physical.pointer=oldPhysical.pointer
  physicalId : physical.id=oldPhysical.id
  physicalOffset : physical.offset=oldPhysical.offset
  physicalEntry : physical.entry=oldPhysical.entry
  physicalCapacity : physical.capacity=oldPhysical.capacity
  binding : CandidateCallBindings.WindowBinding after physical.pointer physical.id physical.offset.toNat 1
  ready : CurrentCallBoolProtection.WindowReady after physical.id physical.offset.toNat 1

/-- Transport a genuine current LIVE Bool through a converter that retains
its actual heap row. The caller has already handled q registration and quiet
permissions; conversion may grow address/root registries and change mode. -/
theorem transport {before oldTracker data owner id offset place}
    (W : UniformWindow before oldTracker data owner id offset 1 .ret)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra oldTracker.global)
    (physical : PhysicalWindow before place) (physicalId : physical.id=id)
    (_physicalOffset : physical.offset.toNat=offset) (allocation : physical.entry.allocation=W.allocation)
    (binding : CandidateCallBindings.WindowBinding before physical.pointer physical.id physical.offset.toNat 1)
    (ready : CurrentCallBoolProtection.WindowReady before physical.id physical.offset.toNat 1)
    (after : Before) (next : MachineHooks.BorrowState)
    (live : after.memory.live.find? (fun row=>row.1==physical.id)=before.memory.live.find? (fun row=>row.1==physical.id))
    (flags : next.global.protectedTags=oldTracker.global.protectedTags)
    (counter : oldTracker.global.nextPointerTag.value.toNat≤next.global.nextPointerTag.value.toNat)
    (rootHit : ∀tag,oldTracker.global.rootTag? id=some tag→next.global.rootTag? id=some tag)
    (base : after.user.addresses.baseAddr.find? (fun row=>row.allocId==physical.id)=
      before.user.addresses.baseAddr.find? (fun row=>row.allocId==physical.id))
    (extras : after.user.payload.payload.user.runtime.extras.allocations.find? (fun row=>row.1==physical.id)=
      before.user.payload.payload.user.runtime.extras.allocations.find? (fun row=>row.1==physical.id))
    (wild : WildcardQuery after physical) :
    Nonempty (Result W physical after next) := by
  have physicalLive:=live.trans physical.live
  have windowLive:=live_id physicalId physicalLive
  have present : Present (ActualWorld after) id W.allocation:=by
    simp only [Present,ActualWorld,Array.toList_map]
    refine List.mem_map.mpr ⟨_,Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some windowLive),?_⟩
    simp only [allocation]
  have issued:=spatial W.issued after next present rootHit
  let Q : UniformWindow after next data owner id offset 1 .ret:={W with
    present:=present,issued:=issued,window:=by
      intro byte inside
      have old:=W.window byte inside
      rw [flags]
      exact old}
  have nextRuntime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra next.global:=by
    refine ⟨by rw [flags];exact runtime.formed,by rw [flags];exact runtime.coherent,runtime.possible,⟨?_,?_⟩⟩
    · intro row member;exact Nat.lt_of_lt_of_le (runtime.below.mapping row member) counter
    · intro row member;rw [flags] at member;exact Nat.lt_of_lt_of_le (runtime.below.protectors row member) counter
  let nextPhysical : PhysicalWindow after place:={physical with
    live:=physicalLive,cachedBase:=base.trans physical.cachedBase}
  obtain ⟨entry,address,entryLive,cached,storage,room,bounds,pointerAddress,nonnull,provenance⟩:=binding
  have entryEq : entry=physical.entry:=congrArg Prod.snd (Option.some.inj (entryLive.symm.trans physical.live))
  have addressEq : address=physical.base:=congrArg (fun row : Miri.Memory.AllocAddresses.BaseAddressEntry=>row.address)
    (Option.some.inj (cached.symm.trans physical.cachedBase))
  subst entry
  subst address
  have nextBinding : CandidateCallBindings.WindowBinding after physical.pointer physical.id physical.offset.toNat 1:=by
    refine ⟨physical.entry,physical.base,physicalLive,base.trans physical.cachedBase,storage,room,bounds,pointerAddress,nonnull,?_⟩
    cases prov : physical.pointer.provenance with
    | concrete supplied tag=>simpa only [prov] using provenance
    | wildcard=>simpa only [prov] using wild prov
  obtain ⟨sync,selected,outside⟩:=ready
  exact ⟨{
    window:=Q,loan:=rfl,pointer:=rfl,allocation:=rfl,precise:=rfl,runtime:=nextRuntime,
    physical:=nextPhysical,physicalPointer:=rfl,physicalId:=rfl,physicalOffset:=rfl,physicalEntry:=rfl,physicalCapacity:=rfl,
    binding:=nextBinding,ready:=⟨sync,extras.trans selected,outside⟩}⟩
end
end DuplicatePrefix.CurrentCallLiveBoolTransport
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallLiveBoolTransport" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved LIVE Bool transport dependency {dependency}"
