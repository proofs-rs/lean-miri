import duplicate_prefix.CurrentCallLazyPositiveEnsure

/-! Cached concrete-root mutable MEMORY branch only. The current descriptor
payload is authoritative here; no fixed imported-source identity or pre-ensure
borrow tree is invented. Cache misses and other provenance branches remain open. -/
namespace DuplicatePrefix.CurrentCallLazyCurrentDescriptor
open Miri Miri.ABI Miri.Memory Miri.Input Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts GeneralRangeMapState GeneralRangeMapOrigins OrdinaryBorrowAuthority
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
namespace Content
abbrev Fragment := CandidateFreezeContentResources.Fragment
end Content
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- Latent content entitlement, independently of writability and before any
root tree exists. The Bool fragment is the SAME current interpretation used by
B; its composition with source contents is explicit. -/
structure License (data : Identities) (sourceId : AllocId) (offset len : UInt64)
    (sourceOwner boolOwner : Nat) (boolId : AllocId) (boolOffset : Nat) where
  contents : Content.Fragment
  composable : CandidateFreezeContentResources.Composable contents data.interpretation.content
  source : ∀ byte, contents byte sourceOwner=some ⟨.mut,.active⟩ ↔
    Window sourceId offset.toNat len.toNat byte
  bool : ∀ byte, data.interpretation.content byte boolOwner=some ⟨.ret,.active⟩ ↔
    Window boolId boolOffset 1 byte

/-- Physical payload correspondence and cached representation facts. These
are not a successful ensure/retag premise. Only CURRENT findGlobal? is used. -/
structure Ready (options : EvalConfigurationCore.Options) (before : RootState)
    (tracker : MachineHooks.BorrowState) (id : AllocId) (root : BorTag)
    (source : Allocation CtfeProvenance Unit) (base offset len : UInt64)
    (argument : Pointer Provenance) : Prop where
  descriptor : before.machine.memory.findGlobal? id=some
    ⟨id,.memory,source.byteSize,source.align,source.mutability,some (.memory source)⟩
  argument : argument=Pointer.new (.concrete id root) (Size.ofBytes (base+offset))
  supported : GlobalSupportedImage.Supported source PreparedReflection.actual.compiler.runtime.target
    before.machine.memory tracker.global.rootPointerTags before.machine.user.addresses.baseAddr
  enabled : before.machine.borrowTracker=some tracker
  rootCached : tracker.global.rootTag? id=some root
  race : before.machine.dataRace=none
  noExtras : (before.machine.user.payload.payload.user.runtime.extras.allocations.any (fun row=>row.1==id))=false
  absent : before.machine.memory.live.find? (fun row=>row.1==id)=none
  cached : before.machine.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩
  addressRoom : base.toNat+source.len<2^64
  nonnull : base+offset≠0
  window : DuplicatePrefixSliceStorage.Positive source.initializationMask source.byteSize.bytes offset len
  storage : source.len=source.byteSize.bytes.toNat
  mutable : source.mutability=.Mut
  rootBelow : root.value.toNat<tracker.global.nextPointerTag.value.toNat
  protectors : ∀ row∈tracker.global.protectedTags.entries,row.1.value.toNat<tracker.global.nextPointerTag.value.toNat

private theorem filter_absent {K U : Type} (before : MachineHooks.MachineState K U) (id : AllocId)
    (absent : before.memory.live.find? (fun row=>row.1==id)=none) :
    before.memory.live.filter (fun row=>row.1!=id)=before.memory.live := by
  apply Array.filter_eq_self.mpr
  intro row member
  simpa using Array.find?_eq_none.mp absent row member

private theorem old_present (options : EvalConfigurationCore.Options) (before : Before)
    (id : AllocId) (allocation : Allocation Provenance BorrowTree)
    (absent : before.memory.live.find? (fun row=>row.1==id)=none)
    (other : AllocId) (old : Allocation Provenance BorrowTree)
    (present : Present (ActualWorld before) other old) :
    Present (ActualWorld (GlobalDataOnlyMaterialize.cached (GlobalDataOnlyActualConfig.extras options)
      before id .global allocation)) other old := by
  unfold Present ActualWorld at present ⊢
  simp only [GlobalDataOnlyMaterialize.cached,filter_absent before id absent]
  simpa only [Array.map_push,Array.toList_push,List.mem_append,List.mem_singleton] using Or.inl present

private theorem old_issued (options : EvalConfigurationCore.Options) (before : Before)
    (tracker : MachineHooks.BorrowState) (id : AllocId) (allocation : Allocation Provenance BorrowTree)
    (absent : before.memory.live.find? (fun row=>row.1==id)=none)
    {other old completion grant} (issued : SpatialDelegation before tracker other old completion grant) :
    SpatialDelegation (GlobalDataOnlyMaterialize.cached (GlobalDataOnlyActualConfig.extras options)
      before id .global allocation) tracker other old completion grant := by
  induction issued with
  | allocated cap => exact .allocated ⟨old_present options before id allocation absent _ _ cap.live,
      cap.extent,cap.treeExtent,cap.rootSlot,cap.rootNode⟩
  | concrete _ path ih => exact .concrete ih path
  | @wildcard origin root originNode rootNode earlier position originRoot prior originAt exposed rootAt parentless older earlierPosition earlierAt rootSlot path edge ih =>
    exact .wildcard originNode rootNode earlier position originRoot ih originAt exposed rootAt parentless older earlierPosition earlierAt rootSlot path edge

private def old_window (options : EvalConfigurationCore.Options) (before : Before)
    (tracker : MachineHooks.BorrowState) (id : AllocId) (allocation : Allocation Provenance BorrowTree)
    (absent : before.memory.live.find? (fun row=>row.1==id)=none)
    {data owner other offset length mode} (B : UniformWindow before tracker data owner other offset length mode) :
    UniformWindow (GlobalDataOnlyMaterialize.cached (GlobalDataOnlyActualConfig.extras options)
      before id .global allocation) tracker data owner other offset length mode where
  loan:=B.loan;pointer:=B.pointer;allocation:=B.allocation;precise:=B.precise
  loanAt:=B.loanAt;pointerAt:=B.pointerAt;pointerId:=B.pointerId
  present:=old_present options before id allocation absent _ _ B.present
  preciseAt:=B.preciseAt;binding:=B.binding;issued:=old_issued options before tracker id allocation absent B.issued
  parents:=B.parents;window:=B.window

/-- Execute the real ensure ONCE on the original caller. The source license is
retained, the exact converted root obtains capability/authority, and the SAME
current Bool window survives in that actual post-world. -/
theorem ensure (options : EvalConfigurationCore.Options) (choice : Unit) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (before : RootState) (tracker : MachineHooks.BorrowState)
    (id : AllocId) (root : BorTag) (source : Allocation CtfeProvenance Unit)
    (base offset len : UInt64) (argument : Pointer Provenance)
    (ready : Ready options before tracker id root source base offset len argument)
    {data sourceOwner boolOwner boolId boolOffset}
    (license : License data id offset len sourceOwner boolOwner boolId boolOffset)
    (B : UniformWindow before.machine tracker data boolOwner boolId boolOffset 1 .ret) :
    ∃ converted : Allocation Provenance Unit, GlobalAllocationAttributes.Attributes source converted ∧
    let allocation := converted.mapExtra (fun _=>BorrowTree.new root source.byteSize)
    let after := GlobalDataOnlyMaterialize.cached (GlobalDataOnlyActualConfig.extras options) before.machine id .global allocation
    (PreparedContracts.actualConfig options choice remaining span).retag.ensureTreeExtra id before=.ok () {before with machine:=after} ∧
    after.borrowTracker=before.machine.borrowTracker ∧ after.user.addresses=before.machine.user.addresses ∧
    id≠boolId ∧ AllocationCapability after tracker id allocation ∧
    DuplicatePrefixBorrowContract.RuntimeFacts allocation.extra tracker.global ∧
    PointerBinds allocation ⟨id,argument,allocationRoot⟩ ∧
    CandidateCallBindings.WindowBinding after argument id offset.toNat len.toNat ∧
    DuplicatePrefixSliceStorage.Positive allocation.initializationMask allocation.byteSize.bytes offset len ∧
    allocation.mutability=.Mut ∧
    CandidateFreezeContentResources.Valid (CandidateFreezeContentResources.union license.contents data.interpretation.content) ∧
    (∃ next : UniformWindow after tracker data boolOwner boolId boolOffset 1 .ret,
      next.pointer=B.pointer ∧ next.allocation=B.allocation ∧ next.precise=B.precise) ∧
    (∀ completion, SpatialDelegation after tracker id allocation completion allocationRoot ∧
      OwnedOn (S05CompletedAncestryReadMutable.Authority allocation.extra completion tracker.global.protectedTags allocationRoot)
        offset (offset+len) allocation.extra.locations ∧
      ∀ byte,CandidateCurrentGrantResources.Embeds allocation tracker.global.protectedTags completion allocationRoot byte .exclusive) := by
  obtain ⟨converted,attributes,actual,live,cap,runtime,binding,window,positive,mutable,resources⟩ :=
    CurrentCallLazyPositiveEnsure.ensure options choice remaining span before tracker id root source
      ready.supported ready.enabled ready.rootCached ready.race ready.noExtras ready.absent
      (Or.inl ready.descriptor) base offset len ready.cached ready.addressRoom ready.nonnull ready.window ready.storage ready.mutable ready.rootBelow ready.protectors
  have different : id≠boolId := by
    intro equal
    have present:=B.present
    unfold Present ActualWorld at present
    rw [Array.toList_map] at present
    obtain ⟨row,member,rowEq⟩:=List.mem_map.mp present
    have absent:=Array.find?_eq_none.mp ready.absent row (Array.mem_toList_iff.mp member)
    have rowId : row.1=boolId:=congrArg Prod.fst rowEq
    simp [rowId,equal] at absent
  refine ⟨converted,attributes,actual,by rfl,by rfl,different,cap,runtime,?_,?_,positive,mutable,
    CandidateFreezeContentResources.union_valid _ _ license.composable,?_,resources⟩
  · rw [ready.argument];exact binding
  · rw [ready.argument];exact window
  · exact ⟨old_window options before.machine tracker id _ ready.absent B,rfl,rfl,rfl⟩

end
end DuplicatePrefix.CurrentCallLazyCurrentDescriptor
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallLazyCurrentDescriptor" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved lazy current descriptor dependency {dependency}"
