import duplicate_prefix.CurrentCallEmptyProtocolControl
import duplicate_prefix.CurrentCallEmptyEntrySourceData
import duplicate_prefix.ConcretePoolRootCopy
import duplicate_prefix.WildcardPoolHitRootCopy
import duplicate_prefix.S04ZeroConcreteRuntime
import duplicate_prefix.S04ZeroWildcardRuntime
import duplicate_prefix.GeneralBorrowFnEntryRegistrationRuntime

/-! Source-only zero-length LIVE argument copying. No source content family
or Bool window is used; append and vacant-slot reuse are both actual cases. -/
namespace DuplicatePrefix.CurrentCallEmptyLiveSourceCopy
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.DataStructures
open CandidateCurrentJointCall CanonicalConfigFacts ActualReferenceContext ActualReferenceMetadata
open RootFrameData EmptyRootArguments GeneralBorrowFnEntryRegistration
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
noncomputable section

structure Ready (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : Before) (tracker : MachineHooks.BorrowState) (frames : Array CompilerFrameContext.ActualFrame)
    (root : RootFrame) (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset : UInt64) where
  model : DuplicatePrefixCallModel.Model options remaining span before
  origins : DuplicatePrefixTypeCacheOrigins.Origins before.user.payload.payload.user.types
  enabled : before.borrowTracker=some tracker
  rootBorrow : root.frame.extra.borrowTracker=some {}
  present : before.memory.live.find? (fun row=>row.1==id)=some (id,entry)
  cached : before.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩
  nonzero : base+offset≠0
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global
  room : entry.allocation.extra.nodes.size+1≤4294967295
  fresh : tracker.global.nextPointerTag.value<18446744073709551615
  dynamicFuel : Nat
  validationFuel : Nat
  dynamicEq : options.place.dynamicFuel=dynamicFuel+1
  validationEq : options.limits.validation=validationFuel+1

def value (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (pointer : Pointer Provenance) : Immediate Provenance :=
  (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base pointer 0 reference).imm

variable {options : EvalConfigurationCore.Options} {remaining : Nat} {span : PreparedContracts.FixedSpanQuery}
variable {before : Before} {tracker : MachineHooks.BorrowState} {frames : Array CompilerFrameContext.ActualFrame}
variable {root : RootFrame} {id : AllocId} {entry : LocalAllocation Provenance BorrowTree MiriMemoryKind}
variable {base offset : UInt64}

structure Packet (limits : ExecutionMachine.Limits)
    (R : Ready options remaining span before tracker frames root id entry base offset) (original : Pointer Provenance) where
  tree : BorrowTree
  machine : Before
  copy : (ExecutionMachine.callHooks (config options (remaining+1) span) limits).copyAllowTransmute ()
    ⟨.immediate (value options remaining span original),reference⟩
    (LocalPlaces.localRuntimePlace frames.size (firstLive root).frame 1 reference).stackView
    (Storage.withCurrent frames (firstLive root).frame (ScopedFrame.entered before tracker .FnEntry))=
    .ok () (Storage.withCurrent frames
      (CurrentCallEmptyProtocolControl.sourceRoot root
        (value options remaining span (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))))
        (({} : FrameState).addProtector id tracker.global.nextPointerTag)).frame machine)
  machineEq : machine={before with
    borrowTracker:=some ⟨(registered tracker.global {} id R.fresh).1,.FnEntry⟩
    memory:=RetagEntry.updatedMemory before.memory id entry tree}
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree (registered tracker.global {} id R.fresh).1
  leaf : CurrentCallEmptyEntrySourceData.Leaf tree tracker.global.nextPointerTag
  growth : tree.nodes.size≤entry.allocation.extra.nodes.size+1

namespace Packet
variable {limits : ExecutionMachine.Limits} {R : Ready options remaining span before tracker frames root id entry base offset}
variable {original : Pointer Provenance}
theorem memory (P : Packet limits R original) : P.machine.memory=RetagEntry.updatedMemory before.memory id entry P.tree := by rw [P.machineEq]
theorem user (P : Packet limits R original) : P.machine.user=before.user := by rw [P.machineEq]
theorem threads (P : Packet limits R original) : P.machine.threads=before.threads := by rw [P.machineEq]
theorem race (P : Packet limits R original) : P.machine.dataRace=before.dataRace := by rw [P.machineEq]
theorem tracked (P : Packet limits R original) : P.machine.borrowTracker=some ⟨(registered tracker.global {} id R.fresh).1,.FnEntry⟩ := by rw [P.machineEq]
end Packet

private theorem frame_eq (root : RootFrame) (updated : Immediate Provenance) (id : AllocId) (tag : BorTag) :
    ConcreteEmptyRootCopy.changedFrame (firstLive root).frame 1 updated ((firstLive root).valid i1) {} id tag=
      (CurrentCallEmptyProtocolControl.sourceRoot root updated (({} : FrameState).addProtector id tag)).frame := rfl

private theorem pool_leaf {tree : BorrowTree} {parentTag tag : BorTag}
    (input : ConcreteEmptyPoolEntry.Input tree parentTag tag) : CurrentCallEmptyEntrySourceData.Leaf input.after tag := by
  obtain ⟨node,present,nodeTag,_,children,_,hidden⟩:=GeneralBorrowFreshMetadataChildSifa.node_fields
    input.stage input.parent .None input.index (GeneralBorrowFreshChild.child tag input.parent) input.stage_new
  have mapped : input.after.indexOfTag tag=some input.index := by
    unfold BorrowTree.indexOfTag
    rw [input.mapping_after]
    exact GeneralBorrowTagMap.pushed_get_new tree.tagMapping tag input.fresh input.index input.free
  refine ⟨input.index,node,mapped,present,nodeTag,children,hidden,?_⟩
  intro cursor valid
  have clean:=input.future_clean input.index input.clean cursor valid
  simp only [GeneralBorrowWildcardVirtualLeaf.effective,clean,Option.getD_none,TreeNode.defaultLocationState]

private theorem slot_leaf (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (clean : GeneralBorrowGcVacantClean.VacantClean tree) :
    CurrentCallEmptyEntrySourceData.Leaf (slot.after tag) tag := by
  refine ⟨slot.index,WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None,
    GeneralBorrowTagMap.pushed_get_new tree.tagMapping tag fresh slot.index slot.free,
    GeneralBorrowFreshLocation.get_same tree.nodes slot.index _,rfl,rfl,rfl,?_⟩
  intro cursor valid
  have empty:=clean slot.index slot.vacant cursor valid
  change ((tree.locations.entries[cursor].data.perms.get slot.index).getD _).accessed=false
  rw [empty];rfl

private theorem local_ready (root : RootFrame) :
    ((firstLive root).frame.locals[1]'((firstLive root).valid i1)).value=.live (.immediate .uninit) ∧
    ((firstLive root).frame.locals[1]'((firstLive root).valid i1)).layout=some reference := by
  constructor
  · simp only [firstLive,RootFrameData.live,RootFrameData.write,Array.getElem_set_self,i1]
  · simp only [firstLive,firstCache,RootFrameData.live,RootFrameData.write,RootFrameData.cache,RootFrameData.atSpan,
      LocalOperands.cachedLayoutFrame,Array.getElem_set_self,i1]

theorem concrete (limits : ExecutionMachine.Limits)
    (R : Ready options remaining span before tracker frames root id entry base offset)
    (parentTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : entry.allocation.extra.indexOfTag parentTag=some parent)
    (present : entry.allocation.extra.nodeAt parent=some parentNode) :
    Nonempty (Packet limits R (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset)))) := by
  let input:=ConcreteEmptyRuntimeEntry.form entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag
    R.runtime.formed parent parentNode tagged present (ConcreteEmptyRuntimeEntry.counter_fresh _ _ R.runtime.below) R.room
  let next:=(registered tracker.global {} id R.fresh).1
  obtain ⟨_,held,_,registeredRuntime,_,fresh⟩:=GeneralBorrowFnEntryRegistrationRuntime.prepare entry.allocation.extra tracker.global {} id R.fresh R.runtime
  have bound : tracker.global.nextPointerTag.value.toNat<next.nextPointerTag.value.toNat := by
    change tracker.global.nextPointerTag.value.toNat<(TypedRetagEmpty.successorTag tracker.global.nextPointerTag R.fresh).value.toNat
    rw [GenericFunctionEntryNumerics.successor_value];omega
  have heldTag : next.protectedTags.contains tracker.global.nextPointerTag=true := by unfold ProtectedTags.contains;rw [held];rfl
  have actual:=S04ZeroConcreteRuntime.construct entry.allocation.extra next registeredRuntime parentTag parent parentNode tagged present
    tracker.global.nextPointerTag fresh R.room bound heldTag offset
  have runtime : DuplicatePrefixBorrowContract.RuntimeFacts input.after next := by
    have rr:=actual.2.1;rw [input.child offset] at rr;exact rr
  have growth : input.after.nodes.size≤entry.allocation.extra.nodes.size+1 := by
    have g:=actual.2.2.2;rw [input.child offset] at g;exact g
  obtain ⟨ctx⟩:=(DuplicatePrefixCallModel.contexts options remaining span before R.model).1
  have copy:=ConcretePoolRootCopy.copy options limits remaining span ctx R.model.debugOff R.model.nullComparator
    R.dynamicFuel R.validationFuel R.dynamicEq R.validationEq id parentTag tracker.global base offset R.nonzero entry
    frames (firstLive root).frame (ScopedFrame.entered before tracker .FnEntry) 1 ((firstLive root).valid i1) .uninit
    (local_ready root).1 (local_ready root).2 (firstLive root).noClocks R.model.ghostOff R.model.shallow R.cached R.present
    {} R.rootBorrow rfl R.fresh input R.model.metadata
    (DuplicatePrefixTypeCacheOrigins.slice_not_constructed _ R.model.metadata R.origins)
    (LocalPlaces.localRuntimePlace frames.size (firstLive root).frame 1 reference).stackView rfl
  refine ⟨⟨input.after,ConcretePoolRootCopy.changedMachine (ScopedFrame.entered before tracker .FnEntry)
    tracker.global R.fresh id entry parentTag input,?_,rfl,runtime,pool_leaf input,growth⟩⟩
  simpa only [value,ConcretePoolRootCopy.changedFrame,frame_eq] using copy

theorem wildcard (limits : ExecutionMachine.Limits)
    (R : Ready options remaining span before tracker frames root id entry base offset)
    (mode : before.user.addresses.provenanceMode≠.strict)
    (geometry : WildcardGeneralHitReborrow.Geometry before.user.addresses.intToPtrMap (base+offset) base id entry.allocation.byteSize)
    (exposed : before.user.addresses.exposed.contains id=true) :
    Nonempty (Packet limits R (Pointer.new .wildcard (Size.ofBytes (base+offset)))) := by
  let slot : WildcardHitPoolRoot.Slot entry.allocation.extra:=WildcardHitPoolRoot.factory entry.allocation.extra
    R.runtime.formed.allocator.pool R.runtime.formed.allocator.accounting (by
      have balance:=R.runtime.formed.allocator.accounting
      unfold GeneralBorrowFreshStagePool.Accounting at balance
      have room:=R.room
      omega)
  let next:=(registered tracker.global {} id R.fresh).1
  obtain ⟨_,held,_,registeredRuntime,_,fresh⟩:=GeneralBorrowFnEntryRegistrationRuntime.prepare entry.allocation.extra tracker.global {} id R.fresh R.runtime
  have bound : tracker.global.nextPointerTag.value.toNat<next.nextPointerTag.value.toNat := by
    change tracker.global.nextPointerTag.value.toNat<(TypedRetagEmpty.successorTag tracker.global.nextPointerTag R.fresh).value.toNat
    rw [GenericFunctionEntryNumerics.successor_value];omega
  have heldTag : next.protectedTags.contains tracker.global.nextPointerTag=true := by unfold ProtectedTags.contains;rw [held];rfl
  have actual:=S04ZeroWildcardRuntime.construct entry.allocation.extra next registeredRuntime tracker.global.nextPointerTag fresh R.room bound heldTag offset
  have runtime : DuplicatePrefixBorrowContract.RuntimeFacts (slot.after tracker.global.nextPointerTag) next := by
    have rr:=actual.2.1;rw [slot.child tracker.global.nextPointerTag fresh offset] at rr;exact rr
  have growth : (slot.after tracker.global.nextPointerTag).nodes.size≤entry.allocation.extra.nodes.size+1 := by
    have g:=actual.2.2.2;rw [slot.child tracker.global.nextPointerTag fresh offset] at g;exact g
  obtain ⟨ctx⟩:=(DuplicatePrefixCallModel.contexts options remaining span before R.model).1
  have copy:=WildcardPoolHitRootCopy.copy options limits remaining span ctx R.model.debugOff R.model.nullComparator
    R.dynamicFuel R.validationFuel R.dynamicEq R.validationEq id tracker.global base offset R.nonzero entry
    frames (firstLive root).frame (ScopedFrame.entered before tracker .FnEntry) 1 ((firstLive root).valid i1) .uninit
    (local_ready root).1 (local_ready root).2 (firstLive root).noClocks R.model.ghostOff R.model.shallow R.cached R.present
    {} R.rootBorrow rfl R.fresh mode geometry exposed fresh slot R.model.metadata
    (DuplicatePrefixTypeCacheOrigins.slice_not_constructed _ R.model.metadata R.origins)
    (LocalPlaces.localRuntimePlace frames.size (firstLive root).frame 1 reference).stackView rfl
  refine ⟨⟨slot.after tracker.global.nextPointerTag,WildcardPoolHitRootCopy.changedMachine (ScopedFrame.entered before tracker .FnEntry)
    tracker.global R.fresh id entry slot,?_,rfl,runtime,slot_leaf _ slot _ fresh (DuplicatePrefixBorrowContract.vacant_clean R.runtime),growth⟩⟩
  simpa only [value,WildcardPoolHitRootCopy.changedFrame,frame_eq] using copy

end
end DuplicatePrefix.CurrentCallEmptyLiveSourceCopy
