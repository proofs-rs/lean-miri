import duplicate_prefix.GeneralBorrowRawRootPrefixFrame
namespace DuplicatePrefix.GeneralBorrowRawRootInitialSlot
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext GenericFunctionEntryState
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
abbrev Initial := GeneralBorrowRawRootZeroEntry.Initial
abbrev slotTag (s : Initial) : BorTag := (next s.tracker s.fresh).global.nextPointerTag

structure Data (s : Initial) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) where
  slot : LocalAllocation Provenance BorrowTree MiriMemoryKind
  present : machine.memory.live.find? (fun row => row.1 == s.slotId) = some (s.slotId,slot)
  tree : slot.allocation.extra = PhysicalMachineWrite.slotTree s.slotRoot (slotTag s) 1 true
  size : slot.allocation.byteSize = Size.ofBytes 1
  storage : slot.allocation.len = 1
  mask : slot.allocation.initializationMask = InitMask.new (Size.ofBytes 1) false
  provenance : slot.allocation.provenanceMap = ProvenanceMap.new
  mutable : slot.allocation.mutability = .Mut
  rootFree : (GeneralBorrowRawRootPrefixResources.bufferGlobal s).protectedTags.contains s.slotRoot = false
  childHeld : (GeneralBorrowRawRootPrefixResources.bufferGlobal s).protectedTags.contains (slotTag s) = true
  distinct : s.slotRoot ≠ slotTag s

/-- The ORIGINAL initialized heap supplies the independent fixed return slot.
This internal determinism adapter consumes the already proved initializer;
whole-call theorems discharge it from their original input. -/
theorem of_call (s : Initial) (n : UInt64) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (call : GeneralBorrowRawRootPositivePrefix.ActualCall s n frame machine) : Nonempty (Data s machine) := by
  obtain ⟨initialized,post,release,actual,tracked,flags,location,size,body,countSlot,borrow,releaseId,releaseTag,releaseSlotId,
    releaseRoot,releaseChild,slotSize,slotLen,slotMask,slotProv,slotMut,frameEq,machineEq⟩ :=
    GeneralBorrowRawRootInitialize.initializes s n
  have same : machine = post := by
    have equality := congrArg (fun result : EStateM.Result StepError RootState Unit =>
      match result with | .ok _ state => some state.machine | _ => none) (call.symm.trans actual)
    exact Option.some.inj equality
  subst machine
  refine ⟨{
    slot:=release.slot,present:=?_,tree:=?_,size:=slotSize,storage:=slotLen,mask:=slotMask,
    provenance:=slotProv,mutable:=slotMut,rootFree:=?_,childHeld:=?_,distinct:=s.slotDistinct}⟩
  · rw [←releaseSlotId];exact release.slotPresent
  · change release.slot.allocation.extra = PhysicalMachineWrite.slotTree s.slotRoot (next s.tracker s.fresh).global.nextPointerTag 1 true
    rw [←releaseRoot,←releaseChild];exact release.slotTree
  · exact GenericFunctionEntryState.buffer_root_free s.tracker s.fresh s.slotFresh s.slotRoot s.slotParentDistinct s.slotDistinct s.slotFree
  · exact GenericFunctionEntryNumerics.slot_child_held s.tracker s.fresh s.slotFresh

/-- Exact ownership of the two ROOT protectors on the fixed initialized caller. -/
theorem frame (s : Initial) (n : UInt64) :
    (GeneralBorrowRawRootInitialize.caller s n).extra.borrowTracker =
      some ((({} : FrameState).addProtector s.id s.tracker.global.nextPointerTag).addProtector s.slotId (slotTag s)) := by
  exact (PositiveRootInstalledFrame.metadata (RawRootInvocation.root s.before s.place s.race)
    (GeneralBorrowRawRootPrefixFrame.sourceValue s) n {} s.id s.tracker.global.nextPointerTag s.slotId (slotTag s)).2.2.2.2.2.2.2.1
end
end DuplicatePrefix.GeneralBorrowRawRootInitialSlot
