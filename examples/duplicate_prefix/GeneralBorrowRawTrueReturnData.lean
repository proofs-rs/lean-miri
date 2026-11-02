import duplicate_prefix.GeneralBorrowRawRootCurrentBoolReturn
namespace DuplicatePrefix.GeneralBorrowRawTrueReturnData
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open PhysicalMachineWrite
set_option autoImplicit false
/-- Physical ROOT/return-slot facts at the INITIAL accepted mutable phase.
No future heap lookup, operation success or return-state fact is supplied. -/
structure Data (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (tag : BorTag) (anchor : UniIndex) where
  context : Context
  validationContext : Context
  accessEq : (PreparedContracts.actualConfig options () remaining span).access = validationContext.access
  validationWidth : validationContext.pointers.arithmetic = ⟨Size.ofBytes 8⟩
  validationRuntimeSize : validationContext.access.runtime.pointerSize = Size.ofBytes 8
  sameRuntime : validationContext.access.runtime.base = context.access.runtime.base
  width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩
  runtimeWidth : context.access.runtime.base.pointerWidth = .w64
  runtimeSize : context.access.runtime.pointerSize = Size.ofBytes 8
  outerAccessEq : (PreparedContracts.actualConfig options () (remaining+1) span).access = context.access
  sourceNode : TreeNode
  sourcePresent : entry.allocation.extra.nodeAt anchor = some sourceNode
  sourceTag : sourceNode.tag = tag
  sourceHidden : sourceNode.isExposed = false
  continuation : caller.returnContinuation = .stop true
  varargs : caller.vaList = #[]
  slotId : AllocId
  separate : slotId ≠ id
  slot : LocalAllocation Provenance BorrowTree MiriMemoryKind
  slotBefore : machine.memory.live.find? (fun row => row.1 == slotId) = some (slotId,slot)
  slotRoot : BorTag
  slotChild : BorTag
  slotTree : slot.allocation.extra = PhysicalMachineWrite.slotTree slotRoot slotChild 1 true
  slotRootFree : tracker.global.protectedTags.contains slotRoot = false
  slotChildHeld : tracker.global.protectedTags.contains slotChild = true
  slotDistinct : slotRoot ≠ slotChild
  frameTracked : caller.extra.borrowTracker = some ((({} : FrameState).addProtector id tag).addProtector slotId slotChild)
  slotSize : slot.allocation.byteSize = Size.ofBytes 1
  slotStorage : slot.allocation.len = 1
  slotMask : slot.allocation.initializationMask = InitMask.new (Size.ofBytes 1) false
  slotProvenance : slot.allocation.provenanceMap = ProvenanceMap.new
  slotMutable : slot.allocation.mutability = .Mut
  place : MPlaceTy Provenance
  layout : place.layout = RootCompilerFacts.boolLayout
  slotBase : UInt64
  slotPointer : place.mplace.ptr = Pointer.new (some (.concrete slotId slotRoot)) (Size.ofBytes slotBase)
  aligned : place.mplace.misaligned = none
  fits : slotBase.toNat+1 < 2^64
  cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == slotId) = some ⟨slotId,slotBase⟩
  extras : (context.extras.get machine.user).allocations.find? (fun row => row.1 == slotId) = some (slotId,⟨none,#[]⟩)
  destination : caller.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩
end DuplicatePrefix.GeneralBorrowRawTrueReturnData
