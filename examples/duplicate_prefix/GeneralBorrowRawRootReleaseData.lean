import duplicate_prefix.GeneralBorrowRawRootEntryResources
import duplicate_prefix.GeneralBorrowRawRootInstalledBuffer
import duplicate_prefix.GeneralBorrowRawFnEntryHidden
import duplicate_prefix.GeneralBorrowRawFnEntryOrder
import duplicate_prefix.GeneralBorrowRawRootReleasePlan
namespace DuplicatePrefix.GeneralBorrowRawRootReleaseData
open Miri Miri.Input Miri.Interpreter Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Form the raw two-protector ROOT pop input on the exact initializer heap.
The slot shape is the actual initializer's exported output; all buffer semantic
conditions are derived from the initial raw owner and explicit node headroom. -/
theorem form
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (buffer slot : AllocId)
    (entry slotEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global)
    (input : GeneralBorrowRawFnEntry.Input entry.allocation.extra tracker.global)
    (headroom : entry.allocation.extra.nodes.size+1 < 65536)
    (borrowFrame : FrameState) (separate : slot ≠ buffer)
    (slotRoom : (TypedRetagGeneric.protectedGlobal tracker.global input.tagRoom).nextPointerTag.value < 18446744073709551615)
    (slotRoot : BorTag)
    (slotFree : tracker.global.protectedTags.contains slotRoot = false)
    (slotRootBuffer : slotRoot ≠ tracker.global.nextPointerTag)
    (slotDistinct : slotRoot ≠ (TypedRetagGeneric.protectedGlobal tracker.global input.tagRoom).nextPointerTag)
    (updated : Allocation Provenance BorrowTree)
    (slotShape : updated.extra = PhysicalMachineWrite.slotTree slotRoot
      (TypedRetagGeneric.protectedGlobal tracker.global input.tagRoom).nextPointerTag 1 true) :
    let finalTree := GeneralBorrowRawFnEntryArgument.finalTree entry.allocation.extra tracker input.parentTag input.offset input.len
    let arguments := GeneralBorrowRawFnEntryScope.resultMachine machine tracker input.tagRoom buffer entry input.parentTag input.offset input.len
    let next : MachineHooks.BorrowState := ⟨TypedRetagGeneric.protectedGlobal tracker.global input.tagRoom,tracker.retagMode⟩
    let borrowed := ReturnProtection.borrowedState frames frame borrowFrame arguments next slotRoom slot slotEntry
      (PhysicalMachineWrite.slotTree slotRoot next.global.nextPointerTag 1 false)
    let actual := CanonicalCopy.replaceAllocation borrowed slot slotEntry.kind updated
    Nonempty (GeneralBorrowRawRootReleasePlan.Input actual.machine.memory
      (TypedRetagGeneric.protectedGlobal next.global slotRoom)) := by
  let finalTree := GeneralBorrowRawFnEntryArgument.finalTree entry.allocation.extra tracker input.parentTag input.offset input.len
  let next : MachineHooks.BorrowState := ⟨TypedRetagGeneric.protectedGlobal tracker.global input.tagRoom,tracker.retagMode⟩
  let arguments := GeneralBorrowRawFnEntryScope.resultMachine machine tracker input.tagRoom buffer entry input.parentTag input.offset input.len
  let borrowed := ReturnProtection.borrowedState frames frame borrowFrame arguments next slotRoom slot slotEntry
      (PhysicalMachineWrite.slotTree slotRoot next.global.nextPointerTag 1 false)
  let actual := CanonicalCopy.replaceAllocation borrowed slot slotEntry.kind updated
  obtain ⟨afterRuntime,capacity,growth,roots,held,slotFresh,child,lookup,⟨owner⟩,activity⟩ :=
    GeneralBorrowRawRootEntryResources.resources entry.allocation.extra tracker borrowFrame buffer slot runtime input slotRoom
  obtain ⟨hiddenChild,node,hiddenLookup,nodePresent,sameTag,hidden⟩ :=
    GeneralBorrowRawFnEntryHidden.hidden entry.allocation.extra tracker borrowFrame buffer runtime input
  have sameChild : hiddenChild = child := Option.some.inj (hiddenLookup.symm.trans lookup)
  subst hiddenChild
  obtain ⟨order,short⟩ := GeneralBorrowRawFnEntryOrder.conditional entry.allocation.extra tracker borrowFrame buffer runtime input headroom
  have installed := (GeneralBorrowRawRootInstalledBuffer.installed frames frame machine tracker input.tagRoom buffer slot entry slotEntry
    input.parentTag input.offset input.len borrowFrame separate slotRoom
    (PhysicalMachineWrite.slotTree slotRoot next.global.nextPointerTag 1 false) updated).1
  have slotInstalled := CanonicalCopy.replace_lookup borrowed slot slotEntry.kind updated
  have rootFree : (TypedRetagGeneric.protectedGlobal next.global slotRoom).protectedTags.contains slotRoot = false := by
    change ((tracker.global.protectedTags.insert tracker.global.nextPointerTag .StrongProtector).insert
      next.global.nextPointerTag .StrongProtector).contains slotRoot = false
    rw [ProtectorInsertion.contains_other _ _ _ .StrongProtector slotDistinct,
      ProtectorInsertion.contains_other _ _ _ .StrongProtector slotRootBuffer]
    exact slotFree
  have childHeld : (TypedRetagGeneric.protectedGlobal next.global slotRoom).protectedTags.contains next.global.nextPointerTag = true := by
    change (next.global.protectedTags.insert next.global.nextPointerTag .StrongProtector).contains next.global.nextPointerTag = true
    unfold ProtectedTags.contains
    rw [ProtectedTags.get_insert_same]
    rfl
  refine ⟨{
    id:=buffer,tag:=tracker.global.nextPointerTag,buffer:={entry with allocation:=entry.allocation.setExtra finalTree},
    present:=installed,anchor:=child,selected:=input.selected,maximum:=input.maximum,offset:=input.offset,len:=input.len,
    runtime:=afterRuntime,positive:=owner,node:=node,anchorPresent:=nodePresent,notExposed:=hidden,tagPresent:=lookup,
    distinct:=?_,order:=order,short:=short,active:=activity,slotId:=slot,separate:=separate,
    slot:=⟨slotEntry.kind,updated⟩,slotPresent:=slotInstalled,slotRoot:=slotRoot,slotChild:=next.global.nextPointerTag,
    slotTree:=slotShape,slotRootFree:=rootFree,slotChildHeld:=childHeld,slotDistinct:=slotDistinct}⟩
  change finalTree.roots.toList.Nodup
  rw [roots]
  exact input.distinct
end DuplicatePrefix.GeneralBorrowRawRootReleaseData
