import duplicate_prefix.S03MaterializableArgumentScope
import duplicate_prefix.S03MaterializableWildcardScope

namespace DuplicatePrefix.S03MaterializableInput
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- Initial source metadata extracted from the materializable alternative.
The descriptor retains the actual MEMORY image or supported STATIC initializer,
and Supported retains the complete finite relocation witness. -/
structure Packet (options : EvalConfigurationCore.Options) (before : Before)
    (tracker : MachineHooks.BorrowState) (id : AllocId) (tag : Option BorTag) where
  source : Allocation CtfeProvenance Unit
  root : BorTag
  absent : before.memory.live.find? (fun row => row.1 == id) = none
  noFunction : before.memory.hasFunctionPointer id = false
  noVaList : before.memory.hasVaListId id = false
  descriptor : DuplicatePrefixEmptyReferenceInput.ImageDescriptor (imageContext options before tracker) before.memory id source
  rootCached : tracker.global.rootTag? id = some root
  agreement : tag = none ∨ tag = some root
  noExtras : before.user.payload.payload.user.runtime.extras.allocations.any (fun row => row.1 == id) = false
  managed : (imageContext options before tracker).nativeLibraryPathsEmpty = true
  supported : GlobalSupportedImage.Supported source PreparedReflection.actual.compiler.runtime.target
    before.memory tracker.global.rootPointerTags before.user.addresses.baseAddr
  rootBelow : root.value.toNat < tracker.global.nextPointerTag.value.toNat
  distinct : root ≠ tracker.global.nextPointerTag

/-- The original raw candidate and cached-root high-water resource produce the
local facts consumed by actual materialization. No root-unprotected restriction,
materialization success or operation result is a premise. -/
theorem of_input (options : EvalConfigurationCore.Options) (before : Before)
    (tracker : MachineHooks.BorrowState) (id : AllocId) (tag : Option BorTag)
    (input : DuplicatePrefixEmptyReferenceInput.Materializable (imageContext options before tracker)
      before.memory before.user.addresses id tag)
    (below : ∀ row ∈ tracker.global.rootPointerTags.toList, row.2.value.toNat < tracker.global.nextPointerTag.value.toNat) :
    Nonempty (Packet options before tracker id tag) := by
  obtain ⟨source,root,absent,noFunction,noVaList,descriptor,cached,agreement,noExtras,managed,supported⟩ := input
  have rootCached : tracker.global.rootTag? id = some root := cached
  obtain ⟨row,found,equal⟩ := Option.map_eq_some_iff.mp cached
  have member : row ∈ tracker.global.rootPointerTags.toList :=
    Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some found)
  have rootBelow : root.value.toNat < tracker.global.nextPointerTag.value.toNat := by
    rw [←equal];exact below row member
  have distinct : root ≠ tracker.global.nextPointerTag := by
    intro same;rw [same] at rootBelow;exact Nat.lt_irrefl _ rootBelow
  have absentExtras : before.user.payload.payload.user.runtime.extras.allocations.any (fun row => row.1 == id) = false := by
    simpa only [imageContext,Array.contains_map,BEq.comm] using noExtras
  exact ⟨⟨source,root,absent,noFunction,noVaList,descriptor,rootCached,agreement,absentExtras,managed,supported,rootBelow,distinct⟩⟩

/-- Source-size metadata is derived from the same descriptor that the actual
initializer consumes, before any local allocation is fabricated. -/
theorem Packet.alloc_info {options : EvalConfigurationCore.Options} {before : Before}
    {tracker : MachineHooks.BorrowState} {id : AllocId} {tag : Option BorTag}
    (packet : Packet options before tracker id tag) :
    before.memory.getAllocInfo id = .ok ⟨packet.source.byteSize,packet.source.align,.liveData,packet.source.mutability⟩ := by
  rcases packet.descriptor with memoryDescriptor | ⟨definition,initializer,staticDescriptor⟩
  · exact GlobalDataOnlyMaterialize.alloc_info before id packet.source packet.absent packet.noFunction packet.noVaList memoryDescriptor
  · exact StaticGlobalAllocInfo.alloc_info before id packet.source definition packet.absent packet.noFunction packet.noVaList staticDescriptor

/-- Initially absent materialized images differ from the original live return
allocation, regardless of its provenance, capacity or offset. -/
theorem separate {options : EvalConfigurationCore.Options} {before : Before}
    {tracker : MachineHooks.BorrowState} {id : AllocId} {tag : Option BorTag}
    (packet : Packet options before tracker id tag) {place : MPlaceTy Provenance}
    (destination : DuplicatePrefixReturnPlaceInput.Input before place) : destination.id ≠ id := by
  intro same
  have live := destination.live
  rw [same,packet.absent] at live
  cases live

end
end DuplicatePrefix.S03MaterializableInput
