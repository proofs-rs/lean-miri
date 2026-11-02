import duplicate_prefix.GeneralBorrowScopedDualPhysicalReturnPlan
import duplicate_prefix.GeneralBorrowStructuralHistoryActivityFull
namespace DuplicatePrefix.GeneralBorrowScopedDualDataReturnPlan
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- Full positive allocation Read/Write data form the physical root pop plan.
The geometry derives broad callback activity; the actual release scan chooses
Read or Write independently at each row, including partial-copy mixed states. -/
def build (memory : MemoryState Provenance BorrowTree MiriMemoryKind) (protections : ProtectedTags)
    (id : AllocId) (tag : BorTag) (buffer : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (present : memory.live.find? (fun row=>row.1==id)=some (id,buffer))
    (anchor selected head : UniIndex) (tail : List UniIndex)
    (context : GeneralBorrowExposedKnownRootRangeData.Context buffer.allocation.extra anchor selected head tail)
    (notExposed : context.anchorNode.isExposed=false)
    (tagPresent : buffer.allocation.extra.indexOfTag tag=some anchor)
    (capacity : UInt64) (positive : (0:UInt64).toNat<capacity.toNat)
    (well : buffer.allocation.extra.locations.WellFormed) (size : buffer.allocation.extra.locations.size.bytes=capacity)
    (fits : buffer.allocation.extra.nodes.data.size≤4294967296)
    (owned : ∀ kind,GeneralRangeMapOrigins.OwnedOn (fun location=>Nonempty (GeneralBorrowExposedKnownRootRangeData.Data
      buffer.allocation.extra location protections anchor selected head tail kind)) 0 capacity buffer.allocation.extra.locations)
    (slotId : AllocId) (separate : slotId≠id) (slot : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (slotPresent : memory.live.find? (fun row=>row.1==slotId)=some (slotId,slot)) (slotRoot slotChild : BorTag)
    (slotTree : slot.allocation.extra=PhysicalMachineWrite.slotTree slotRoot slotChild 1 true)
    (slotRootFree : protections.contains slotRoot=false) (slotChildHeld : protections.contains slotChild=true)
    (slotDistinct : slotRoot≠slotChild) : GeneralBorrowScopedDualPhysicalReturnPlan.Input memory protections where
  id:=id;tag:=tag;buffer:=buffer;present:=present;anchor:=anchor;selected:=selected;head:=head;tail:=tail
  lower:=0;upper:=capacity;positive:=positive;fits:=fits;context:=context;notExposed:=notExposed;tagPresent:=tagPresent
  active:=by
    have full := GeneralBorrowFreshActiveWithin.active_on buffer.allocation.extra anchor .Write 0 buffer.allocation.extra.locations.size.bytes well
      (GeneralBorrowStructuralHistoryActivityFull.full buffer.allocation.extra anchor well)
    rw [size] at full
    exact full
  owned:=owned
  slotId:=slotId;separate:=separate;slot:=slot;slotPresent:=slotPresent;slotRoot:=slotRoot;slotChild:=slotChild
  slotTree:=slotTree;slotRootFree:=slotRootFree;slotChildHeld:=slotChildHeld;slotDistinct:=slotDistinct
end DuplicatePrefix.GeneralBorrowScopedDualDataReturnPlan
