import duplicate_prefix.GeneralBorrowScopedInactiveWritableDualPhysicalReturnPlan
import duplicate_prefix.GeneralBorrowExposedScopedWindowReleaseActivity
namespace DuplicatePrefix.GeneralBorrowScopedInactiveWritableWindowDataReturnPlan
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- Window-only Read/Write owners and genuine outside inactivity form the
actual root pop plan. The real release scan dispatches each associated kind
inside the window and skips inactive outside rows, including stored defaults. -/
def build (memory : MemoryState Provenance BorrowTree MiriMemoryKind) (protections : ProtectedTags)
    (id : AllocId) (tag : BorTag) (buffer : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (present : memory.live.find? (fun row=>row.1==id)=some (id,buffer))
    (anchor selected head : UniIndex) (tail : List UniIndex)
    (context : GeneralBorrowExposedKnownRootRangeData.Context buffer.allocation.extra anchor selected head tail)
    (notExposed : context.anchorNode.isExposed=false)
    (tagPresent : buffer.allocation.extra.indexOfTag tag=some anchor)
    (offset len : UInt64) (positive : offset.toNat<(offset+len).toNat)
    (well : buffer.allocation.extra.locations.WellFormed)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin buffer.allocation.extra anchor .Write offset (offset+len))
    (fits : buffer.allocation.extra.nodes.data.size≤4294967296)
    (support : Nat → Prop)
    (owned : GeneralRangeMapOrigins.OwnedOn (fun location=>Nonempty (GeneralBorrowExposedScopedInactiveWritableAccessData.Data
      buffer.allocation.extra location protections anchor selected head tail support)) offset (offset+len) buffer.allocation.extra.locations)
    (slotId : AllocId) (separate : slotId≠id) (slot : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (slotPresent : memory.live.find? (fun row=>row.1==slotId)=some (slotId,slot)) (slotRoot slotChild : BorTag)
    (slotTree : slot.allocation.extra=PhysicalMachineWrite.slotTree slotRoot slotChild 1 true)
    (slotRootFree : protections.contains slotRoot=false) (slotChildHeld : protections.contains slotChild=true)
    (slotDistinct : slotRoot≠slotChild) : GeneralBorrowScopedInactiveWritableDualPhysicalReturnPlan.Input memory protections where
  id:=id;tag:=tag;buffer:=buffer;present:=present;anchor:=anchor;selected:=selected;head:=head;tail:=tail
  lower:=offset;upper:=offset+len;positive:=positive;fits:=fits;context:=context;notExposed:=notExposed;tagPresent:=tagPresent
  active:=GeneralBorrowFreshActiveWithin.active_on buffer.allocation.extra anchor .Write offset (offset+len) well active
  support:=support;owned:=owned
  slotId:=slotId;separate:=separate;slot:=slot;slotPresent:=slotPresent;slotRoot:=slotRoot;slotChild:=slotChild
  slotTree:=slotTree;slotRootFree:=slotRootFree;slotChildHeld:=slotChildHeld;slotDistinct:=slotDistinct
end DuplicatePrefix.GeneralBorrowScopedInactiveWritableWindowDataReturnPlan
