import duplicate_prefix.GeneralBorrowScopedResourcesRelease
import duplicate_prefix.GeneralBorrowScopedPhysicalReturnPlan
namespace DuplicatePrefix.GeneralBorrowScopedResourcesReturnPlan
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposedKnownRootState (Scope)
open GeneralBorrowFreshMetadataChildShared (Input)
open GeneralBorrowExposedScopedSharedLeafConstructor (Resources)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
noncomputable section

/-- Assemble the real two-row pop contract directly from current scoped
Resources and the independent bool-slot allocation. Both releases and the
production stack-pop operation follow from this data. -/
def build (memory : MemoryState Provenance BorrowTree MiriMemoryKind) (protections : ProtectedTags)
    (input : Input) (selected head : UniIndex) (tail : List UniIndex) (kind : AccessKind)
    (raw : Resources input protections selected head tail (fun _=>true))
    (positive : input.offset.toNat<(input.offset+input.len).toNat)
    (active : GeneralBorrowFreshReleaseLoop.ActiveOn input.tree input.parent kind input.offset (input.offset+input.len))
    (matching : ∀ position (valid : position<input.tree.locations.entries.size) state,
      input.tree.locations.entries[position].data.perms.get input.parent=some state → state.accessed=true →
      ∀ associated,state.permission.associatedAccess=some associated → associated=kind)
    (id : AllocId) (buffer : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (present : memory.live.find? (fun row=>row.1==id)=some (id,buffer)) (treeEq : buffer.allocation.extra=input.tree)
    (slotId : AllocId) (separate : slotId≠id) (slot : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (slotPresent : memory.live.find? (fun row=>row.1==slotId)=some (slotId,slot)) (slotRoot slotChild : BorTag)
    (slotTree : slot.allocation.extra=PhysicalMachineWrite.slotTree slotRoot slotChild 1 true)
    (slotRootFree : protections.contains slotRoot=false) (slotChildHeld : protections.contains slotChild=true)
    (slotDistinct : slotRoot≠slotChild) : GeneralBorrowScopedPhysicalReturnPlan.Input memory protections where
  id:=id;tag:=input.parentTag;buffer:=buffer;present:=present;anchor:=input.parent
  selected:=selected;head:=head;tail:=tail;kind:=kind;lower:=input.offset;upper:=input.offset+input.len;positive:=positive
  fits:=by rw [treeEq];change input.tree.nodes.size≤4294967296;have bound:=raw.room;omega
  context:={
    anchorNode:=input.parentNode
    selectedNode:=raw.selectedNode
    anchorPresent:=by rw [treeEq];exact input.parentPresent
    selectedPresent:=by rw [treeEq];exact raw.selectedPresent
    roots:=by rw [treeEq];exact raw.roots
    depth:=by rw [treeEq];exact input.depth
    children:=by rw [treeEq];exact input.children
    tags:=by rw [treeEq];exact raw.tags }
  notExposed:=by exact raw.hidden input.parent input.parentNode raw.component.anchor input.parentPresent
  tagPresent:=by rw [treeEq];exact input.parentTagPresent
  active:=by rw [treeEq];exact active
  matching:=by rw [treeEq];exact matching
  owned:=by
    rw [treeEq]
    cases kind with
    | Read => exact GeneralBorrowScopedResourcesData.read input protections selected head tail (fun _=>true) raw
    | Write => exact GeneralBorrowScopedResourcesData.write input protections selected head tail raw
  slotId:=slotId;separate:=separate;slot:=slot;slotPresent:=slotPresent;slotRoot:=slotRoot;slotChild:=slotChild
  slotTree:=slotTree;slotRootFree:=slotRootFree;slotChildHeld:=slotChildHeld;slotDistinct:=slotDistinct
end
end DuplicatePrefix.GeneralBorrowScopedResourcesReturnPlan
