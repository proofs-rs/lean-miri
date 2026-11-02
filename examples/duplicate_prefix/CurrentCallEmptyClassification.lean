import duplicate_prefix.CurrentCallOrdinaryInput
import duplicate_prefix.WildcardEmptyCoherentResolution
namespace DuplicatePrefix.CurrentCallEmptyClassification
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
open Miri.TreeBorrows
open CandidateCurrentJointCall CurrentCallOrdinaryInput
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- Exhaustive CURRENT target representation. Metadata-backed absent targets
are kept separate from data payloads that really require materialization. -/
inductive Target (before : Before) (tracker : MachineHooks.BorrowState) (id : AllocId) (tag : Option BorTag) : Type where
  | live (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
      (present : before.memory.live.find? (fun row=>row.1==id)=some (id,entry))
      (parent : DuplicatePrefixEmptyReferenceInput.Parent entry.allocation.extra tag) : Target before tracker id tag
  | nonlive (metadata : DuplicatePrefixEmptyReferenceInput.Metadata before.memory id tag)
      (absent : before.memory.live.find? (fun row=>row.1==id)=none) : Target before tracker id tag
  | current (absent : before.memory.live.find? (fun row=>row.1==id)=none)
      (noFunction : before.memory.hasFunctionPointer id=false) (noVaList : before.memory.hasVaListId id=false)
      (registry : InitialRegistryVacant before id) (source : Allocation CtfeProvenance Unit) (root : BorTag)
      (payload : CurrentPayload before id source) (storage : Storage source) (compiler : CompilerFormat source)
      (cachedRoot : tracker.global.rootTag? id=some root) (compatible : tag=none ∨tag=some root) : Target before tracker id tag

/-- No source loan, family, operation result or successful ensure is assumed. -/
def target {before tracker id tag} (physical : ZeroTarget before tracker id tag) : Target before tracker id tag := by
  apply Classical.choice
  rcases physical with metadata | ⟨absent,noFunction,noVaList,registry,source,root,payload,storage,compiler,cachedRoot,compatible⟩
  · cases metadata with
    | live entry present parent=>exact ⟨.live entry present parent⟩
    | functionRow absent present=>exact ⟨.nonlive (.functionRow absent present) absent⟩
    | vaListRow absent noFunction present=>exact ⟨.nonlive (.vaListRow absent noFunction present) absent⟩
    | nondataGlobal descriptor absent noFunction noVaList present kind=>
      exact ⟨.nonlive (.nondataGlobal descriptor absent noFunction noVaList present kind) absent⟩
    | dead entry absent noFunction noVaList noGlobal present=>
      exact ⟨.nonlive (.dead entry absent noFunction noVaList noGlobal present) absent⟩
  · exact ⟨.current absent noFunction noVaList registry source root payload storage compiler cachedRoot compatible⟩

structure Hit (before : Before) (tracker : MachineHooks.BorrowState) (address : UInt64) where
  id : AllocId
  base : UInt64
  info : AllocationInfo
  known : before.memory.getAllocInfo id=.ok info
  geometry : WildcardGeneralHitReborrow.Geometry before.user.addresses.intToPtrMap address base id info.size
  exposed : before.user.addresses.exposed.contains id=true
  cached : before.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩
  target : Target before tracker id none

/-- The real query split is derived from the declared coherent inverse map.
Function/va-list/nondata/dead cases are never selected by a caller callback. -/
theorem wildcard {before tracker} (address : UInt64)
    (nonstrict : before.user.addresses.provenanceMode≠.strict)
    (coherent : GlobalAddressRecurringFormation.State before.memory before.user.addresses)
    (suppliers : ∀row∈before.user.addresses.intToPtrMap,GlobalAddressLiveErrorExclusion.Supplier before.memory row.allocId)
    (targets : ∀row∈before.user.addresses.intToPtrMap,before.user.addresses.exposed.contains row.allocId=true→
      before.user.addresses.baseAddr.find? (fun entry=>entry.allocId==row.allocId)=some ⟨row.allocId,row.address⟩ ∧ZeroTarget before tracker row.allocId none) :
    before.user.addresses.allocIdFromAddr address 0 (GlobalAddressLiveErrorExclusion.lookup before.memory)=.ok none ∨Nonempty (Hit before tracker address) := by
  rcases WildcardEmptyCoherentResolution.classify before.memory before.user.addresses address coherent nonstrict suppliers with
    ⟨position,row,valid,present,equal,done⟩ | ⟨cut,partition,choice⟩
  · by_cases exposed : before.user.addresses.exposed.contains row.allocId=true
    · have member:=Array.mem_of_getElem? present
      obtain ⟨info,known,_⟩:=GlobalAddressLiveErrorExclusion.metadata_of_supplier before.memory row.allocId (suppliers row member)
      exact .inr ⟨⟨row.allocId,row.address,info,known,.inl ⟨equal.symm,position,valid,coherent.ordered,present⟩,
        exposed,(targets row member exposed).1,target (targets row member exposed).2⟩⟩
    · change before.user.addresses.allocIdFromAddr address 0 (GlobalAddressLiveErrorExclusion.lookup before.memory)=
        .ok (if before.user.addresses.exposed.contains row.allocId=true then some row.allocId else none) at done
      rw [ite_eq_right exposed] at done
      exact .inl done
  · rcases choice with ⟨zero,done⟩ | ⟨row,info,nonzero,present,known,nondead,done⟩
    · exact .inl done
    · by_cases inside : address-row.address<info.size.bytes ∧before.user.addresses.exposed.contains row.allocId=true
      · have member:=Array.mem_of_getElem? present
        have position : cut-1+1=cut:=by omega
        exact .inr ⟨⟨row.allocId,row.address,info,known,.inr ⟨cut-1,by rw [position];exact partition,present,inside.1⟩,
          inside.2,(targets row member inside.2).1,target (targets row member inside.2).2⟩⟩
      · rw [ite_eq_right inside] at done
        exact .inl done

/-- A finite physical dispatch, derived internally from EmptySource. It does
not introduce source ownership or collapse wildcard provenance to integer. -/
inductive Source (before : Before) (tracker : MachineHooks.BorrowState) (argument : DuplicatePrefixSliceArgument.Argument) : Type where
  | integer (address : UInt64) (encoding : argument=.integer address) (nonnull : address≠0) : Source before tracker argument
  | concrete (pointer : Pointer Provenance) (encoding : argument=.pointer pointer) (id : AllocId) (tag : BorTag)
      (provenance : pointer.provenance=.concrete id tag) (nonnull : pointer.offset.bytes≠0)
      (base : UInt64) (cached : before.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩)
      (target : Target before tracker id (some tag)) : Source before tracker argument
  | miss (pointer : Pointer Provenance) (encoding : argument=.pointer pointer) (provenance : pointer.provenance=.wildcard)
      (nonnull : pointer.offset.bytes≠0) (nonstrict : before.user.addresses.provenanceMode≠.strict)
      (query : before.user.addresses.allocIdFromAddr pointer.offset.bytes 0 (GlobalAddressLiveErrorExclusion.lookup before.memory)=.ok none) : Source before tracker argument
  | hit (pointer : Pointer Provenance) (encoding : argument=.pointer pointer) (provenance : pointer.provenance=.wildcard)
      (nonnull : pointer.offset.bytes≠0) (nonstrict : before.user.addresses.provenanceMode≠.strict)
      (selected : Hit before tracker pointer.offset.bytes) : Source before tracker argument

def classify {before tracker argument} (physical : EmptySource before tracker (DuplicatePrefixSliceArgument.placePointer argument)) : Source before tracker argument := by
  apply Classical.choice
  cases argument with
  | integer address=>exact ⟨.integer address rfl physical.1⟩
  | pointer pointer=>
    obtain ⟨nonnull,source⟩:=physical
    cases provenance : pointer.provenance with
    | concrete id tag=>
      change pointer.offset.bytes≠0 at nonnull
      simp only [DuplicatePrefixSliceArgument.placePointer,Pointer.withOptionalProvenance,provenance] at source
      change (∃base,before.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩) ∧ZeroTarget before tracker id (some tag) at source
      obtain ⟨⟨base,cached⟩,selected⟩:=source
      exact ⟨.concrete pointer rfl id tag provenance nonnull base cached (target selected)⟩
    | wildcard=>
      change pointer.offset.bytes≠0 at nonnull
      simp only [DuplicatePrefixSliceArgument.placePointer,Pointer.withOptionalProvenance,provenance] at source
      change before.user.addresses.provenanceMode≠.strict ∧GlobalAddressRecurringFormation.State before.memory before.user.addresses ∧
        (∀row∈before.user.addresses.intToPtrMap,GlobalAddressLiveErrorExclusion.Supplier before.memory row.allocId) ∧
        (∀row∈before.user.addresses.intToPtrMap,before.user.addresses.exposed.contains row.allocId=true→
          before.user.addresses.baseAddr.find? (fun entry=>entry.allocId==row.allocId)=some ⟨row.allocId,row.address⟩ ∧ZeroTarget before tracker row.allocId none) at source
      obtain ⟨nonstrict,coherent,suppliers,targets⟩:=source
      rcases wildcard pointer.offset.bytes nonstrict coherent suppliers targets with miss | selected
      · exact ⟨.miss pointer rfl provenance nonnull nonstrict miss⟩
      · obtain ⟨hit⟩:=selected
        exact ⟨.hit pointer rfl provenance nonnull nonstrict hit⟩
end
end DuplicatePrefix.CurrentCallEmptyClassification
