import empty_function.RelocationAdmittedRoot
import empty_function.RelocationTypeId
import empty_function.AddressStaticPost
import empty_function.AddressTransport
namespace EmptyFunction.RelocationNodrawTablesStep
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
/-- Cached normal roots and uncached TypeId roots consume no address choice.
The latter adds the real zero base; it does not require a generator. -/
theorem step (before : ChoiceExecution.S) (hooks : ChoiceExecution.H)
    (externStatic : MIR.DefId → MachineAddress.M MiriMemoryKind ChoiceExecution.Payload (Pointer Provenance))
    (tables : InputDraft.AddressTables (⟨⟨#[]⟩,before⟩ : WholeCall.State))
    (tracker : MachineHooks.BorrowState) (provenance : CtfeProvenance) (offset : UInt64)
    (admission : RawRootAdmission.Normal before.memory provenance.allocId)
    (enabled : before.borrowTracker = some tracker)
    (room : tracker.global.nextPointerTag.value.toNat+1 < 2^64)
    (width : hooks.arithmetic = ⟨Size.ofBytes 8⟩)
    (classification : (∃ base,before.user.addresses.baseAddr.find? (fun row => row.allocId == provenance.allocId) = some ⟨provenance.allocId,base⟩) ∨
      ∃ info,before.memory.getAllocInfo provenance.allocId = .ok info ∧ info.kind = .typeId ∧ before.memory.isAllocLive provenance.allocId = true) :
    ∃ pointer final global tag,
      PointerSource.globalRootPointer ChoiceExecution.tapeAccess hooks externStatic
        (Pointer.new provenance (Size.ofBytes offset)) before = .ok pointer final ∧
      final.memory = before.memory ∧ final.threads = before.threads ∧
      ChoiceExecution.tapeAccess.get final = ChoiceExecution.tapeAccess.get before ∧
      final.user.payload.payload.user.runtime = before.user.payload.payload.user.runtime ∧
      RelocationContext.view final.user.payload = RelocationContext.view before.user.payload ∧
      (∀ oldId old,before.user.addresses.baseAddr.find? (fun row => row.allocId == oldId) = some old →
        final.user.addresses.baseAddr.find? (fun row => row.allocId == oldId) = some old) ∧
      AddressStaticPost.view final.user.addresses = AddressStaticPost.view before.user.addresses ∧
      final.user.addresses.intToPtrMap = before.user.addresses.intToPtrMap ∧
      tracker.global.rootPointerTag provenance.allocId = .ok (global,tag) ∧
      final.borrowTracker = some {tracker with global} ∧ final.dataRace = before.dataRace ∧
      InputDraft.AddressTables (⟨⟨#[]⟩,final⟩ : WholeCall.State) := by
  rcases classification with ⟨base,cached⟩ | ⟨info,metadata,typed,live⟩
  · obtain ⟨tag,final,actual,memory,threads,addresses,tape,global,tagged,enabled,race,runtime,context⟩ :=
      RelocationAdmittedRoot.normal_cached before hooks externStatic tracker provenance offset base admission enabled room cached width
    refine ⟨_,final,global,tag,actual,memory,threads,tape,runtime,context,?_,?_,?_,tagged,enabled,race,?_⟩
    · intro oldId old found;rw [addresses];exact found
    · rw [addresses]
    · rw [addresses]
    · exact AddressTransport.tables _ _ memory addresses tables
  · cases cached : before.user.addresses.baseAddr.find? (fun row => row.allocId == provenance.allocId) with
    | some row =>
      have id : row.allocId = provenance.allocId := by
        have matched := Array.find?_some cached
        simpa only [beq_iff_eq] using matched
      have same : row = ⟨provenance.allocId,row.address⟩ := by cases row; simp_all
      rw [same] at cached
      obtain ⟨tag,final,actual,memory,threads,addresses,tape,global,tagged,enabled,race,runtime,context⟩ :=
        RelocationAdmittedRoot.normal_cached before hooks externStatic tracker provenance offset row.address admission enabled room cached width
      refine ⟨_,final,global,tag,actual,memory,threads,tape,runtime,context,?_,?_,?_,tagged,enabled,race,?_⟩
      · intro oldId old found;rw [addresses];exact found
      · rw [addresses]
      · rw [addresses]
      · exact AddressTransport.tables _ _ memory addresses tables
    | none =>
      obtain ⟨global,tag,tagged,actual⟩ := RelocationTypeId.root before hooks externStatic tracker provenance offset info
        admission enabled room cached metadata typed live width
      let final : ChoiceExecution.S := {before with borrowTracker := some {tracker with global},user :=
        {before.user with addresses := {before.user.addresses with baseAddr := before.user.addresses.baseAddr.push ⟨provenance.allocId,0⟩}}}
      refine ⟨_,final,global,tag,actual,rfl,rfl,rfl,rfl,rfl,?_,rfl,rfl,tagged,rfl,rfl,?_⟩
      · intro oldId old prior
        change (before.user.addresses.baseAddr.push ⟨provenance.allocId,0⟩).find? _ = _
        simp only [Array.find?_push,prior,Option.or]
      · have cachedTables := AddressPost.cache_zero_tables (⟨⟨#[]⟩,before⟩ : WholeCall.State) tables provenance.allocId cached
        refine AddressTransport.tables (AddressPost.withAddresses (⟨⟨#[]⟩,before⟩ : WholeCall.State) (before.user.addresses.cacheAddress provenance.allocId 0).state) (⟨⟨#[]⟩,final⟩ : WholeCall.State) rfl ?_ cachedTables
        rw [AddressPost.cache_zero _ _ cached]
        rfl
end EmptyFunction.RelocationNodrawTablesStep
