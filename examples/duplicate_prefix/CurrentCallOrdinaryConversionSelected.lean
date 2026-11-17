import duplicate_prefix.CurrentCallOrdinaryInput
import duplicate_prefix.CurrentCallConversionPlanAdequacy
import duplicate_prefix.CurrentCallConversionMetadataBounds
import duplicate_prefix.CurrentCallConversionSelectedWeight
namespace DuplicatePrefix.CurrentCallOrdinaryConversionSelected
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open CandidateCurrentJointCall CurrentCallOrdinaryInput
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

def Data (before : Before) (id : AllocId) (source : Allocation CtfeProvenance Unit) : Prop:=
  CurrentPayload before id source ∧Storage source ∧CompilerFormat source ∧
  before.memory.live.find? (fun row=>row.1==id)=none ∧
  before.memory.hasFunctionPointer id=false ∧before.memory.hasVaListId id=false

private theorem latent_data (before : Before) (tracker : MachineHooks.BorrowState)
    (family : CurrentCallSpatialCover.Family) (offset length capacity : UInt64) (initialized : Bool)
    (role : LatentRole before tracker family offset length capacity initialized)
    (source : Allocation CtfeProvenance Unit) (payload : CurrentCallConversionPlan.payload before family.allocation=some source) :
    Data before family.allocation source := by
  obtain ⟨absent,noFunction,noVaList,_,_,old,current,_,format,physical⟩:=role
  have oldPayload:=CurrentCallConversionPlanAdequacy.payload_of_current before family.allocation old absent noFunction noVaList current
  have same : source=old:=Option.some.inj (payload.symm.trans oldPayload)
  subst source
  exact ⟨current,physical.1,format,absent,noFunction,noVaList⟩

private theorem current_size {before id source info}
    (data : Data before id source) (known : before.memory.getAllocInfo id=.ok info) : info.size=source.byteSize := by
  obtain ⟨current,_,_,absent,noFunction,noVaList⟩:=data
  unfold MemoryState.hasVaListId at noVaList
  cases current with
  | memory descriptor=>
    simp only [MemoryState.getAllocInfo,absent,noFunction,noVaList,Bool.false_eq_true,ite_false,descriptor] at known
    exact (congrArg AllocationInfo.size (Except.ok.inj known)).symm
  | internalStatic definition descriptor initializer=>
    simp only [MemoryState.getAllocInfo,absent,noFunction,noVaList,Bool.false_eq_true,ite_false,descriptor] at known
    exact (congrArg AllocationInfo.size (Except.ok.inj known)).symm

private theorem return_data {options limits remaining span before argument length place}
    (input : OrdinaryInput options limits remaining span before argument length place)
    (source : Allocation CtfeProvenance Unit) (payload : CurrentCallConversionPlan.payload before input.returnFamily.allocation=some source) :
    Data before input.returnFamily.allocation source := by
  rcases input.returnBacking with live | latent
  · have none:=CurrentCallConversionPlanAdequacy.live_payload before input.tracker input.returnFamily input.returnOffset 1 input.returnCapacity false live
    rw [none] at payload
    cases payload
  · exact latent_data before input.tracker input.returnFamily input.returnOffset 1 input.returnCapacity false latent source payload

/-- Selected initial data are projected from the declared source/return roles.
No converter execution or callback result occurs in this statement. -/
theorem payloads {options limits remaining span before argument length place}
    (input : OrdinaryInput options limits remaining span before argument length place) :
    ∀row∈CurrentCallConversionPlan.selectedRows before argument length place,
      Data before row.1 row.2 ∧SelectedConversion before argument input.returnFamily.allocation row.1 row.2 := by
  have ret (id : AllocId) (source : Allocation CtfeProvenance Unit)
      (same : some input.returnFamily.allocation=some id) (payload : CurrentCallConversionPlan.payload before id=some source) :
      Data before id source ∧SelectedConversion before argument input.returnFamily.allocation id source := by
    have equal:=Option.some.inj same
    subst id
    exact ⟨return_data input source payload,Or.inl rfl⟩
  by_cases zero : length=0
  · obtain ⟨selected,rows⟩:=CurrentCallConversionPlanAdequacy.empty_rows options limits remaining span before argument length place input zero
    rw [rows]
    intro row member
    obtain ⟨payload,side⟩:=CurrentCallConversionSelectedWeight.rowsFromIds_member before
      (CurrentCallConversionPlanAdequacy.emptyId selected) (some input.returnFamily.allocation) row member
    rcases side with sourceSide | retSide
    · cases selected with
      | integer address encoding nonnull=>simp only [CurrentCallConversionPlanAdequacy.emptyId] at sourceSide;cases sourceSide
      | miss pointer encoding provenance nonnull nonstrict query=>simp only [CurrentCallConversionPlanAdequacy.emptyId] at sourceSide;cases sourceSide
      | concrete pointer encoding id tag provenance nonnull base cached target=>
        have same : id=row.1:=Option.some.inj sourceSide
        cases target with
        | live entry present parent=>
          have none:=CurrentCallConversionPlan.payload_live before id entry present
          rw [←same,none] at payload;cases payload
        | nonlive metadata absent=>
          have none:=CurrentCallConversionPlanAdequacy.metadata_payload before input.tracker id (some tag) metadata
          rw [←same,none] at payload;cases payload
        | current absent noFunction noVaList registry source root current storage format rootCached compatible=>
          have old:=CurrentCallConversionPlanAdequacy.payload_of_current before id source absent noFunction noVaList current
          have actual : CurrentCallConversionPlan.payload before id=some row.2:=by rw [←same] at payload;exact payload
          have sameSource : row.2=source:=Option.some.inj (actual.symm.trans old)
          refine ⟨?_,Or.inr ?_⟩
          · rw [←same,sameSource];exact ⟨current,storage,format,absent,noFunction,noVaList⟩
          · rw [encoding]
            change (match pointer.provenance with | .concrete supplied _=>row.1=supplied | .wildcard=>_)
            rw [provenance];exact same.symm
      | hit pointer encoding provenance nonnull nonstrict hit=>
        have same : hit.id=row.1:=Option.some.inj sourceSide
        cases targetEq : hit.target with
        | live entry present parent=>
          have none:=CurrentCallConversionPlan.payload_live before hit.id entry present
          rw [←same,none] at payload;cases payload
        | nonlive metadata absent=>
          have none:=CurrentCallConversionPlanAdequacy.metadata_payload before input.tracker hit.id none metadata
          rw [←same,none] at payload;cases payload
        | current absent noFunction noVaList registry source root current storage format rootCached compatible=>
          have old:=CurrentCallConversionPlanAdequacy.payload_of_current before hit.id source absent noFunction noVaList current
          have actual : CurrentCallConversionPlan.payload before hit.id=some row.2:=by rw [←same] at payload;exact payload
          have sameSource : row.2=source:=Option.some.inj (actual.symm.trans old)
          have data : Data before hit.id source:=⟨current,storage,format,absent,noFunction,noVaList⟩
          refine ⟨?_,Or.inr ?_⟩
          · rw [←same,sameSource];exact data
          · rw [encoding]
            change (match pointer.provenance with | .concrete supplied _=>row.1=supplied | .wildcard=>_)
            rw [provenance]
            refine ⟨?_,hit.base,?_⟩
            · rw [←same];exact hit.exposed
            · rw [←same,sameSource,←current_size data hit.known];exact hit.geometry
    · exact ret row.1 row.2 retSide payload
  · obtain ⟨family,offset,capacity,encoding,selected,backing,rows⟩:=
      CurrentCallConversionPlanAdequacy.positive_rows options limits remaining span before argument length place input zero
    rw [rows]
    intro row member
    obtain ⟨payload,side⟩:=CurrentCallConversionSelectedWeight.rowsFromIds_member before (some family.allocation) (some input.returnFamily.allocation) row member
    rcases side with sourceSide | retSide
    · have same : family.allocation=row.1:=Option.some.inj sourceSide
      rcases backing with live | latent
      · have none:=CurrentCallConversionPlanAdequacy.live_payload before input.tracker family offset length capacity true live
        rw [←same,none] at payload;cases payload
      · have data : Data before family.allocation row.2:=latent_data before input.tracker family offset length capacity true latent row.2 (by rw [same];exact payload)
        refine ⟨?_,Or.inr ?_⟩
        · rw [←same];exact data
        · rw [encoding]
          obtain ⟨_,_,_,_,⟨root,provenance,rootCached⟩,_⟩:=latent
          change (match family.value.provenance with | .concrete supplied _=>row.1=supplied | .wildcard=>_)
          rw [provenance];exact same.symm
    · exact ret row.1 row.2 retSide payload

/-- Every actual selected relocation has the declared initial metadata. -/
theorem targets_metadata {options limits remaining span before argument length place}
    (input : OrdinaryInput options limits remaining span before argument length place)
    (id : AllocId) (member : id∈CurrentCallConversionPlan.selectedIds before argument length place) :
    RelocationTargetMetadata before id := by
  simp only [CurrentCallConversionPlan.selectedIds, CurrentCallConversionPlan.selectedPayloads,
    List.mem_flatMap, List.mem_map] at member
  obtain ⟨source,⟨row,rowMember,rfl⟩,ptr,ptrMember,idEq⟩:=member
  obtain ⟨data,selected⟩:=payloads input row rowMember
  obtain ⟨current,_,_,absent,_,_⟩:=data
  subst id
  exact input.relocationMetadata row.1 row.2 absent current selected ptr (by simpa using ptrMember)

/-- Selected rows are counted by descriptor identity, even when their payloads agree. -/
theorem weight_le {options limits remaining span before argument length place}
    (input : OrdinaryInput options limits remaining span before argument length place)
    (weight : Allocation CtfeProvenance Unit→Nat) :
    ((CurrentCallConversionPlan.selectedPayloads before argument length place).map weight).sum≤
      ((currentConversionInputs before).map weight).sum := by
  unfold CurrentCallConversionPlan.selectedPayloads
  simp only [List.map_map]
  apply CurrentCallConversionSelectedWeight.rows_weight_le
  intro row member
  exact (payloads input row member).1.1


private theorem filtered_flatMap_length (sources : List (Allocation CtfeProvenance Unit)) (p : AllocId→Bool) :
    ((sources.flatMap fun source=>source.provenanceMap.ptrs.toList.map (fun row=>row.2.allocId)).filter p).length=
    (sources.map fun source=>((source.provenanceMap.ptrs.toList.map (fun row=>row.2.allocId)).filter p).length).sum := by
  induction sources with
  | nil=>simp
  | cons source rest ih=>simp [List.flatMap_cons,List.filter_append,ih]

/-- Every predicate-counted selected request is bounded by the declared global budget list. -/
theorem misses_le {options limits remaining span before argument length place}
    (input : OrdinaryInput options limits remaining span before argument length place) (p : AllocId→Bool) :
    ((CurrentCallConversionPlan.selectedIds before argument length place).filter p).length≤
      ((conversionTargets before).filter p).length := by
  have bound:=weight_le input (fun source=>((source.provenanceMap.ptrs.toList.map (fun row=>row.2.allocId)).filter p).length)
  rw [←filtered_flatMap_length] at bound
  change ((CurrentCallConversionPlan.selectedIds before argument length place).filter p).length≤_ at bound
  have total:=filtered_flatMap_length (currentConversionInputs before) p
  unfold conversionTargets
  simp only [List.flatMap_append,List.filter_append,List.length_append]
  omega

theorem root_misses_le {options limits remaining span before argument length place}
    (input : OrdinaryInput options limits remaining span before argument length place) :
    ((CurrentCallConversionPlan.selectedIds before argument length place).filter
      (fun id=>(input.tracker.global.rootTag? id).isNone)).length≤rootMissCount before input.tracker :=
  misses_le input _

theorem address_misses_le {options limits remaining span before argument length place}
    (input : OrdinaryInput options limits remaining span before argument length place) :
    ((CurrentCallConversionPlan.selectedIds before argument length place).filter
      (fun id=>(before.user.addresses.baseAddr.find? (fun row=>row.allocId==id)).isNone)).length≤addressMissCount before :=
  misses_le input _


 theorem payload_data {options limits remaining span before argument length place}
    (input : OrdinaryInput options limits remaining span before argument length place)
    (source : Allocation CtfeProvenance Unit)
    (member : source∈CurrentCallConversionPlan.selectedPayloads before argument length place) :
    ∃id,Data before id source ∧SelectedConversion before argument input.returnFamily.allocation id source := by
  change source∈(CurrentCallConversionPlan.selectedRows before argument length place).map Prod.snd at member
  obtain ⟨row,rowMember,equal⟩:=List.mem_map.mp member
  subst source
  exact ⟨row.1,payloads input row rowMember⟩


/-- A CURRENT selected source is the first payload, with any distinct return
payload following it. Equal allocation IDs suppress the second conversion. -/
theorem source_first (before : Before) (argument : DuplicatePrefixSliceArgument.Argument)
    (length : UInt64) (place : MPlaceTy Provenance) (id : AllocId)
    (source : Allocation CtfeProvenance Unit)
    (query : CurrentCallConversionPlan.sourceQuery before argument length=.ok (some id))
    (payload : CurrentCallConversionPlan.payload before id=some source) :
    ∃rest,CurrentCallConversionPlan.selectedPayloads before argument length place=source::rest ∧
      CurrentCallConversionPlan.selectedIds before argument length place=
        source.provenanceMap.ptrs.toList.map (fun row=>row.2.allocId) ++
          rest.flatMap (fun source=>source.provenanceMap.ptrs.toList.map (fun row=>row.2.allocId)) := by
  let tail:=((CurrentCallConversionPlan.returnQuery before place).toOption.bind _root_.id).bind fun ret=>
    if id==ret then none else (CurrentCallConversionPlan.payload before ret).map fun value=>(ret,value)
  have rows : CurrentCallConversionPlan.selectedRows before argument length place=(id,source)::tail.toList := by
    simp only [CurrentCallConversionPlan.selectedRows,CurrentCallConversionPlan.rowsFromIds,query,
      Except.toOption,id_eq,Option.bind_some,payload,Option.map_some,Option.any_some,Option.toList_some,
      List.singleton_append]
    rfl
  refine ⟨tail.toList.map Prod.snd,?_,?_⟩
  · simp only [CurrentCallConversionPlan.selectedPayloads,rows,List.map_cons]
  · simp only [CurrentCallConversionPlan.selectedIds,CurrentCallConversionPlan.selectedPayloads,
      rows,List.map_cons,List.flatMap_cons]

end
end DuplicatePrefix.CurrentCallOrdinaryConversionSelected

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "CurrentCallOrdinaryConversionSelected.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved initial-conversion dependency {name}: {dependency}"
