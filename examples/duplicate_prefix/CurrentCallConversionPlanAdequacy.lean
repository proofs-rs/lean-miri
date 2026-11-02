import duplicate_prefix.CurrentCallConversionPlan
import duplicate_prefix.CurrentCallEmptyClassification

/-! Initial selected-pointer and CURRENT-payload adequacy for the exact lower
conversion plan. Later source conversion's preservation of the Bool query is
separate; no future operation result occurs in these premises. -/
namespace DuplicatePrefix.CurrentCallConversionPlanAdequacy
open Miri Miri.ABI Miri.Input Miri.Memory Miri.Interpreter Miri.TreeBorrows
open Miri.Memory.AllocAddresses
open CandidateCurrentJointCall CurrentCallOrdinaryInput CurrentCallSpatialCover
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem payload_of_current (before : Before) (id : AllocId) (source : Allocation CtfeProvenance Unit)
    (absent : before.memory.live.find? (fun row=>row.1==id)=none)
    (noFunction : before.memory.hasFunctionPointer id=false) (noVaList : before.memory.hasVaListId id=false)
    (current : CurrentPayload before id source) : CurrentCallConversionPlan.payload before id=some source := by
  cases current with
  | memory descriptor=>exact CurrentCallConversionPlan.payload_memory before id source absent noFunction noVaList descriptor
  | internalStatic definition descriptor initializer=>
      exact CurrentCallConversionPlan.payload_static before id definition source absent noFunction noVaList descriptor initializer

private theorem signed_nonnegative (length : UInt64) (fits : length.toNat<2^63) :
    0≤length.toInt64.toInt := by
  have cast : length.toInt64=Int64.ofNat length.toNat := by
    apply Int64.toBitVec_inj.mp
    simp only [UInt64.toInt64,Int64.ofNat]
    simp
  rw [cast,Int64.toInt_ofNat_of_lt fits]
  omega

/-- The real typed resolver queries size zero. Its initial selection equals
all admitted nonnegative plan sizes: the primitive uses only the sign. -/
theorem allocation_size_zero (addresses : GlobalAddressState) (address : UInt64)
    (length : UInt64) (hooks : AddressLookupHooks) (fits : length.toNat<2^63) :
    addresses.allocIdFromAddr address length.toInt64 hooks=addresses.allocIdFromAddr address 0 hooks := by
  have nonnegative:=signed_nonnegative length fits
  unfold GlobalAddressState.allocIdFromAddr
  simp only [show ¬length.toInt64.toInt<0 from by omega,show ¬(0:Int64).toInt<0 from by decide,↓reduceIte]

theorem query_concrete (before : Before) (pointer : Pointer Provenance) (length : UInt64)
    (id : AllocId) (tag : BorTag) (base : UInt64)
    (provenance : pointer.provenance=.concrete id tag)
    (cached : before.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩) :
    CurrentCallConversionPlan.query before pointer length=.ok (some id) := by
  unfold CurrentCallConversionPlan.query GlobalAddressState.ptrGetAlloc
  unfold_internal ".GlobalAddressState.findBase"
  simp only [provenance,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure,cached,Option.map_some]
  erw [DuplicatePrefix.PointerArithmetic.truncate_u64_identity]
  rfl

theorem query_wildcard (before : Before) (pointer : Pointer Provenance) (length : UInt64)
    (id : AllocId) (base : UInt64) (info : AllocationInfo)
    (provenance : pointer.provenance=.wildcard) (fits : length.toNat<2^63)
    (geometry : WildcardGeneralHitReborrow.Geometry before.user.addresses.intToPtrMap pointer.offset.bytes base id info.size)
    (mode : before.user.addresses.provenanceMode≠.strict)
    (exposed : before.user.addresses.exposed.contains id=true)
    (cached : before.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩)
    (known : before.memory.getAllocInfo id=.ok info) (live : before.memory.isAllocLive id=true) :
    CurrentCallConversionPlan.query before pointer length=.ok (some id) := by
  have selected : before.user.addresses.allocIdFromAddr pointer.offset.bytes 0
      (GlobalAddressLiveErrorExclusion.lookup before.memory)=.ok (some id) := by
    rcases geometry with ⟨equal,position,valid,ordered,row⟩|⟨position,cut,row,inside⟩
    · rw [equal]
      exact WildcardOrderedHitAddress.allocation _ _ _ _ position valid ordered row mode exposed (by simp [GlobalAddressLiveErrorExclusion.lookup,live])
    · exact WildcardInteriorHitAddress.allocation _ _ _ _ _ _ position mode cut row
        (by simp [GlobalAddressLiveErrorExclusion.lookup,known,Except.toOption]) inside exposed (by simp [GlobalAddressLiveErrorExclusion.lookup,live])
  unfold CurrentCallConversionPlan.query GlobalAddressState.ptrGetAlloc
  unfold_internal ".GlobalAddressState.findBase"
  simp only [provenance,allocation_size_zero _ _ length _ fits,selected,bind,Bind.bind,Except.bind,
    pure,Pure.pure,Except.pure,cached,Option.map_some]
  erw [DuplicatePrefix.PointerArithmetic.truncate_u64_identity]
  rfl

theorem query_of_selected (before : Before) (tracker : MachineHooks.BorrowState)
    (family : Family) (offset capacity length : UInt64) (initialized : Bool)
    (selected : SelectedPointer before tracker family offset capacity)
    (backing : LiveRole before tracker family offset length capacity initialized ∨
      LatentRole before tracker family offset length capacity initialized)
    (fits : length.toNat<2^63) :
    CurrentCallConversionPlan.query before family.value length=.ok (some family.allocation) := by
  obtain ⟨base,cached,room,position,nonnull,representation⟩:=selected
  cases provenance : family.value.provenance with
  | concrete id tag=>
      rw [provenance] at representation
      obtain ⟨same,_⟩:=representation
      subst id
      exact query_concrete before family.value length family.allocation tag base provenance cached
  | wildcard=>
      rw [provenance] at representation
      obtain ⟨mode,exposed,geometry⟩:=representation
      rcases backing with live|latent
      · obtain ⟨entry,present,capacityEq,_⟩:=live
        have member:=Array.mem_of_find?_eq_some present
        have any : before.memory.live.any (fun row=>row.1==family.allocation)=true :=
          Array.any_eq_true'.mpr ⟨(family.allocation,entry),member,by simp⟩
        have live : before.memory.isAllocLive family.allocation=true := by simp [MemoryState.isAllocLive,any]
        let info : AllocationInfo:=⟨Size.ofBytes capacity,entry.allocation.align,.liveData,entry.allocation.mutability⟩
        have known : before.memory.getAllocInfo family.allocation=.ok info := by
          simp [MemoryState.getAllocInfo,present,info,capacityEq,pure,Pure.pure,Except.pure]
        exact query_wildcard before family.value length family.allocation base info provenance fits
          geometry mode exposed cached known live
      · obtain ⟨_,_,_,_,⟨root,concrete,_⟩,_⟩:=latent
        rw [provenance] at concrete
        cases concrete

theorem live_payload (before : Before) (tracker : MachineHooks.BorrowState)
    (family : Family) (offset length capacity : UInt64) (initialized : Bool)
    (backing : LiveRole before tracker family offset length capacity initialized) :
    CurrentCallConversionPlan.payload before family.allocation=none := by
  obtain ⟨entry,present,_⟩:=backing
  exact CurrentCallConversionPlan.payload_live before family.allocation entry present

theorem latent_payload (before : Before) (tracker : MachineHooks.BorrowState)
    (family : Family) (offset length capacity : UInt64) (initialized : Bool)
    (backing : LatentRole before tracker family offset length capacity initialized) :
    ∃source : Allocation CtfeProvenance Unit,CurrentPayload before family.allocation source ∧
      CurrentCallConversionPlan.payload before family.allocation=some source := by
  obtain ⟨absent,noFunction,noVaList,_,_,source,current,_⟩:=backing
  exact ⟨source,current,payload_of_current before family.allocation source absent noFunction noVaList current⟩

/-- Erasure of the EXISTING declarative empty classifier, not another resolver. -/
def emptyId {before tracker argument} (selected : CurrentCallEmptyClassification.Source before tracker argument) : Option AllocId :=
  match selected with
  | .integer ..=>none
  | .concrete _ _ id ..=>some id
  | .miss ..=>none
  | .hit _ _ _ _ _ hit=>some hit.id

theorem empty_query (before : Before) (tracker : MachineHooks.BorrowState)
    (argument : DuplicatePrefixSliceArgument.Argument)
    (physical : EmptySource before tracker (DuplicatePrefixSliceArgument.placePointer argument))
    (selected : CurrentCallEmptyClassification.Source before tracker argument) :
    CurrentCallConversionPlan.sourceQuery before argument 0=.ok (emptyId selected) := by
  cases selected with
  | integer address encoding nonnull=>
      change CurrentCallConversionPlan.sourceQuery before argument 0=.ok none
      rw [encoding];rfl
  | concrete pointer encoding id tag provenance nonnull base cached target=>
      change CurrentCallConversionPlan.sourceQuery before argument 0=.ok (some id)
      rw [encoding]
      exact query_concrete before pointer 0 id tag base provenance cached
  | miss pointer encoding provenance nonnull nonstrict raw=>
      change CurrentCallConversionPlan.sourceQuery before argument 0=.ok none
      rw [encoding]
      change CurrentCallConversionPlan.query before pointer 0=.ok none
      unfold CurrentCallConversionPlan.query GlobalAddressState.ptrGetAlloc
      simp only [provenance,show (0:UInt64).toInt64=0 from rfl,raw,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]
      rfl
  | hit pointer encoding provenance nonnull nonstrict hit=>
      change CurrentCallConversionPlan.sourceQuery before argument 0=.ok (some hit.id)
      rw [encoding]
      rw [encoding] at physical
      simp only [DuplicatePrefixSliceArgument.placePointer,Pointer.withOptionalProvenance,provenance] at physical
      obtain ⟨_,_,coherent,_⟩:=physical
      have live : before.memory.isAllocLive hit.id=true :=
        coherent.live.2 hit.id (Array.contains_iff_mem.mp hit.exposed)
      exact query_wildcard before pointer 0 hit.id hit.base hit.info provenance (by decide)
        hit.geometry nonstrict hit.exposed hit.cached hit.known live

theorem metadata_payload (before : Before) (_tracker : MachineHooks.BorrowState) (id : AllocId)
    (tag : Option BorTag) (metadata : DuplicatePrefixEmptyReferenceInput.Metadata before.memory id tag) :
    CurrentCallConversionPlan.payload before id=none := by
  cases metadata with
  | live entry present parent=>exact CurrentCallConversionPlan.payload_live before id entry present
  | functionRow absent present=>simp [CurrentCallConversionPlan.payload,absent,present]
  | vaListRow absent noFunction present=>simp [CurrentCallConversionPlan.payload,absent,noFunction,present]
  | nondataGlobal descriptor absent noFunction noVaList present kind=>
      rcases kind with kind|kind|kind <;>
        simp [CurrentCallConversionPlan.payload,absent,noFunction,noVaList,present,kind]
  | dead entry absent noFunction noVaList noGlobal present=>
      simp [CurrentCallConversionPlan.payload,absent,noFunction,noVaList,noGlobal]

def emptyPayload {before tracker id tag} (target : CurrentCallEmptyClassification.Target before tracker id tag) :
    Option (Allocation CtfeProvenance Unit) :=
  match target with
  | .live ..=>none
  | .nonlive ..=>none
  | .current _ _ _ _ source ..=>some source

theorem target_payload (before : Before) (tracker : MachineHooks.BorrowState) (id : AllocId) (tag : Option BorTag)
    (target : CurrentCallEmptyClassification.Target before tracker id tag) :
    CurrentCallConversionPlan.payload before id=emptyPayload target := by
  cases target with
  | live entry present parent=>exact CurrentCallConversionPlan.payload_live before id entry present
  | nonlive metadata absent=>exact metadata_payload before tracker id tag metadata
  | current absent noFunction noVaList registry source root current storage compiler cached compatible=>
      exact payload_of_current before id source absent noFunction noVaList current

theorem return_query (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (before : Before)
    (argument : DuplicatePrefixSliceArgument.Argument) (length : UInt64) (place : MPlaceTy Provenance)
    (input : OrdinaryInput options limits remaining span before argument length place) :
    CurrentCallConversionPlan.returnQuery before place=.ok (some input.returnFamily.allocation) := by
  have query:=query_of_selected before input.tracker input.returnFamily input.returnOffset input.returnCapacity
    1 false input.returnRepresentation input.returnBacking (by decide)
  simpa only [CurrentCallConversionPlan.returnQuery,input.returnEncoding,Pointer.withOptionalProvenance] using query

theorem positive_source_query (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (before : Before)
    (argument : DuplicatePrefixSliceArgument.Argument) (length : UInt64) (place : MPlaceTy Provenance)
    (input : OrdinaryInput options limits remaining span before argument length place) (positive : length≠0) :
    ∃family offset capacity,argument=.pointer family.value ∧
      SelectedPointer before input.tracker family offset capacity ∧
      (LiveRole before input.tracker family offset length capacity true ∨
       LatentRole before input.tracker family offset length capacity true) ∧
      CurrentCallConversionPlan.sourceQuery before argument length=.ok (some family.allocation) := by
  rcases input.source with ⟨zero,_⟩|⟨_,fits,family,offset,capacity,encoding,_,_,selected,backing,_⟩
  · exact False.elim (positive zero)
  · refine ⟨family,offset,capacity,encoding,selected,backing,?_⟩
    rw [encoding]
    exact query_of_selected before input.tracker family offset capacity length true selected backing fits

/-- The admitted positive ABI yields the exact source-then-Bool IDs consumed
by the lower plan, without any successful execution premise. -/
theorem positive_rows (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (before : Before)
    (argument : DuplicatePrefixSliceArgument.Argument) (length : UInt64) (place : MPlaceTy Provenance)
    (input : OrdinaryInput options limits remaining span before argument length place) (positive : length≠0) :
    ∃family offset capacity,argument=.pointer family.value ∧
      SelectedPointer before input.tracker family offset capacity ∧
      (LiveRole before input.tracker family offset length capacity true ∨
       LatentRole before input.tracker family offset length capacity true) ∧
      CurrentCallConversionPlan.selectedRows before argument length place=
        CurrentCallConversionPlan.rowsFromIds before (some family.allocation) (some input.returnFamily.allocation) := by
  obtain ⟨family,offset,capacity,encoding,selected,backing,query⟩:=
    positive_source_query options limits remaining span before argument length place input positive
  exact ⟨family,offset,capacity,encoding,selected,backing,
    CurrentCallConversionPlan.selected_of_queries before argument length place _ _ query
      (return_query options limits remaining span before argument length place input)⟩

/-- Empty-source selection reuses the existing exhaustive CURRENT classifier.
Its current payload converts, live/nondata/dead/integer/miss alternatives do
not. The return allocation is still the actual nonempty selected Bool. -/
theorem empty_rows (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (before : Before)
    (argument : DuplicatePrefixSliceArgument.Argument) (length : UInt64) (place : MPlaceTy Provenance)
    (input : OrdinaryInput options limits remaining span before argument length place) (zero : length=0) :
    ∃selected : CurrentCallEmptyClassification.Source before input.tracker argument,
      CurrentCallConversionPlan.selectedRows before argument length place=
        CurrentCallConversionPlan.rowsFromIds before (emptyId selected) (some input.returnFamily.allocation) := by
  have physical : EmptySource before input.tracker (DuplicatePrefixSliceArgument.placePointer argument) := by
    rcases input.source with ⟨_,physical,_⟩|⟨positive,_⟩
    · exact physical
    · exact False.elim (positive zero)
  let selected:=CurrentCallEmptyClassification.classify physical
  refine ⟨selected,CurrentCallConversionPlan.selected_of_queries before argument length place _ _ ?_
    (return_query options limits remaining span before argument length place input)⟩
  exact (congrArg (fun n=>CurrentCallConversionPlan.sourceQuery before argument n) zero).trans
    (empty_query before input.tracker argument physical selected)

end DuplicatePrefix.CurrentCallConversionPlanAdequacy

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "CurrentCallConversionPlanAdequacy.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved conversion plan adequacy dependency {name}: {dependency}"
