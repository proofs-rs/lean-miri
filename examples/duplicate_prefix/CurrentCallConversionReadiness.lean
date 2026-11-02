import duplicate_prefix.CurrentCallConversionPlan
import duplicate_prefix.CurrentCallConversionChoiceProtocol

/-! Initial typed choice and allocator readiness for the selected CTFE
conversions. The protocol describes actual current tape inputs/policy and pure
cache/pool updates, not callback success. A strict exhausted tape can fail even
at probability zero; malformed typed inputs are not repaired by fallback.
A reused address is also checked against its bucket's alignment. Only an
initial managed non-type-ID miss requires that otherwise unused pool property.
All existing choice policies and all legal supplied choices remain available. -/
namespace DuplicatePrefix.CurrentCallConversionReadiness
open Miri Miri.ABI Miri.Memory Miri.Interpreter
open Miri.Memory.AllocAddresses
open CurrentCallConversionChoiceProtocol
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Pure current-data test; cached targets, type IDs and external address mode
do not sample the managed reuse pool. The numerical budget's conservative
superset is deliberately not used as the selected choice-request sequence. -/
def managedMiss (before : CurrentCallConversionPlan.Before) (ids : List AllocId) : Bool :=
  before.user.addresses.addressMode==.managed && ids.any fun id=>
    (before.user.addresses.baseAddr.find? (fun row=>row.allocId==id)).isNone &&
      ((before.memory.getAllocInfo id).toOption.map (fun info=>info.kind !=.typeId)).getD false

/-- Every field concerns INITIAL data and is independent of the count. -/
structure Ready (before : CurrentCallConversionPlan.Before)
    (argument : DuplicatePrefixSliceArgument.Argument) (length : UInt64) (place : MPlaceTy Provenance) : Prop where
  protocol : ∃finalAddresses finalTape,
    AddressProtocol before.memory (UInt32.ofNat before.threads.activeThread.toNat)
      before.user.addresses before.user.payload.payload.user.choices
      (CurrentCallConversionPlan.selectedIds before argument length place) finalAddresses finalTape
  poolAligned : managedMiss before (CurrentCallConversionPlan.selectedIds before argument length place)=true→
    ∀generation,before.user.addresses.generation=some generation→BucketsAligned generation.reusePool

theorem managedMiss_of_member (before : CurrentCallConversionPlan.Before) (ids : List AllocId)
    (id : AllocId) (info : AllocationInfo) (mode : before.user.addresses.addressMode=.managed)
    (member : id∈ids) (uncached : before.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=none)
    (metadata : before.memory.getAllocInfo id=.ok info) (nonTypeId : info.kind≠.typeId) :
    managedMiss before ids=true := by
  simp only [managedMiss,mode,beq_self_eq_true,Bool.true_and]
  apply List.any_eq_true.mpr
  refine ⟨id,member,?_⟩
  simp [uncached,metadata,nonTypeId,Except.toOption]

theorem Ready.aligned {before : CurrentCallConversionPlan.Before}
    {argument : DuplicatePrefixSliceArgument.Argument} {length : UInt64} {place : MPlaceTy Provenance}
    (ready : Ready before argument length place) (id : AllocId) (info : AllocationInfo)
    (mode : before.user.addresses.addressMode=.managed)
    (member : id∈CurrentCallConversionPlan.selectedIds before argument length place)
    (uncached : before.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=none)
    (metadata : before.memory.getAllocInfo id=.ok info) (nonTypeId : info.kind≠.typeId)
    (generation : AddressGenerationState) (present : before.user.addresses.generation=some generation) :
    BucketsAligned generation.reusePool :=
  ready.poolAligned (managedMiss_of_member before _ id info mode member uncached metadata nonTypeId) generation present

end DuplicatePrefix.CurrentCallConversionReadiness

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "CurrentCallConversionReadiness.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved initial conversion readiness dependency {name}: {dependency}"
