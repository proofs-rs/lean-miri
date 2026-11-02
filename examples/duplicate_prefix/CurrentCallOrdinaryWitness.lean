import duplicate_prefix.CurrentCallConversionTargetAdequacy
import Miri.Input.InitialMachine

/-! A concrete positive CURRENT/CURRENT input for the declared domain.

One mutable three-byte descriptor contains source bytes [0,2) and the Bool
return slot [2,3). Both pointers use the same cached allocation/root; there
are no initial LIVE allocations, protectors or exposed IDs. The fixed image's
15 distinct relocation targets deliberately all map to this one runtime ID.
`OrdinaryInput` permits this synthetic current registry independently of the
initial compiler catalog. This is not an injective-catalog or Rust-history
formation certificate, nor an example of initial LIVE ownership.

`input` constructs all fields on ONE state. Only the existing fixed span and
two JSON-comparator contracts remain parameters. No operation-success, NoUB,
future producer or post-entry certificate is assumed. `nonempty` packages
this conditional inhabitant; CurrentCallOrdinaryWitnessSafety connects it to
the original safety theorem at length 2/count 1. -/
namespace DuplicatePrefix.CurrentCallOrdinaryWitness
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.Input
open Miri.TreeBorrows Miri.Concurrency Miri.Memory.AllocAddresses
open CurrentCallOrdinaryInput CurrentCallSpatialCover CurrentCallFamilySatisfaction
open CandidateFreezeContentResources
open CandidateStableCallOwnership
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
set_option cbv.maxSteps 4000000
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail
noncomputable section

def id : AllocId := ⟨1, by decide⟩
def tag : BorTag := ⟨1, by decide⟩
def bytes : Allocation CtfeProvenance Unit :=
  (Allocation.fromBytes #[11,22,0] Align.ONE .Mut).toOption.get (by decide +kernel)
def descriptor : GlobalAllocation := ⟨id,.memory,Size.ofBytes 3,Align.ONE,.Mut,some (.memory bytes)⟩
/-- All distinct fixed relocation targets; `fixed_ids` checks coverage. -/
def exportTargets : List Nat := [15,64,73,88,99,155,164,206,218,291,313,319,410,499,624]
-- The domain allows current descriptors independently of the original catalog.
def memory : MemoryState Provenance BorrowTree MiriMemoryKind :=
  {((MemoryState.empty.setGlobalEntries #[descriptor]).setIssuedIds #[id]).setImportedGlobalIds
    (exportTargets.map fun target => (target,id)).toArray with nextAllocId:=2}
def tracker : MachineHooks.BorrowState :=
  ⟨{nextPointerTag := ⟨32,by decide⟩,rootPointerTags := #[(id,tag)]},.Default⟩
def host : Machine.MinimalHost := ⟨⟨0,0,0,.virtual 0,0,false⟩,#[]⟩
def store : MachineGCRoots.Storage Unit Unit Unit Unit Unit Unit Unit where
  threads := {affinity:=none}
  tls := ⟨ThreadTlsData.initial,#[],#[]⟩
  errnoPlaces := #[]
  unwindPayloads := .empty
  extras := {allocations:=#[]}
  environment := .uninit
  directories := {}
  descriptors := {}
  ownership := {}
  entry := ⟨none,none,none,none⟩
  externStatics := {}
def world : EvalWorld.World Unit Unit Unit Unit Unit Unit Unit Unit Machine.MinimalHost where
  runtime := store
  main := none
  types := {PreparedReflection.actual.types with entries:=#[]}
  functions := ⟨#[],#[]⟩
  vtables := ⟨#[]⟩
  choices := {inputs:=#[]}
  backend := .none
  host := host
def addresses : GlobalAddressState where
  intToPtrMap := #[⟨4096,id⟩]
  baseAddr := #[⟨id,4096⟩]
  provenanceMode := .permissive
  addressMode := .managed
  generation := some ⟨⟨12288,9223372036854775807⟩,⟨0,0,#[]⟩⟩
def before : CurrentCallConversionPlan.Before where
  memory := memory
  borrowTracker := some tracker
  dataRace := none
  threads := ThreadManager.initial true
  raceAllocations := #[]
  allocationSpans := #[]
  user := ⟨addresses,
    ⟨⟨⟨ThreadId.MAIN_THREAD,#[]⟩,⟨0⟩,world⟩,.Shallow,.Int,false,#[]⟩,#[]⟩
def source : Family := ⟨0,id,Pointer.new (.concrete id tag) (Size.ofBytes 4096)⟩
def ret : Family := ⟨1,id,Pointer.new (.concrete id tag) (Size.ofBytes 4098)⟩
def place : MPlaceTy Provenance := ⟨⟨ret.value.withOptionalProvenance,.none,none⟩,RootCompilerFacts.boolLayout⟩
def actual := #[source.value.withOptionalProvenance,ret.value.withOptionalProvenance]
def Fs : Fragment := fun byte owner => if owner=0 ∧ byte.1=id ∧ byte.2<2 then some ⟨.mut,.active⟩ else none
def Fr : Fragment := fun byte owner => if owner=1 ∧ byte.1=id ∧ byte.2=2 then some ⟨.ret,.active⟩ else none
def budget : Nat := DuplicatePrefixCallSpecification.work before 2 + 1000
def limits : ExecutionMachine.Limits := ⟨budget,budget,budget,budget⟩
def options := Machine.exampleOptions limits budget budget budget budget .Shallow ⟨false,false⟩
theorem mem_eq : before.memory=memory := rfl
theorem no_live : before.memory.live=#[] := by rw [mem_eq]; rfl
theorem enabled : before.borrowTracker=some tracker := rfl
def emptyAssignment : Assignment #[] where
  families := #[]
  references := #[]
  size := rfl
  coherent := by simp
def assignment : Assignment actual :=
  (emptyAssignment.retag ⟨source.allocation,source.value⟩ source.value.withOptionalProvenance ⟨rfl,rfl⟩).retag
    ⟨ret.allocation,ret.value⟩ ret.value.withOptionalProvenance ⟨rfl,rfl⟩

theorem runtime : DuplicatePrefixRuntimeInput.OrderedState before tracker := by
  refine {
    enabled:=enabled
    allocationIds:=?_
    cachedRootIds:=?_
    cachedRootTags:=?_
    tags:=?_
    formed:=?_
    roots:=?_
    coherent:=?_
    possible:=?_
    byteLength:=?_
    maskValid:=?_
    maskLength:=?_
    provenance:=?_
    treeLength:=?_
    parentTags:=?_}
  all_goals first | decide +kernel | simp [no_live]

theorem model (span : PreparedContracts.FixedSpanQuery)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (sourceMatches : (PreparedReflection.actual.runtime.source.raw == PreparedReflection.actual.runtime.source.raw)=true) :
    DuplicatePrefixCallModel.Model options budget span before where
  debugOff := rfl
  preciseOff := rfl
  implicitOff := rfl
  ghostOff := rfl
  shallow := rfl
  defaultTracker := ⟨tracker,enabled,rfl⟩
  noDataRace := rfl
  noBackend := rfl
  metadata := by rfl
  fixedScheduler := rfl
  unchecked := by
    rw [(CanonicalConfigFacts.actual_fields options () (budget+1) span).terminators]
    rfl
  noGc := by
    rw [(CanonicalConfigFacts.actual_fields options () (budget+1) span).terminators]
    rfl
  nullComparator := cmp
  sourceMatches := sourceMatches

theorem fragments : Composable Fs Fr := by
  constructor
  · intro byte a b ca cb different ha hb
    simp only [Fs] at ha hb
    split at ha <;> split at hb <;> simp_all
  constructor
  · intro byte a b ca cb different ha hb
    simp only [Fr] at ha hb
    split at ha <;> split at hb <;> simp_all
  constructor
  · intro byte owner
    by_cases zero : owner=0
    · right; simp [Fr,zero]
    · left; simp [Fs,zero]
  · intro byte a b ca cb ha hb
    simp only [Fs,Fr] at ha hb
    split at ha <;> split at hb <;> simp_all <;> omega

-- Initial metadata facts for the same concrete packet.
theorem fixed_ids : ∀ row∈fixedRelocations,memory.runtimeIdForExport? row.target=some id := by
  have targets : ∀ row∈fixedRelocations,row.target∈exportTargets := by decide +kernel
  have checked : exportTargets.all (fun target=>decide (memory.runtimeIdForExport? target=some id))=true := by cbv
  intro row member
  exact of_decide_eq_true (List.all_eq_true.mp checked row.target (targets row member))

theorem target_only (target : AllocId) (member : target∈conversionTargets before) : target=id := by
  have current : currentConversionInputs before=[bytes] := rfl
  have initializers : PreparedReflection.actual.image.initializers=#[] := rfl
  have ptrs : bytes.provenanceMap.ptrs=#[] := by cbv
  unfold conversionTargets at member
  simp only [current,initializers,Array.toList_empty,List.map_nil,List.append_nil,
    List.flatMap_cons,List.flatMap_nil,ptrs,List.nil_append] at member
  obtain ⟨row,inRows,found⟩ := List.mem_filterMap.mp member
  rw [mem_eq,fixed_ids row inRows] at found
  exact (Option.some.inj found).symm

theorem roots_zero : rootMissCount before tracker=0 := by
  unfold rootMissCount
  have empty : ((conversionTargets before).filter fun target=>(tracker.global.rootTag? target).isNone)=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro target member
    rw [target_only target member]
    cbv
  rw [empty];rfl

theorem addresses_zero : addressMissCount before=0 := by
  unfold addressMissCount
  have empty : ((conversionTargets before).filter fun target=>(before.user.addresses.baseAddr.find? (fun row=>row.allocId==target)).isNone)=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro target member
    rw [target_only target member]
    change ¬ (addresses.baseAddr.find? (fun row=>row.allocId==id)).isNone
    cbv
  rw [empty];rfl
theorem fixed_metadata : RelocationTargetMetadata before id := by
  refine ⟨.globalRow descriptor ?_ ?_ ?_ ?_,?_,?_⟩
  · rw [no_live]; rfl
  · rw [mem_eq]; cbv
  · rw [mem_eq]; cbv
  · rw [mem_eq]; cbv
  · rw [mem_eq]; cbv
  · intro missing
    have cached : before.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,4096⟩ := by rfl
    rw [cached] at missing
    cases missing

theorem latent (family : Family) (offset length : UInt64) (initialized : Bool)
    (value : family.value=Pointer.new (.concrete id tag) (Size.ofBytes (4096+offset)))
    (allocation : family.allocation=id)
    (bounds : offset.toNat+length.toNat≤3) :
    LatentRole before tracker family offset length 3 initialized := by
  unfold LatentRole
  rw [allocation]
  refine ⟨?_,?_,?_,?_,⟨tag,?_,?_⟩,bytes,?_,?_,?_,?_⟩
  · rw [no_live]; rfl
  · rw [mem_eq]; cbv
  · rw [mem_eq]; cbv
  · unfold InitialRegistryVacant
    change (#[] : Array (AllocId × MemoryExtras.AllocationExtra Unit)).any (fun row=>row.1==id)=false
    simp
  · rw [value]; rfl
  · rfl
  · apply CurrentPayload.memory
    rw [mem_eq]; cbv
  · cbv
  · cbv
  · refine ⟨?_,?_,?_,?_⟩
    · refine ⟨by cbv,by cbv,by cbv,?_⟩
      have h : bytes.provenanceMap=ProvenanceMap.new := by cbv
      rw [h]
      constructor <;> simp [ProvenanceMap.new,ProvenanceCopy.FragmentsAvoidPointers]
    · rfl
    · exact bounds
    · intro _ byte lower upper
      cbv

theorem selected (family : Family) (offset : UInt64)
    (value : family.value=Pointer.new (.concrete id tag) (Size.ofBytes (4096+offset)))
    (allocation : family.allocation=id) (small : offset.toNat≤2) :
    SelectedPointer before tracker family offset 3 := by
  refine ⟨4096,?_,by decide,?_,?_,?_⟩
  · rw [allocation]; rfl
  · rw [value]
    change (4096+offset).toNat=4096+offset.toNat
    rw [UInt64.toNat_add]; simp; omega
  · rw [value]
    change 4096+offset≠(0:UInt64)
    intro equal
    have h := congrArg UInt64.toNat equal
    rw [UInt64.toNat_add] at h
    simp at h
    omega
  · rw [value]
    exact ⟨allocation.symm,Or.inr ⟨by rw [no_live];rfl,by rfl⟩⟩

theorem resources : DuplicatePrefixCallSpecification.Resources options limits budget before tracker 2 := by
  refine {
    remainingFuel:=?_
    executionFuel:=?_
    configuredFuel:=?_
    dynamicFuel:=?_
    compatibility:=?_
    tagRoom:=?_
    tagsBelow:=?_
    cachedRootsBelow:=?_
    nodeRoom:=?_
    storageRoom:=?_
    globalRoom:=?_
    initializerRoom:=?_}
  · exact Nat.le_add_right _ _
  · unfold DuplicatePrefixCallSpecification.fuelAtLeast
    exact ⟨Nat.le_add_right _ _,Nat.le_add_right _ _,Nat.le_add_right _ _,Nat.le_add_right _ _⟩
  · unfold DuplicatePrefixCallSpecification.fuelAtLeast
    exact ⟨Nat.le_add_right _ _,Nat.le_add_right _ _,Nat.le_add_right _ _,Nat.le_add_right _ _⟩
  · exact Nat.le_add_right _ _
  · exact Nat.le_add_right _ _
  · decide +kernel
  · simp [no_live]
  · decide +kernel
  · simp [no_live]
  · simp [no_live]
  · change ∀ row∈#[descriptor].toList, _
    decide +kernel
  · decide +kernel

def input (span : PreparedContracts.FixedSpanQuery)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (sourceMatches : (PreparedReflection.actual.runtime.source.raw == PreparedReflection.actual.runtime.source.raw)=true) :
    OrdinaryInput options limits budget span before (.pointer source.value) 2 place where
  tracker := tracker
  model := model span cmp sourceMatches
  runtime := runtime
  defaultMode := rfl
  cacheOrigins := by
    change ∀ entry∈(#[] : Array RuntimeArrayTypes.Entry), _
    simp
  stackReady := by
    refine ⟨ThreadRecord.initial (some [109,97,105,110]) none,?_,?_⟩
    · change (ThreadManager.initial true).activeThread?=some (ThreadRecord.initial (some [109,97,105,110]) none)
      cbv
    · simp [ThreadRecord.initial]
  resources := resources
  protectorsBelow := by simp [tracker]
  conversionBudget := by
    refine ⟨?_,?_,Or.inl ?_⟩
    · intro row member; exact ⟨id,by rw [mem_eq];exact fixed_ids row member⟩
    · rw [roots_zero]
      decide +kernel
    · exact addresses_zero
  conversionReady := by
    have none : CurrentCallConversionPlan.selectedIds before (.pointer source.value) 2 place=[] := by
      simp only [CurrentCallConversionPlan.selectedIds,CurrentCallConversionPlan.selectedPayloads,
        CurrentCallConversionPlan.selectedRows,CurrentCallConversionPlan.rowsFromIds,
        CurrentCallConversionPlan.sourceQuery,CurrentCallConversionPlan.returnQuery,
        CurrentCallConversionPlan.query,CurrentCallConversionPlan.payload,mem_eq,
        show before.user.addresses=addresses from rfl,place,ret,source]
      cbv
    constructor
    · refine ⟨before.user.addresses,before.user.payload.payload.user.choices,?_⟩
      rw [none]
      exact CurrentCallConversionChoiceProtocol.AddressProtocol.nil _ _
    · rw [CurrentCallConversionReadiness.managedMiss,none]
      simp
  actual := actual
  assignment := assignment
  sourceOccurrence := 0
  returnOccurrence := 1
  sourceActual := rfl
  returnActual := rfl
  Fs := Fs
  Fr := Fr
  sourceOwner := 0
  returnOwner := 1
  composable := fragments
  returnFamily := ret
  returnBound := ⟨rfl,rfl⟩
  returnOffset := 2
  returnCapacity := 3
  returnEncoding := rfl
  returnLayout := rfl
  returnAligned := rfl
  returnCharge := by intro byte; simp [Fr,Window,ret] <;> omega
  returnRepresentation := selected ret 2 rfl rfl (by decide)
  relocationMetadata := by
    intro target payload _ current _ row member
    cases current with
    | memory descriptorEq =>
      have memberGlobal := CurrentCallConversionTargetAdequacy.global_member descriptorEq
      change _∈[descriptor] at memberGlobal
      have same := List.mem_singleton.mp memberGlobal
      have payloadEq : payload=bytes := by
        have p := congrArg GlobalAllocation.payload same
        exact GlobalAllocationPayload.memory.inj (Option.some.inj p)
      subst payload
      change row∈(#[] : Array (Size × CtfeProvenance)) at member
      simp at member
    | internalStatic definition descriptorEq initializer =>
      have memberGlobal := CurrentCallConversionTargetAdequacy.global_member descriptorEq
      change _∈[descriptor] at memberGlobal
      have same := List.mem_singleton.mp memberGlobal
      have p := congrArg GlobalAllocation.payload same
      cases p
  fixedRelocationMetadata := by
    intro row member target found
    rw [mem_eq,fixed_ids row member] at found
    cases found
    exact fixed_metadata
  returnBacking := Or.inr (latent ret 2 1 false rfl rfl (by decide))
  returnReady := by simp [no_live]
  source := Or.inr ⟨by decide,by decide,source,0,3,rfl,⟨rfl,rfl⟩,
    by intro byte;simp [Fs,Window,source],selected source 0 rfl rfl (by decide),
    Or.inr (latent source 0 2 true rfl rfl (by decide)),by simp [no_live]⟩
  exposedCached := by
    intro target member
    change (#[] : Array AllocId).contains target=true at member
    simp at member

theorem nonempty (span : PreparedContracts.FixedSpanQuery)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (sourceMatches : (PreparedReflection.actual.runtime.source.raw == PreparedReflection.actual.runtime.source.raw)=true) :
    Nonempty (OrdinaryInput options limits budget span before (.pointer source.value) 2 place) :=
  ⟨input span cmp sourceMatches⟩

#print axioms nonempty

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CurrentCallOrdinaryWitness." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved concrete witness dependency {name}: {dependency}"

end
end DuplicatePrefix.CurrentCallOrdinaryWitness
