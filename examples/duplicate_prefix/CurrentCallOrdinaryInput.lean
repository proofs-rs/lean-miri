import duplicate_prefix.CurrentCallFamilySpatialAdmission
import duplicate_prefix.CurrentCallBoolProtection
import duplicate_prefix.GlobalAddressLiveErrorExclusion
import duplicate_prefix.GlobalAddressReuseResources
import duplicate_prefix.CurrentCallConversionReadiness

/-! Adopted declarative CURRENT-input target domain for the fixed interpreter.
Every condition below is initial data. There is no operation outcome, adapter,
trace, future resource factory, whole-source completion, or Rust-caller history
certificate. This module does not prove all-count safety for the domain.

Selected-pointer representation is an explicit independent requirement.
ConversionBudget.addresses includes GlobalAddressReuseResources.State's inverse
map, layout and reuse-pool conditions; it is not purely numeric and restricts
existing function/va-list inverse rows. fixedMappings and
fixedRelocationMetadata cover the WHOLE fixed image's relocation list as a
conservative external-metadata requirement, not just selected ABI payloads.
Conversion readiness additionally describes the actual initial typed choice
protocol and, only for a selected managed miss, reuse-pool bucket alignment.
A strict exhausted tape and a misaligned reusable address are real error
branches; numerical room alone does not exclude them. -/
namespace DuplicatePrefix.CurrentCallOrdinaryInput
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open Miri.Memory.AllocAddresses
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CurrentCallSpatialCover CurrentCallFamilySatisfaction
open CandidateFreezeContentResources
set_option autoImplicit false

/-- Physical representation of either runtime or compiler allocation data.
Live byte fragments are allowed; no initialization bit is required of Bool. -/
def Storage {P E : Type} (allocation : Allocation P E) : Prop :=
  allocation.len=allocation.byteSize.bytes.toNat ∧
  InitMaskCopy.WellFormed allocation.initializationMask ∧
  allocation.initializationMask.len=allocation.byteSize ∧
  ProvenanceCopy.WellFormed allocation.provenanceMap allocation.len

def Physical {P E : Type} (allocation : Allocation P E) (offset length : UInt64)
    (initialized : Bool) : Prop :=
  Storage allocation ∧allocation.mutability=.Mut ∧
  offset.toNat+length.toNat≤allocation.byteSize.bytes.toNat ∧
  (initialized=true→∀byte,offset.toNat≤byte→byte<offset.toNat+length.toNat→
    OrdinaryPhysicalValidity.ByteInitialized allocation.initializationMask byte)

/-- CURRENT payloads accepted by the fixed raw global supplier. The static
initializer row is actual imported data, not a successful provider operation.
There is no equality between current globals and the initial compiler catalog. -/
inductive CurrentPayload (before : Before) (id : AllocId)
    (source : Allocation CtfeProvenance Unit) : Prop where
  | memory (descriptor : before.memory.findGlobal? id=some
      ⟨id,.memory,source.byteSize,source.align,source.mutability,some (.memory source)⟩)
  | internalStatic (definition : Nat)
      (descriptor : before.memory.findGlobal? id=some
        ⟨id,.static,source.byteSize,source.align,source.mutability,some (.static definition true false false)⟩)
      (initializer : PreparedReflection.actual.image.initializers.find? (·.1==definition)=some (definition,source))

/-- Named external CTFE format restriction required by adjustFromTcx's ptrs
assertion. Arbitrary finite pointer relocations remain allowed. In particular,
no relocation target address/root is required to be cached by this predicate. -/
def CompilerFormat (source : Allocation CtfeProvenance Unit) : Prop :=
  source.provenanceMap.byteFragments=none

/-- World-bound live ownership uses the SAME actual allocation as storage.
The allocation license states the primary-root/cache representation explicitly. -/
def LiveRole (before : Before) (tracker : MachineHooks.BorrowState) (family : Family)
    (offset length capacity : UInt64) (initialized : Bool) : Prop :=
  ∃entry : LocalAllocation Provenance BorrowTree MiriMemoryKind,
    before.memory.live.find? (fun row=>row.1==family.allocation)=some (family.allocation,entry) ∧
    entry.allocation.byteSize=Size.ofBytes capacity ∧Physical entry.allocation offset length initialized ∧
    AllocationCapability before tracker family.allocation entry.allocation ∧
    Satisfies tracker family entry.allocation (Window family.allocation offset.toNat length.toNat)

/-- A newly materialized tree has no exposed node, including for size zero.
This is a local current-tree fact, not a construction-history assumption. -/
theorem new_no_wildcard_binding (allocation : Allocation Provenance BorrowTree)
    (root : BorTag) (size : Size) (pointer : PointerInstance)
    (shape : allocation.extra=BorrowTree.new root size)
    (wild : pointer.value.provenance=.wildcard) : ¬PointerBinds allocation pointer := by
  rintro ⟨node,found,_,bound⟩
  rw [shape] at found
  have valid := GeneralBorrowNodeUpdate.lookup_valid (BorrowTree.new root size).nodes pointer.grant node found
  have zero : pointer.grant=allocationRoot := GeneralBorrowNodeUpdate.index_injective _ _ (by
    change pointer.grant.toNat<1 at valid
    change pointer.grant.toNat=0
    omega)
  rw [zero] at found
  change (BorrowTree.new root size).nodes.get (⟨0⟩ : UniIndex)=some node at found
  rw [BorrowTree.new_root_node] at found
  cases found
  rw [wild] at bound
  change false=true at bound
  cases bound

/-- Nonempty wildcard satisfaction names an actually exposed CURRENT live
node. Latent roles cannot satisfy this by inventing an exposed fresh root. -/
theorem LiveRole.wildcard_origin {before : Before} {tracker : MachineHooks.BorrowState}
    {family : Family} {offset length capacity : UInt64} {initialized : Bool}
    (role : LiveRole before tracker family offset length capacity initialized)
    (positive : 0<length.toNat) (wild : family.value.provenance=.wildcard) :
    ∃entry : LocalAllocation Provenance BorrowTree MiriMemoryKind,
      before.memory.live.find? (fun row=>row.1==family.allocation)=some (family.allocation,entry) ∧
      ∃grant node,entry.allocation.extra.nodes.get grant=some node ∧node.isExposed=true := by
  obtain ⟨entry,live,_,_,_,owned⟩ := role
  have hit : Window family.allocation offset.toNat length.toNat (family.allocation,offset.toNat) := by
    constructor
    · rfl
    · constructor <;> omega
  obtain ⟨_,grant,chain,binding,_⟩ := owned _ hit
  obtain ⟨node,found,_,exposed⟩ := binding
  change (match family.value.provenance with
    | .concrete id tag=>id=family.allocation ∧tag=node.tag
    | .wildcard=>node.isExposed=true) at exposed
  rw [wild] at exposed
  exact ⟨entry,live,grant,node,found,exposed⟩

/-- Initial metadata coherence for a selected descriptor, not a future
initialization law. Other allocation IDs retain arbitrary registry entries. -/
def InitialRegistryVacant (before : Before) (id : AllocId) : Prop :=
  (before.user.payload.payload.user.runtime.extras.allocations.any (fun row=>row.1==id))=false

/-- A latent entitlement is the fixed owner's exact descriptor footprint in
Composable contents (specified by OrdinaryInput), not invented pre-live raw TB
ownership. Live lookup has priority: an old compiler descriptor cannot select
this branch when a current allocation exists. There is no Supported/empty-map,
callback-result or future-ensure implication in this definition. The selected
latent registry must be vacant because actual initAllocation rejects duplicates. -/
def LatentRole (before : Before) (tracker : MachineHooks.BorrowState) (family : Family) (offset length capacity : UInt64)
    (initialized : Bool) : Prop :=
  before.memory.live.find? (fun row=>row.1==family.allocation)=none ∧
  before.memory.hasFunctionPointer family.allocation=false ∧before.memory.hasVaListId family.allocation=false ∧
  InitialRegistryVacant before family.allocation ∧
  (∃root,family.value.provenance=.concrete family.allocation root ∧tracker.global.rootTag? family.allocation=some root) ∧
  ∃source : Allocation CtfeProvenance Unit,
    CurrentPayload before family.allocation source ∧source.byteSize=Size.ofBytes capacity ∧
    CompilerFormat source ∧Physical source offset length initialized

/-- Initial ABI pointer representation, independent of physical storage and
resource tokens. Missing selected concrete bases are excluded openly: the fixed
resolver reports missingBaseAddress rather than inserting them. Positive wild
references retain the actual exposed allocation and inverse geometry; this
clause does not assume that a selected latent descriptor is already live. Converting relocation
TARGETS is not subject to this initial selected-pointer requirement. -/
def SelectedPointer (before : Before) (tracker : MachineHooks.BorrowState) (family : Family)
    (offset capacity : UInt64) : Prop :=
  ∃base : UInt64,
    before.user.addresses.baseAddr.find? (fun row=>row.allocId==family.allocation)=some ⟨family.allocation,base⟩ ∧
    base.toNat+capacity.toNat<2^64 ∧family.value.offset.bytes.toNat=base.toNat+offset.toNat ∧
    family.value.offset.bytes≠0 ∧
    match family.value.provenance with
    | .concrete id tag => id=family.allocation ∧
        ((∃entry : LocalAllocation Provenance BorrowTree MiriMemoryKind,
          before.memory.live.find? (fun row=>row.1==id)=some (id,entry) ∧
          ∃anchor node,entry.allocation.extra.indexOfTag tag=some anchor ∧entry.allocation.extra.nodeAt anchor=some node) ∨
         (before.memory.live.find? (fun row=>row.1==id)=none ∧tracker.global.rootTag? id=some tag))
    | .wildcard => before.user.addresses.provenanceMode≠AllocAddresses.ProvenanceMode.strict ∧
        before.user.addresses.exposed.contains family.allocation=true ∧
        WildcardGeneralHitReborrow.Geometry before.user.addresses.intToPtrMap family.value.offset.bytes base family.allocation (Size.ofBytes capacity)

/-- Raw zero-size target metadata. No source content family is introduced.
No-relocation maps or relocation-target cache hits are not required here. -/
def ZeroTarget (before : Before) (tracker : MachineHooks.BorrowState) (id : AllocId) (tag : Option BorTag) : Prop :=
  DuplicatePrefixEmptyReferenceInput.Metadata before.memory id tag ∨
  (before.memory.live.find? (fun row=>row.1==id)=none ∧
   before.memory.hasFunctionPointer id=false ∧before.memory.hasVaListId id=false ∧
   InitialRegistryVacant before id ∧
   ∃source root,CurrentPayload before id source ∧Storage source ∧CompilerFormat source ∧
     tracker.global.rootTag? id=some root ∧(tag=none ∨tag=some root))

/-- Exact initial zero-size representation alternatives. For wild values the
raw inverse-table consistency and metadata suppliers are stated, not a success
of resolvePointer. Unlike the older empty Candidate, targets use CurrentPayload
rather than Supported-image/materialization assumptions. -/
def EmptySource (before : Before) (tracker : MachineHooks.BorrowState)
    (pointer : Pointer (Option Provenance)) : Prop :=
  pointer.offset.bytes≠0 ∧match pointer.provenance with
  | none => True
  | some (.concrete id tag) =>
      (∃base,before.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩) ∧
      ZeroTarget before tracker id (some tag)
  | some .wildcard => before.user.addresses.provenanceMode≠AllocAddresses.ProvenanceMode.strict ∧
      GlobalAddressRecurringFormation.State before.memory before.user.addresses ∧
      (∀row∈before.user.addresses.intToPtrMap,GlobalAddressLiveErrorExclusion.Supplier before.memory row.allocId) ∧
      (∀row∈before.user.addresses.intToPtrMap,before.user.addresses.exposed.contains row.allocId=true→
        before.user.addresses.baseAddr.find? (fun entry=>entry.allocId==row.allocId)=some ⟨row.allocId,row.address⟩ ∧
        ZeroTarget before tracker row.allocId none)

/-- Every CURRENT descriptor source that can be converted: memory payloads
are read directly and internal static payloads use the ACTUAL initializer row.
Duplicates are retained, so even two IDs sharing an initializer are counted. -/
def currentConversionInputs (before : Before) : List (Allocation CtfeProvenance Unit) :=
  before.memory.globals.toList.filterMap fun row=>match row.payload with
    | some (.memory source)=>some source
    | some (.static definition true false false)=>
        (PreparedReflection.actual.image.initializers.find? (·.1==definition)).map Prod.snd
    | _=>none

def fixedRelocations : List Relocation :=
  PreparedReflection.actual.image.source.toList.flatMap fun node=>
    node.memory.toList.flatMap (fun memory=>memory.relocations.toList) ++
    (match node.data with | some (.memory memory)=>memory.relocations.toList | _=>[])

/-- A nonrecursive finite upper bound: adjustFromTcx invokes adjustPointer
once for each relocation, not once for each pointed-to allocation's contents.
The fixed initializer/supplier lists are overcounted intentionally. -/
def conversionTargets (before : Before) : List AllocId :=
  ((currentConversionInputs before ++ PreparedReflection.actual.image.initializers.toList.map Prod.snd).flatMap
    (fun source=>source.provenanceMap.ptrs.toList.map (fun row=>row.2.allocId))) ++
  fixedRelocations.filterMap (fun row=>before.memory.runtimeIdForExport? row.target)

def rootMissCount (before : Before) (tracker : MachineHooks.BorrowState) : Nat :=
  ((conversionTargets before).filter (fun id=>(tracker.global.rootTag? id).isNone)).length

def addressMissCount (before : Before) : Nat :=
  ((conversionTargets before).filter (fun id=>(before.user.addresses.baseAddr.find? (fun row=>row.allocId==id)).isNone)).length

def maximumMetadataSize (before : Before) : Nat :=
  ((before.memory.live.toList.map (fun row=>row.2.allocation.byteSize.bytes.toNat)) ++
    before.memory.globals.toList.map (fun row=>row.size.bytes.toNat)).foldr max 1

def maximumMetadataAlignment (before : Before) : Nat :=
  ((before.memory.live.toList.map (fun (row : AllocId × LocalAllocation Provenance BorrowTree MiriMemoryKind)=>2^row.2.allocation.align.pow2)) ++
    before.memory.globals.toList.map (fun (row : GlobalAllocation)=>2^row.align.pow2)).foldr max 1

/-- Checked generator arithmetic uses Fin16 slack (at most 15), a whole
alignment addition before subtraction, and max(size,1). TypeId caching uses
zero without a generator bump and is conservatively charged as well. -/
def addressCharge (before : Before) : Nat :=
  15 + maximumMetadataAlignment before + maximumMetadataSize before

/-- Raw metadata for the REAL globalRootPointer target branches. No target
cache is required. TLS/extern-static dispatch and unavailable static payloads
are outside this fixed metadata scope; function/vtable/typeId/extraFn/va IDs
are included. Address generation uses the same existing ID, never a fresh ID. -/
def RelocationTargetMetadata (before : Before) (id : AllocId) : Prop :=
  GlobalAddressLiveErrorExclusion.Supplier before.memory id ∧
  (match before.memory.findGlobal? id with
   | some global=>match global.payload with
     | some (.static _ _ tls foreign)=>tls=false ∧foreign=false
     | none=>global.kind≠.static
     | _=>True
   | none=>before.memory.hasExtraFunctionId id=true ∨before.memory.hasVaListId id=true) ∧
  ((before.user.addresses.baseAddr.find? (fun row=>row.allocId==id))=none→
    (∀entry : LocalAllocation Provenance BorrowTree MiriMemoryKind,
      before.memory.live.find? (fun row=>row.1==id)=some (id,entry)→entry.allocation.align.pow2≤29) ∧
    (∀global,before.memory.findGlobal? id=some global→global.align.pow2≤29))

/-- Select only descriptor conversions relevant to the ABI; unrelated CURRENT
payloads are used in the conservative NUMERIC bound, not metadata restrictions.
The wild clause also covers zero-size inverse hits on latent descriptors. -/
def SelectedConversion (before : Before) (argument : DuplicatePrefixSliceArgument.Argument)
    (returnId id : AllocId) (source : Allocation CtfeProvenance Unit) : Prop :=
  id=returnId ∨match argument with
  | .integer _=>False
  | .pointer pointer=>match pointer.provenance with
    | .concrete supplied _=>id=supplied
    | .wildcard=>before.user.addresses.exposed.contains id=true ∧∃base,
        WildcardGeneralHitReborrow.Geometry before.user.addresses.intToPtrMap pointer.offset.bytes base id source.byteSize

/-- Numeric/configuration reserve, independent of the requested count. Every
admitted pointer adjustment requests at most one root tag and one address;
managed nonnative conversion allocates NO memory allocation IDs. Existing
Resources reserve the body tags; this adds all initially missing target roots.
Fresh addresses have enough cursor/end space for every possible Fin16 slack.
No recursive cost, successful callback or all-target-cache-hit clause occurs. -/
structure ConversionBudget (before : Before) (tracker : MachineHooks.BorrowState) : Prop where
  fixedMappings : ∀row∈fixedRelocations,∃id,before.memory.runtimeIdForExport? row.target=some id
  rootTags : tracker.global.nextPointerTag.value.toNat + 16 + rootMissCount before tracker < 2^64
  addresses : addressMissCount before=0 ∨∃generation sizes,
    GlobalAddressReuseResources.State before.memory before.user.addresses generation sizes ∧
    Float.le 0.0 generation.reusePool.addressReuseRate=true ∧Float.le generation.reusePool.addressReuseRate 1.0=true ∧
    Float.le 0.0 generation.reusePool.addressReuseCrossThreadRate=true ∧Float.le generation.reusePool.addressReuseCrossThreadRate 1.0=true ∧
    generation.generator.nextBaseAddr.toNat + addressMissCount before * addressCharge before < 2^64 ∧
    generation.generator.nextBaseAddr.toNat + addressMissCount before * addressCharge before ≤generation.generator.endAddr.toNat

/-- All fields are count-independent. Model/settings, numeric margins and
external representation metadata are explicit, separate from chosen ownership.
Latent source and return may name the SAME descriptor: only Composable exact
footprints separate their bytes. Such a dispatcher must ensure once, then take
the Bool LIVE case. Initial WindowReady is required ONLY for an already-live
return allocation. Neither a latent ensure law nor an execution provider occurs. -/
structure OrdinaryInput (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (before : Before)
    (argument : DuplicatePrefixSliceArgument.Argument) (len : UInt64) (place : MPlaceTy Provenance) where
  tracker : MachineHooks.BorrowState
  model : DuplicatePrefixCallModel.Model options remaining span before
  runtime : DuplicatePrefixRuntimeInput.OrderedState before tracker
  defaultMode : tracker.retagMode=.Default
  cacheOrigins : DuplicatePrefixTypeCacheOrigins.Origins before.user.payload.payload.user.types
  stackReady : CurrentCallPush.StackReadiness before #[]
  resources : DuplicatePrefixCallSpecification.Resources options limits remaining before tracker len
  /-- Current allocator consistency, including when there are no LIVE rows:
  in that case the per-allocation `resources.tagsBelow` is vacuous. -/
  protectorsBelow : ∀ row ∈ tracker.global.protectedTags.entries,
    row.1.value.toNat < tracker.global.nextPointerTag.value.toNat
  conversionBudget : ConversionBudget before tracker
  conversionReady : CurrentCallConversionReadiness.Ready before argument len place
  actual : Array (Pointer (Option Provenance))
  assignment : Assignment actual
  sourceOccurrence : Nat
  returnOccurrence : Nat
  sourceActual : actual[sourceOccurrence]?=some (DuplicatePrefixSliceArgument.placePointer argument)
  returnActual : actual[returnOccurrence]?=some place.mplace.ptr
  Fs : Fragment
  Fr : Fragment
  sourceOwner : Nat
  returnOwner : Nat
  composable : Composable Fs Fr
  returnFamily : Family
  returnBound : assignment.Binds returnOccurrence returnFamily
  returnOffset : UInt64
  returnCapacity : UInt64
  returnEncoding : place.mplace.ptr=returnFamily.value.withOptionalProvenance
  returnLayout : place.layout=RootCompilerFacts.boolLayout
  returnAligned : place.mplace.misaligned=none
  returnCharge : CurrentCallPointwiseSpatialCover.ExactCharge Fr returnOwner .ret returnFamily.allocation returnOffset.toNat 1
  returnRepresentation : SelectedPointer before tracker returnFamily returnOffset returnCapacity
  relocationMetadata : ∀id source,before.memory.live.find? (fun row=>row.1==id)=none→
    CurrentPayload before id source→SelectedConversion before argument returnFamily.allocation id source→
    ∀row∈source.provenanceMap.ptrs,RelocationTargetMetadata before row.2.allocId
  fixedRelocationMetadata : ∀row∈fixedRelocations,∀id,
    before.memory.runtimeIdForExport? row.target=some id→RelocationTargetMetadata before id
  returnBacking : LiveRole before tracker returnFamily returnOffset 1 returnCapacity false ∨
    LatentRole before tracker returnFamily returnOffset 1 returnCapacity false
  returnReady : (∃entry : LocalAllocation Provenance BorrowTree MiriMemoryKind,
      before.memory.live.find? (fun row=>row.1==returnFamily.allocation)=some (returnFamily.allocation,entry))→
    CurrentCallBoolProtection.WindowReady before returnFamily.allocation returnOffset.toNat 1
  source : (len=0 ∧EmptySource before tracker (DuplicatePrefixSliceArgument.placePointer argument) ∧
      (∀byte,Fs byte sourceOwner≠some ⟨.mut,.active⟩)) ∨
    (len≠0 ∧len.toNat<9223372036854775808 ∧∃family offset capacity,
      argument=.pointer family.value ∧assignment.Binds sourceOccurrence family ∧
      CurrentCallPointwiseSpatialCover.ExactCharge Fs sourceOwner .mut family.allocation offset.toNat len.toNat ∧
      SelectedPointer before tracker family offset capacity ∧
      (LiveRole before tracker family offset len capacity true ∨LatentRole before tracker family offset len capacity true) ∧
      ((∃entry : LocalAllocation Provenance BorrowTree MiriMemoryKind,
        before.memory.live.find? (fun row=>row.1==family.allocation)=some (family.allocation,entry))→
        CurrentCallBoolProtection.WindowReady before family.allocation offset.toNat len.toNat))

  /-- Independent current address-assignment coherence, including exposed IDs
  unrelated to either argument. Absolute runtime pointer construction caches
  its base before exposure; free clears exposure before GC forgets dead bases.
  This is not implied by bare expose_provenance or the recurring State. -/
  exposedCached : ∀id,before.user.addresses.exposed.contains id=true→
    ∃base,before.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩

end DuplicatePrefix.CurrentCallOrdinaryInput
