import duplicate_prefix.DuplicatePrefixCallModel
import duplicate_prefix.DuplicatePrefixRuntimeInput
import duplicate_prefix.DuplicatePrefixReturnPlaceInput
import duplicate_prefix.DuplicatePrefixArgumentCallResult
import duplicate_prefix.DuplicatePrefixEmptyReferenceInput

namespace DuplicatePrefix.DuplicatePrefixCallSpecification
open Miri Miri.Input Miri.Memory Miri.ABI Miri.Interpreter

abbrev Before := MachineHooks.MachineState MiriMemoryKind Machine.RootUser

/-- Concrete initial-data budget proposal, not a proved execution bound.
Later proofs must establish sufficiency or revise this formula explicitly.
It has no operation, outcome, trace, or final-state parameter. -/
def work (before : Before) (len : UInt64) : Nat :=
  64 + len.toNat + (before.memory.live.toList.map fun row =>
    row.2.allocation.len + 32 * row.2.allocation.extra.nodes.size +
      32 * row.2.allocation.extra.locations.entries.size).sum +
    (before.memory.globals.toList.map fun row => row.size.bytes.toNat).sum +
    (PreparedReflection.actual.image.initializers.toList.map fun row =>
      row.2.len + 16 * row.2.provenanceMap.ptrs.size).sum

def fuelAtLeast (budget : Nat) (limits : ExecutionMachine.Limits) : Prop :=
  budget ≤ limits.callDispatch ∧ budget ≤ limits.casts ∧
    budget ≤ limits.retag ∧ budget ≤ limits.validation

set_option autoImplicit false in
/-- Explicit numeric resource candidate. Sixteen tag/node slots and the fuel
formula are conservative proposals, not ordinary reference-validity clauses
and not yet certified sufficient. No empty free pool is required. High-water
facts are stated on raw tag maps/protector entries, not on successful inserts. -/
structure Resources (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (before : Before) (tracker : MachineHooks.BorrowState) (len : UInt64) : Prop where
  remainingFuel : work before len ≤ remaining
  executionFuel : fuelAtLeast (work before len) limits
  configuredFuel : fuelAtLeast (work before len) options.limits
  dynamicFuel : work before len ≤ options.place.dynamicFuel
  compatibility : work before len ≤ options.compatibilityBudget
  tagRoom : tracker.global.nextPointerTag.value.toNat + 16 < 2^64
  tagsBelow : ∀ row ∈ before.memory.live.toList,
    GeneralBorrowForestTagHighWater.Below row.2.allocation.extra
      tracker.global.protectedTags tracker.global.nextPointerTag
  cachedRootsBelow : ∀ row ∈ tracker.global.rootPointerTags.toList,
    row.2.value.toNat < tracker.global.nextPointerTag.value.toNat
  nodeRoom : ∀ row ∈ before.memory.live.toList, row.2.allocation.extra.nodes.size + 16 < 65536
  storageRoom : ∀ row ∈ before.memory.live.toList, row.2.allocation.len + 64 < 2^64
  globalRoom : ∀ row ∈ before.memory.globals.toList, row.size.bytes.toNat + 64 < 2^64
  initializerRoom : ∀ row ∈ PreparedReflection.actual.image.initializers.toList, row.2.len + 64 < 2^64

/-- Lazy-image evidence is bound to the actual imported compiler and prestate,
never existentially chosen to make metadata appear supported. -/
def imageContext (options : EvalConfigurationCore.Options) (before : Before)
    (tracker : MachineHooks.BorrowState) : DuplicatePrefixEmptyReferenceInput.ImageContext where
  runtime := PreparedReflection.actual.compiler.runtime.target
  initializers := PreparedReflection.actual.image.initializers
  rootTags := tracker.global.rootPointerTags
  extraAllocationIds := before.user.payload.payload.user.runtime.extras.allocations.map Prod.fst
  nativeLibraryPathsEmpty :=
    ((Machine.leaves PreparedReflection.actual.prepared options.place.debugAssertions).pointerSource.nativeLibraryPaths
      before.user.payload.payload.user.host).isEmpty

set_option autoImplicit false in
/-- Reference alternatives in the proposed domain. Empty references use raw
zero-size metadata authorization, including provenance-free dangling addresses.
Positive references bind a real provenance-carrying pointer to live backing.
TypedMemoryProviders.resolvePointer returns an unresolved address immediately
for no-provenance values, even in permissive mode; integer-to-wildcard casts
are a distinct representation, not an implicit positive-reference alternative.
Ordinary-valid coverage of the normalization remains unproved. -/
inductive Reference (options : EvalConfigurationCore.Options) (before : Before)
    (tracker : MachineHooks.BorrowState) (argument : DuplicatePrefixSliceArgument.Argument) (len : UInt64) where
  | empty (zero : len = 0)
      (metadata : DuplicatePrefixEmptyReferenceInput.Candidate (imageContext options before tracker)
        before.memory before.user.addresses (DuplicatePrefixSliceArgument.placePointer argument))
  | positive (pointer : Pointer Provenance)
      (encoding : argument = .pointer pointer)
      (input : DuplicatePrefixReferenceInput.Positive before pointer len)

set_option autoImplicit false in
/-- Provisional normalized call-time contract, with independent named groups.
All conditions describe initial data. No successful helper, interpreter step,
target invocation, final permission/activity or NoUB field is admitted.

This is NOT a definition of all ordinary valid Rust callers. Residual-subset
authorization, base-address normalization, static consistency choices, numeric
budget and the canonical empty-stack harness require coverage/justification.
S02-S05 must remove excess conditions or revise this candidate, never declare
all-input safety merely by proving this candidate's target. The fixed result
uses the original actual call and the physical bool return place. -/
structure LegacyContract (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (before : Before)
    (argument : DuplicatePrefixSliceArgument.Argument) (len : UInt64) (place : MPlaceTy Provenance) where
  model : DuplicatePrefixCallModel.Model options remaining span before
  tracker : MachineHooks.BorrowState
  runtime : DuplicatePrefixRuntimeInput.State before tracker
  reference : Reference options before tracker argument len
  destination : DuplicatePrefixReturnPlaceInput.Input before place
  separated : len = 0 ∨ (DuplicatePrefixSliceArgument.address argument).toNat + len.toNat ≤ destination.pointer.offset.bytes.toNat ∨
    destination.pointer.offset.bytes.toNat + 1 ≤ (DuplicatePrefixSliceArgument.address argument).toNat
  thread : Miri.Concurrency.ThreadRecord
  active : before.threads.activeThread? = some thread
  emptyHarnessCache : thread.topUserRelevantFrame = none
  resources : Resources options limits remaining before tracker len


/-- Strengthened working contract: the additional ordered-state premise is
explicit. LegacyContract preserves the original domain; no all-valid-input
coverage or completion follows from this narrowing. -/
structure Contract (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (before : Before)
    (argument : DuplicatePrefixSliceArgument.Argument) (len : UInt64) (place : MPlaceTy Provenance) where
  model : DuplicatePrefixCallModel.Model options remaining span before
  tracker : MachineHooks.BorrowState
  runtime : DuplicatePrefixRuntimeInput.OrderedState before tracker
  reference : Reference options before tracker argument len
  destination : DuplicatePrefixReturnPlaceInput.Input before place
  separated : len = 0 ∨ (DuplicatePrefixSliceArgument.address argument).toNat + len.toNat ≤ destination.pointer.offset.bytes.toNat ∨
    destination.pointer.offset.bytes.toNat + 1 ≤ (DuplicatePrefixSliceArgument.address argument).toNat
  thread : Miri.Concurrency.ThreadRecord
  active : before.threads.activeThread? = some thread
  emptyHarnessCache : thread.topUserRelevantFrame = none
  resources : Resources options limits remaining before tracker len

/-- The exact proposed safety statement for the provisional contract. This is
a DEFINITION OF A PROOF GOAL, not a proved theorem or an added axiom. Count is
universally quantified after the count-independent contract; no branch success
or generated-history factory is assumed. Complete valid-input coverage and
the canonical-harness reduction remain separate mandatory obligations. -/
def Target : Prop :=
  ∀ (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (before : Before)
    (argument : DuplicatePrefixSliceArgument.Argument) (len : UInt64) (place : MPlaceTy Provenance),
    Contract options limits remaining span before argument len place →
    ∀ count : UInt64, DuplicatePrefixArgumentCallResult.Result options limits remaining span before argument len count place

/-- Preserve the original, broader proof goal instead of silently erasing it. -/
def LegacyTarget : Prop :=
  ∀ (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (before : Before)
    (argument : DuplicatePrefixSliceArgument.Argument) (len : UInt64) (place : MPlaceTy Provenance),
    LegacyContract options limits remaining span before argument len place →
    ∀ count : UInt64, DuplicatePrefixArgumentCallResult.Result options limits remaining span before argument len count place

/-- Forget ONLY the newly added static order premise. -/
def Contract.toLegacy {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {argument : DuplicatePrefixSliceArgument.Argument} {len : UInt64} {place : MPlaceTy Provenance}
    (input : Contract options limits remaining span before argument len place) :
    LegacyContract options limits remaining span before argument len place := {
  model := input.model
  tracker := input.tracker
  runtime := input.runtime.toState
  reference := input.reference
  destination := input.destination
  separated := input.separated
  thread := input.thread
  active := input.active
  emptyHarnessCache := input.emptyHarnessCache
  resources := input.resources }

/-- The old goal implies the narrowed goal; the converse is not claimed. -/
theorem target_of_legacy (old : LegacyTarget) : Target := by
  intro options limits remaining span before argument len place input count
  exact old options limits remaining span before argument len place input.toLegacy count

end DuplicatePrefix.DuplicatePrefixCallSpecification
