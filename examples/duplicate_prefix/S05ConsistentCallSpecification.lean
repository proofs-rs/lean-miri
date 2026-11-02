import duplicate_prefix.S05FixedProfileMetadata

/-! Explicit initial-domain refinement for the fixed duplicate_prefix profile.
The original Contract and Target remain available unchanged. The new goal is
still open: packaging initial consistency does not establish any execution.
-/
namespace DuplicatePrefix.S05ConsistentCallSpecification
open Miri Miri.Input Miri.Memory Miri.ABI Miri.Interpreter
open DuplicatePrefixCallSpecification
set_option autoImplicit false

/-- The existing call-time contract together with explicit initial metadata
compatibility for the selected no-foreign, no-race-clock profile. The added
fields are initial data conditions only: live extras rows exist, have empty
sync metadata and no weak buffer under the model's noDataRace premise, and
array-cache entries satisfy the partial Origins condition.

Origins allows populated array caches. It excludes compiler non-array IDs,
including the slice type queried by the empty path; it does not certify array
layouts, keys, aliases or next-ID allocation. Thus this wrapper is neither full
runtime consistency nor a characterization of all valid Rust callers.

The original Contract did not imply these conditions. This is an explicit
domain refinement, not a proof of the original Target. No operation success,
future permission, return capability or NoUB premise is added. -/
structure ConsistentContract (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (before : Before)
    (argument : DuplicatePrefixSliceArgument.Argument) (len : UInt64) (place : MPlaceTy Provenance) where
  contract : Contract options limits remaining span before argument len place
  metadata : S05FixedProfileMetadata.Compatible before

/-- Revised proof goal with the same actual call and Result as Target, and
only the explicitly refined initial domain. Count remains universal after the
count-independent contract. This definition is not a proved safety theorem;
the empty-entry/body/Return connection (S03), general coverage and resource
sufficiency obligations remain open. -/
def Target : Prop :=
  ∀ (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (before : Before)
    (argument : DuplicatePrefixSliceArgument.Argument) (len : UInt64) (place : MPlaceTy Provenance),
    ConsistentContract options limits remaining span before argument len place →
    ∀ count : UInt64, DuplicatePrefixArgumentCallResult.Result options limits remaining span before argument len count place

/-- Original safety, if established, would cover this refined domain. There
is no converse: metadata compatibility is not derived from the old Contract. -/
theorem target_of_original (original : DuplicatePrefixCallSpecification.Target) : Target := by
  intro options limits remaining span before argument len place input count
  exact original options limits remaining span before argument len place input.contract count

/-- Initial live extras facts consumed by the actual protection/uninit path.
The empty sync array also satisfies the local one-byte separation condition. -/
theorem ConsistentContract.return_extras
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {argument : DuplicatePrefixSliceArgument.Argument} {len : UInt64} {place : MPlaceTy Provenance}
    (input : ConsistentContract options limits remaining span before argument len place) :
    before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == input.contract.destination.id) =
      some (input.contract.destination.id,⟨none,#[]⟩) :=
  input.metadata.return_extras input.contract.destination input.contract.model.noDataRace

/-- The slice field query used by initial FnEntry and the empty shared/len
suffix receives the existing cache-exclusion premise without requiring the
whole cache to be empty. Preservation across execution is a separate proof. -/
theorem ConsistentContract.slice_not_constructed
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {argument : DuplicatePrefixSliceArgument.Argument} {len : UInt64} {place : MPlaceTy Provenance}
    (input : ConsistentContract options limits remaining span before argument len place) :
    before.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false :=
  input.metadata.slice_not_constructed input.contract.model

end DuplicatePrefix.S05ConsistentCallSpecification
