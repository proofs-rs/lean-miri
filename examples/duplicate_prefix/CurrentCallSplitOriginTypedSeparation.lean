import duplicate_prefix.CurrentCallSplitOriginTypedEntry
import duplicate_prefix.CurrentCallSplitOriginSeparation

/-! Couple the actual constructed typed caller packet to the finite separation
proof. This rejects one uniform-origin representation of its current V pointer;
it is neither a Rust reachability, whole-call, nor UB claim. -/
namespace DuplicatePrefix.CurrentCallSplitOriginTypedSeparation
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.Input
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources CurrentCallResourceNormalization
open CanonicalConfigFacts ActualReferenceContext CurrentCallTypedFnEntry
open CurrentCallSplitOriginTypedInput CurrentCallSplitOriginTypedEntry
open CurrentCallSplitOriginTrace (ix tag)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

theorem no_uniform_input :
    ¬∃ completion,ParentInterpretation sourceAllocation.extra completion ∧
      SpatialDelegation machine tracker sourceId sourceAllocation completion (ix 3) ∧
      ∀ byte,byte<2 → Embeds sourceAllocation tracker.global.protectedTags completion (ix 3) byte .exclusive := by
  have unchanged : sourceAllocation.setExtra CurrentCallSplitOriginTrace.finalWrite.tree=sourceAllocation := rfl
  simpa only [unchanged,show tracker.global.protectedTags={} from rfl] using
    CurrentCallSplitOriginSeparation.no_uniform_origin machine tracker sourceId sourceAllocation

/-- The constructed underlying machine's same source allocation also has no
uniform issued origin. Root-frame preparation changes no source storage. -/
theorem no_uniform_before :
    ¬∃ completion,ParentInterpretation sourceAllocation.extra completion ∧
      SpatialDelegation before tracker sourceId sourceAllocation completion (ix 3) ∧
      ∀ byte,byte<2 → Embeds sourceAllocation tracker.global.protectedTags completion (ix 3) byte .exclusive := by
  have unchanged : sourceAllocation.setExtra CurrentCallSplitOriginTrace.finalWrite.tree=sourceAllocation := rfl
  simpa only [unchanged,show tracker.global.protectedTags={} from rfl] using
    CurrentCallSplitOriginSeparation.no_uniform_origin before tracker sourceId sourceAllocation

/-- Physical source/Bool data, genuine cached bindings, the checked unchanged
compiler cache, uniform-origin separation, and real Strong FnEntry success all
refer to the SAME current packet. Only existing fixed decoder contracts remain. -/
theorem physical_typed_separation (span : PreparedContracts.FixedSpanQuery) (cmp : ProjectionMetadataFacts.NullComparator) :
    OrdinaryPhysicalValidity.MutU8Slice sourceAllocation 0 2 ∧
    OrdinaryPhysicalValidity.BoolDestination destinationAllocation 0 ∧
    destinationAllocation.initializationMask=InitMask.new (Size.ofBytes 1) false ∧
    CandidateCallBindings.WindowBinding machine sourcePointer sourceId 0 2 ∧
    CandidateCallBindings.WindowBinding machine destinationPointer destinationId 0 1 ∧
    machine.user.payload.payload.user.types=PreparedReflection.actual.types ∧
    DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get state) ∧
    (¬∃ completion,ParentInterpretation sourceAllocation.extra completion ∧
      SpatialDelegation machine tracker sourceId sourceAllocation completion (ix 3) ∧
      ∀ byte,byte<2 → Embeds sourceAllocation tracker.global.protectedTags completion (ix 3) byte .exclusive) ∧
    output.global.protectedTags.get (tag 6)=some .StrongProtector ∧
    output.frame.protectedTags=#[(sourceId,tag 6)] ∧
    (∃ ctx : ActualReferenceContext.Context options remaining span,
      TypedRetag.retagPtrValue (adapted options remaining span ctx.pointers) options.limits.retag
        (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base sourcePointer 2 ActualReferenceMetadata.reference)
        ActualReferenceMetadata.reference.ty .FnEntry state =
        .ok (some (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
          (changedPointer sourcePointer sourceId (tag 6)) 2 ActualReferenceMetadata.reference))
          (Storage.withCurrent #[] finalFrame finalMachine) ∧
        finalMachine.borrowTracker=some ⟨output.global,tracker.retagMode⟩ ∧
        finalFrame.extra.borrowTracker=some output.frame ∧ finalFrame.returnPlace=.memory place) := by
  exact ⟨source_physical,destination_physical,destination_uninitialized,source_binding,destination_binding,
    fixed_metadata,cache_origins,no_uniform_input,actual_child.2.2.2.1,actual_child.2.2.2.2.1,typed_fnentry span cmp⟩

end
end DuplicatePrefix.CurrentCallSplitOriginTypedSeparation
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallSplitOriginTypedSeparation" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved typed split-origin coupling dependency {dependency}"
