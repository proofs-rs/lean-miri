import duplicate_prefix.ActualReferenceContext
import duplicate_prefix.ActualRetagContext

namespace DuplicatePrefix.DuplicatePrefixCallModel
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter

set_option autoImplicit false in
/-- Explicit selected interpreter/configuration scope for the call-time target.
These are raw configuration and initial machine facts, not slice validity,
execution success, or resource sufficiency. The library/MIR identities are
fixed by the imports and checked separately by the source/pin/MIR audit.

There is deliberately no root-count, permission profile, allocator noFree,
canonical bool-slot shape, cached-address, absent type-cache entry, special
allocation extras, or outer-stack assumption. Such current adapter restrictions
must not be hidden inside this model scope. Numeric fuel/headroom is separate.
The two opaque JSON comparison facts are explicit external metadata premises. -/
structure Model (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) : Prop where
  debugOff : options.place.debugAssertions = false
  preciseOff : options.retag.preciseInteriorMut = false
  implicitOff : options.retag.implicitWrites = false
  ghostOff : before.user.payload.ghost = false
  shallow : before.user.payload.validation = .Shallow
  defaultTracker : ∃ tracker, before.borrowTracker = some tracker ∧ tracker.retagMode = .Default
  noDataRace : before.dataRace = none
  noBackend : before.user.payload.payload.user.backend = .none
  metadata : before.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime
  fixedScheduler : before.threads.fixedScheduling = true
  unchecked : ((PreparedContracts.actualConfig options () (remaining + 1) span).terminators.getControl
    before.user).checkedArithmetic = false
  noGc : ((PreparedContracts.actualConfig options () (remaining + 1) span).terminators.getControl
    before.user).gcInterval = 0
  nullComparator : ProjectionMetadataFacts.NullComparator
  sourceMatches : (PreparedReflection.actual.runtime.source.raw ==
    PreparedReflection.actual.runtime.source.raw) = true

/-- The reference/retag callback construction certificates follow from the
fixed configuration. They are not operation-success witnesses supplied by a
caller, and neither stage needs a separate assumed Context field. -/
theorem contexts (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (model : Model options remaining span before) :
    Nonempty (ActualReferenceContext.Context options remaining span) ∧
    Nonempty (ActualReferenceContext.Context options (remaining + 1) span) ∧
    Nonempty (ActualRetagContext.Context options remaining span) ∧
    Nonempty (ActualRetagContext.Context options (remaining + 1) span) :=
  ⟨ActualReferenceContext.exists_context options remaining span model.preciseOff model.implicitOff,
    ActualReferenceContext.exists_context options (remaining + 1) span model.preciseOff model.implicitOff,
    ActualRetagContext.exists_context options remaining span model.preciseOff model.implicitOff,
    ActualRetagContext.exists_context options (remaining + 1) span model.preciseOff model.implicitOff⟩

/-- The source-comparison adapter is formed from the explicit raw comparator
premise, without assuming a successful interpreter metadata operation. -/
def sourceComparator (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (model : Model options remaining span before) : PreparedContracts.SourceComparator :=
  ⟨model.sourceMatches⟩

/-- The 64-bit pointer layout is derived from the fixed imported metadata and
configuration builder rather than repeated as a caller premise. -/
theorem pointer_layout (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) :
    (PreparedContracts.actualConfig options () remaining span).arithmetic = ⟨Size.ofBytes 8⟩ ∧
    (PreparedContracts.actualConfig options () remaining span).access.runtime.base.pointerWidth = .w64 ∧
    (PreparedContracts.actualConfig options () remaining span).access.runtime.pointerSize = Size.ofBytes 8 := by
  refine ⟨CanonicalConfigFacts.actual_arithmetic _ _ _ _, CanonicalConfigFacts.actual_target_width _ _ _ _, ?_⟩
  rw [CanonicalConfigFacts.actual_access_runtime]
  rfl

end DuplicatePrefix.DuplicatePrefixCallModel
