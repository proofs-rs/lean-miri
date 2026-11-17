import duplicate_prefix.CandidateStableCallOwnership
import duplicate_prefix.DuplicatePrefixCallSpecification

/-! UNADOPTED actual-call bindings for the unadopted ownership candidate.
These transparent relations identify current machine data, not ordinary-input
coverage or ownership adequacy. Pointer bits do not certify copy identity,
frame/protector lifetimes, exposure-at-origin time, or correlated alternatives.
Those certifications remain unresolved; no history certificate is introduced.
-/
namespace DuplicatePrefix.CandidateCallBindings
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Interpreter
open CandidateStableCallOwnership
set_option autoImplicit false

/-- Strip only the interpreter's local allocation wrapper, retaining every live
allocation and its actual ID, contents and borrow tree. -/
def actualWorld (before : DuplicatePrefixCallSpecification.Before) : World :=
  before.memory.live.map fun row => (row.1, row.2.allocation)

/-- Explicit normalization DATA. Concrete provenance names this allocation;
wildcards retain the actual inverse-map/exposure constraints. This does not
assert an access succeeds, nor derive cache formation from physical validity. -/
def WindowBinding (before : DuplicatePrefixCallSpecification.Before)
    (pointer : Pointer Provenance) (id : AllocId) (offset length : Nat) : Prop :=
  ∃ (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (base : UInt64),
    before.memory.live.find? (fun row => row.1 == id) = some (id, entry) ∧
    before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩ ∧
    entry.allocation.len = entry.allocation.byteSize.bytes.toNat ∧
    base.toNat + entry.allocation.len < 2^64 ∧
    offset + length ≤ entry.allocation.len ∧
    pointer.offset.bytes.toNat = base.toNat + offset ∧
    pointer.offset.bytes ≠ 0 ∧
    (match pointer.provenance with
    | .concrete supplied _ => supplied = id
    | .wildcard => before.user.addresses.provenanceMode ≠ .strict ∧
        before.user.addresses.exposed.contains id = true ∧
        WildcardGeneralHitReborrow.Geometry before.user.addresses.intToPtrMap
          pointer.offset.bytes base id entry.allocation.byteSize)

/-- Owner-to-loan-to-instance lookup is explicit. Equal bits alone never merge
instances or imply that a program copy shares this origin choice. -/
def OwnerBinding (before : DuplicatePrefixCallSpecification.Before)
    (interpretation : Interpretation) (owner : Nat) (pointer : Pointer Provenance)
    (id : AllocId) (offset length : Nat) : Prop :=
  ∃ (loan : Loan) (pointerInstance : PointerInstance),
    interpretation.loans[owner]? = some loan ∧
    interpretation.pointers[loan.pointer]? = some pointerInstance ∧
    pointerInstance.value = pointer ∧ pointerInstance.allocation = id ∧
    WindowBinding before pointer id offset length

/-- Empty source imposes no live allocation, tag, loan or pointer-instance
requirement. Nonnullness is separate ordinary empty-reference address data.
Positive integer encoding cannot satisfy the provenance-carrying branch. -/
def SourceBinding (before : DuplicatePrefixCallSpecification.Before)
    (interpretation : Interpretation) (call : CallLoans)
    (argument : DuplicatePrefixSliceArgument.Argument) (len : UInt64) : Prop :=
  (len = 0 ∧ DuplicatePrefixSliceArgument.address argument ≠ 0) ∨
  (len ≠ 0 ∧ ∃ pointer, argument = .pointer pointer ∧
    OwnerBinding before interpretation call.sourceOwner pointer
      call.sourceId call.sourceOffset call.length)

/-- The return footprint is one byte at the actual typed bool place, with the
actual optional provenance preserved. Initialization/value validity is absent. -/
def ReturnBinding (before : DuplicatePrefixCallSpecification.Before)
    (interpretation : Interpretation) (call : CallLoans)
    (place : MPlaceTy Provenance) : Prop :=
  place.layout = RootCompilerFacts.boolLayout ∧
  ∃ pointer, place.mplace.ptr = pointer.withOptionalProvenance ∧
    OwnerBinding before interpretation call.returnOwner pointer call.returnId call.returnOffset 1

/-- Minimal actual mapping only, not a full physical/environment envelope.
`held` is exactly the enabled tracker table, not certified frame ownership.
Claims/Interprets remain separate candidate clauses on this SAME interpretation.
This record proves neither candidate adoption nor Candidate ⇒ Contract. -/
structure Bindings (before : DuplicatePrefixCallSpecification.Before)
    (world : World) (held : ProtectedTags) (interpretation : Interpretation)
    (call : CallLoans) (argument : DuplicatePrefixSliceArgument.Argument)
    (len : UInt64) (place : MPlaceTy Provenance) : Prop where
  world_eq : world = actualWorld before
  protectors : ∃ tracker, before.borrowTracker = some tracker ∧ held = tracker.global.protectedTags
  length_eq : call.length = len.toNat
  source : SourceBinding before interpretation call argument len
  destination : ReturnBinding before interpretation call place

end DuplicatePrefix.CandidateCallBindings

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CandidateCallBindings." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved actual-call binding dependency {dependency}"
