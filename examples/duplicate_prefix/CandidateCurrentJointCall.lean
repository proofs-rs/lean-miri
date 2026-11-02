import duplicate_prefix.CandidateStableCallOwnership
import duplicate_prefix.DuplicatePrefixSliceArgument
import duplicate_prefix.CandidateCallBindings

/-! UNADOPTED current-call candidate. The three predicates below deliberately
separate actual identities, precise content entitlement, and an INITIAL scalar
observation relation. None defines Ordinary/ValidInput or asserts admission,
execution, preservation, or coverage. Address normalization, physical storage,
cache/SIFA coherence, metadata and resources remain separate obligations. -/
namespace DuplicatePrefix.CandidateCurrentJointCall
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.Input
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership
set_option autoImplicit false

abbrev Before := MachineHooks.MachineState MiriMemoryKind Machine.RootUser

def ActualWorld (before : Before) : World :=
  before.memory.live.map fun row => (row.1,row.2.allocation)

/-- One occurrence names one fixed instance, rather than choosing an origin
per byte or access. Equal bits alone do not equate distinct instances. -/
structure Occurrence where
  slot : Nat
  bits : Pointer Provenance

/-- A current root-origin binding, not a historical retag event. Multiple
roots may name the SAME family instance. No old typed handle is required. -/
structure Attachment where
  allocation : AllocId
  root : UniIndex
  family : Nat

structure Identities where
  interpretation : Interpretation
  occurrences : Array Occurrence
  attachments : Array Attachment

/-- Consistency of the LISTED annotations only. Empty annotation arrays satisfy
this predicate; it does not reconstruct or cover actual program copies, ambient
families, or every wildcard root. Such coverage/admission remains OPEN. The
closed packet separately connects its listed A/B family to known dataflow. -/
def StableChoices (data : Identities) : Prop :=
  (∀ occurrence ∈ data.occurrences.toList, ∃ pointer,
    data.interpretation.pointers[occurrence.slot]? = some pointer ∧ pointer.value = occurrence.bits) ∧
  (∀ attachment ∈ data.attachments.toList, ∃ pointer precise,
    data.interpretation.pointers[attachment.family]? = some pointer ∧
    pointer.allocation = attachment.allocation ∧
    (attachment.allocation,precise) ∈ data.interpretation.precise.toList ∧
    precise.completion.parents[attachment.root.toNat]? = some (some pointer.grant))

/-- This binds actual values, not address-cache execution. Protector equality
identifies the current tracker table; it does NOT establish loan/protector
lifetime consistency. The window offsets
still require independent physical pointer normalization before execution.
At length zero there is NO source loan/instance/origin/live-allocation demand. -/
def ActualBindings (before : Before) (argument : DuplicatePrefixSliceArgument.Argument)
    (len : UInt64) (place : MPlaceTy Provenance) (held : ProtectedTags)
    (call : CallLoans) (data : Identities) : Prop :=
  before.borrowTracker.map (fun tracker => tracker.global.protectedTags) = some held ∧
  call.length = len.toNat ∧ StableChoices data ∧
  (∀ pointer ∈ data.interpretation.pointers.toList, ∃ allocation,
    Present (ActualWorld before) pointer.allocation allocation ∧ PointerBinds allocation pointer) ∧
  (0 < len.toNat → ∃ loan pointer,
    data.interpretation.loans[call.sourceOwner]? = some loan ∧
    data.interpretation.pointers[loan.pointer]? = some pointer ∧
    pointer.allocation = call.sourceId ∧ argument = .pointer pointer.value) ∧
  (place.layout = RootCompilerFacts.boolLayout ∧ ∃ loan pointer,
    data.interpretation.loans[call.returnOwner]? = some loan ∧
    data.interpretation.pointers[loan.pointer]? = some pointer ∧
    pointer.allocation = call.returnId ∧ place.mplace.ptr = pointer.value.withOptionalProvenance)

/-- Explicit address-representation boundary: this binds claim offsets to the
actual current cached bases and pointer bits. It is kept OUT of precise content
ownership. Missing-cache formation/admission is not asserted by this candidate.
Together with ActualBindings this prevents relocating a claim to arbitrary
disjoint offsets while keeping the same actual source/return pointer bits. -/
def NormalizedWindows (before : Before) (argument : DuplicatePrefixSliceArgument.Argument)
    (len : UInt64) (place : MPlaceTy Provenance) (call : CallLoans) (data : Identities) : Prop :=
  CandidateCallBindings.SourceBinding before data.interpretation call argument len ∧
  CandidateCallBindings.ReturnBinding before data.interpretation call place

/-- Precise topology/dimensions refer to the actual world's node identities,
but no RAW permission table occurs in this predicate. -/
def PreciseShape (world : World) (interpretation : Interpretation) : Prop :=
  (world.toList.map Prod.fst).Nodup ∧
  (interpretation.precise.toList.map Prod.fst).Nodup ∧
  (∀ id precise, (id,precise) ∈ interpretation.precise.toList → ∃ allocation,
    Present world id allocation ∧ Completes allocation.extra precise.completion ∧
    precise.states.size = allocation.len ∧
    ∀ row ∈ precise.states.toList, row.size = allocation.extra.nodes.data.size)

/-- Joint available Freeze contents. Suspended charges demand no active right;
ambient raw pointers/Cell grants create no content charge by their existence.
All active rights are checked in ONE precise state and completion. -/
def PreciseJoint (world : World) (held : ProtectedTags) (interpretation : Interpretation) : Prop :=
  PreciseShape world interpretation ∧ CandidateFreezeContentResources.Valid interpretation.content ∧
  (∀ (owner : Nat) (loan : Loan), interpretation.loans[owner]? = some loan →
    (∃ pointer, interpretation.pointers[loan.pointer]? = some pointer) ∧
    ∀ parent, loan.parent = some parent → ∃ (earlier : Loan),
      interpretation.loans[parent]? = some earlier ∧ earlier.depth < loan.depth) ∧
  (∀ byte owner charge, interpretation.content byte owner = some charge →
    ∃ loan pointer allocation precise,
      interpretation.loans[owner]? = some loan ∧ interpretation.pointers[loan.pointer]? = some pointer ∧
      pointer.allocation = byte.1 ∧ Present world byte.1 allocation ∧ byte.2 < allocation.len ∧
      (byte.1,precise) ∈ interpretation.precise.toList ∧
      (charge.role = .active → LoanRights allocation held precise pointer byte.2 charge.mode) ∧
      (∀ parent, loan.parent = some parent → ∃ parentLoan parentPointer parentCharge,
        interpretation.loans[parent]? = some parentLoan ∧
        interpretation.pointers[parentLoan.pointer]? = some parentPointer ∧
        parentPointer.allocation = byte.1 ∧
        Below precise.completion parentPointer.grant pointer.grant ∧
        interpretation.content byte parent = some parentCharge ∧ parentCharge.role = .suspended ∧
        CandidateFreezeContentResources.MayDelegate parentCharge.mode charge.mode))

/-- SOURCE-INDEPENDENT INITIAL observation candidate, explicitly stronger than
what a particular operation may need. It is NOT asserted necessary, preserved,
or admitted by every ordinary representation. No cache/profile/resources here. -/
def InitialObservation (world : World) (held : ProtectedTags)
    (interpretation : Interpretation) : Prop :=
  ∀ id allocation precise, Present world id allocation →
    (id,precise) ∈ interpretation.precise.toList →
    ∀ byte, byte < allocation.len → ∀ segment ∈ allocation.extra.locations.entries.toList,
    segment.range.start.toNat ≤ byte → byte < segment.range.stop.toNat →
    ∀ index node, allocation.extra.nodes.get index = some node →
    ∀ kind relation, Allows (PreciseState precise byte index) (held.contains node.tag) kind relation →
      Allows (RawState segment.data index node) (held.contains node.tag) kind relation

def RawRights (allocation : Allocation Provenance BorrowTree) (held : ProtectedTags)
    (precise : PreciseAllocation) (pointer : PointerInstance) (byte : Nat)
    (mode : CandidateFreezeContentResources.Mode) : Prop :=
  ∀ segment ∈ allocation.extra.locations.entries.toList,
    segment.range.start.toNat ≤ byte → byte < segment.range.stop.toNat →
    ∀ index node, allocation.extra.nodes.get index = some node →
      (Below precise.completion index pointer.grant → Allows (RawState segment.data index node)
        (held.contains node.tag) (if mode = .read then .Read else .Write) .LocalAccess) ∧
      (¬ Below precise.completion index pointer.grant → Allows (RawState segment.data index node)
        (held.contains node.tag) (if mode = .read then .Read else .Write) .ForeignAccess)

/-- Separation is DERIVED from available contents, not from unequal allocation
IDs. Thus a Bool destination in the same allocation remains admissible when
its byte is disjoint from the source's active window. -/
theorem source_return_disjoint (interpretation : Interpretation) (call : CallLoans)
    (valid : CandidateFreezeContentResources.Valid interpretation.content)
    (claims : Claims interpretation call) (byte : CandidateFreezeContentResources.Byte)
    (source : Window call.sourceId call.sourceOffset call.length byte)
    (destination : Window call.returnId call.returnOffset 1 byte) : False := by
  exact CandidateFreezeContentResources.active_exclusive_conflict _ valid byte
    call.sourceOwner call.returnOwner .mut .ret claims.1
    ((claims.2.1 byte).mpr source) ((claims.2.2 byte).mpr destination) (by decide)

/-- Projection only: this does not establish representation admission or input
coverage. No callback count, mask, or successful operation is a premise. -/
theorem active_raw (world : World) (held : ProtectedTags) (interpretation : Interpretation)
    (joint : PreciseJoint world held interpretation)
    (observation : InitialObservation world held interpretation)
    (byte : CandidateFreezeContentResources.Byte) (owner : Nat)
    (mode : CandidateFreezeContentResources.Mode)
    (active : interpretation.content byte owner = some ⟨mode,.active⟩) :
    ∃ loan pointer allocation precise,
      interpretation.loans[owner]? = some loan ∧ interpretation.pointers[loan.pointer]? = some pointer ∧
      pointer.allocation = byte.1 ∧ Present world byte.1 allocation ∧ byte.2 < allocation.len ∧
      (byte.1,precise) ∈ interpretation.precise.toList ∧ RawRights allocation held precise pointer byte.2 mode := by
  obtain ⟨loan,pointer,allocation,precise,loanAt,pointerAt,id,present,bound,preciseAt,rights,_⟩ :=
    joint.2.2.2 byte owner _ active
  refine ⟨loan,pointer,allocation,precise,loanAt,pointerAt,id,present,bound,preciseAt,?_⟩
  intro segment member lower upper index node nodeAt
  have selected := rights rfl index node nodeAt
  exact ⟨fun ancestry => observation _ _ _ present preciseAt _ bound _ member lower upper _ _ nodeAt _ _ (selected.1 ancestry),
    fun outside => observation _ _ _ present preciseAt _ bound _ member lower upper _ _ nodeAt _ _ (selected.2 outside)⟩

theorem source_raw (before : Before) (held : ProtectedTags) (data : Identities) (call : CallLoans)
    (joint : PreciseJoint (ActualWorld before) held data.interpretation)
    (claims : Claims data.interpretation call)
    (observation : InitialObservation (ActualWorld before) held data.interpretation)
    (byte : CandidateFreezeContentResources.Byte) (inside : Window call.sourceId call.sourceOffset call.length byte) :
    ∃ loan pointer allocation precise,
      data.interpretation.loans[call.sourceOwner]? = some loan ∧
      data.interpretation.pointers[loan.pointer]? = some pointer ∧ pointer.allocation = byte.1 ∧
      Present (ActualWorld before) byte.1 allocation ∧ byte.2 < allocation.len ∧
      (byte.1,precise) ∈ data.interpretation.precise.toList ∧ RawRights allocation held precise pointer byte.2 .mut :=
  active_raw _ _ _ joint observation byte call.sourceOwner .mut ((claims.2.1 byte).mpr inside)

theorem return_raw (before : Before) (held : ProtectedTags) (data : Identities) (call : CallLoans)
    (joint : PreciseJoint (ActualWorld before) held data.interpretation)
    (claims : Claims data.interpretation call)
    (observation : InitialObservation (ActualWorld before) held data.interpretation)
    (byte : CandidateFreezeContentResources.Byte) (inside : Window call.returnId call.returnOffset 1 byte) :
    ∃ loan pointer allocation precise,
      data.interpretation.loans[call.returnOwner]? = some loan ∧
      data.interpretation.pointers[loan.pointer]? = some pointer ∧ pointer.allocation = byte.1 ∧
      Present (ActualWorld before) byte.1 allocation ∧ byte.2 < allocation.len ∧
      (byte.1,precise) ∈ data.interpretation.precise.toList ∧ RawRights allocation held precise pointer byte.2 .ret :=
  active_raw _ _ _ joint observation byte call.returnOwner .ret ((claims.2.2 byte).mpr inside)

end DuplicatePrefix.CandidateCurrentJointCall

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CandidateCurrentJointCall." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved current-joint candidate dependency {dependency}"
