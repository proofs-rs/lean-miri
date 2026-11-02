import empty_function.Specification
namespace EmptyFunction.DispatcherSkeleton
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open EmptyFunction.WholeCall EmptyFunction.InputDraft
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false

/-- Actual lookup precedence, expressed entirely as current raw table facts. -/
inductive Registry (s : Static) (p : Packet) (id : AllocId) : Prop where
  | live (entry : Entry)
      (lookup : p.before.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry)) : Registry s p id
  | function (absent : p.before.machine.memory.live.find? (fun row => row.1 == id) = none)
      (present : p.before.machine.memory.hasFunctionPointer id = true) : Registry s p id
  | vaList (absent : p.before.machine.memory.live.find? (fun row => row.1 == id) = none)
      (noFunction : p.before.machine.memory.hasFunctionPointer id = false)
      (present : p.before.machine.memory.hasVaListId id = true) : Registry s p id
  | global (absent : p.before.machine.memory.live.find? (fun row => row.1 == id) = none)
      (noFunction : p.before.machine.memory.hasFunctionPointer id = false)
      (noVaList : p.before.machine.memory.hasVaListId id = false)
      (entry : GlobalAllocation) (present : p.before.machine.memory.findGlobal? id = some entry)
      (backing : Backing s p.before id) : Registry s p id
  | dead (absent : p.before.machine.memory.live.find? (fun row => row.1 == id) = none)
      (noFunction : p.before.machine.memory.hasFunctionPointer id = false)
      (noVaList : p.before.machine.memory.hasVaListId id = false)
      (noGlobal : p.before.machine.memory.findGlobal? id = none)
      (entry : DeadAllocation)
      (present : p.before.machine.memory.dead.find? (fun row => row.allocId == id) = some entry) : Registry s p id

theorem registry (s : Static) (p : Packet) (id : AllocId) (backing : Backing s p.before id) :
    Registry s p id := by
  classical
  cases hl : p.before.machine.memory.live.find? (fun row => row.1 == id) with
  | some row =>
    have identity : row.1 = id := by
      have member := Array.find?_some hl
      simpa using member
    cases row with
    | mk found entry => simp only at identity;subst found;exact .live entry hl
  | none =>
    cases hf : p.before.machine.memory.hasFunctionPointer id with
    | true => exact .function hl hf
    | false =>
      cases hv : p.before.machine.memory.hasVaListId id with
      | true => exact .vaList hl hf hv
      | false =>
        cases hg : p.before.machine.memory.findGlobal? id with
        | some entry => exact .global hl hf hv entry hg backing
        | none =>
          cases backing with
          | live entry present => rw [hl] at present;cases present
          | global entry present _ _ _ _ => rw [hg] at present;cases present
          | extraFunction extra =>
            unfold MemoryState.hasFunctionPointer at hf
            unfold MemoryState.hasExtraFunctionId at extra
            simp [extra] at hf
          | vaList present => rw [hv] at present;cases present
          | dead entry present _ _ _ _ => exact .dead hl hf hv hg entry present

/-- A wildcard candidate is selected by raw nearest-key geometry and exposure,
not by an assumed successful operational resolver. -/
def Candidate (p : Packet) (pointer : Pointer (Option Provenance)) (row : AllocAddresses.InverseAddressEntry) : Prop :=
  row ∈ p.before.machine.user.addresses.intToPtrMap ∧
  p.before.machine.user.addresses.exposed.contains row.allocId = true ∧
  WildcardCandidate p.before pointer row

inductive PointerView (s : Static) (p : Packet) (pointer : Pointer (Option Provenance)) : Prop where
  | integer (encoding : pointer.provenance = none) : PointerView s p pointer
  | concrete (id : AllocId) (tag : BorTag)
      (encoding : pointer.provenance = some (.concrete id tag))
      (registry : Registry s p id) : PointerView s p pointer
  | wildcardMiss (encoding : pointer.provenance = some .wildcard)
      (absent : ¬ ∃ row, Candidate p pointer row) : PointerView s p pointer
  | wildcardHit (encoding : pointer.provenance = some .wildcard)
      (row : AllocAddresses.InverseAddressEntry) (candidate : Candidate p pointer row)
      (registry : Registry s p row.allocId) : PointerView s p pointer

theorem pointer_view (s : Static) (p : Packet) (tracker : MachineHooks.BorrowState)
    (pointer : Pointer (Option Provenance)) (input : PointerInput s p.before tracker pointer) :
    PointerView s p pointer := by
  classical
  cases input with
  | integer encoding => exact .integer encoding
  | concrete id tag base tables encoding cached backing parent latent =>
    exact .concrete id tag encoding (registry s p id backing)
  | wildcard encoding mode tables selected =>
    by_cases hit : ∃ row, Candidate p pointer row
    · obtain ⟨row,candidate⟩ := hit
      exact .wildcardHit encoding row candidate
        (registry s p row.allocId (selected row candidate.1 candidate.2.1 candidate.2.2))
    · exact .wildcardMiss encoding hit

inductive LocalView {s : Static} {p : Packet} {tracker : MachineHooks.BorrowState}
    (destination : LocalDestination s p tracker) : Prop where
  | wholeImmediate (value : Immediate Provenance) (whole : destination.offset = none)
      (encoding : destination.oldOperand = .immediate value) : LocalView destination
  | wholeIndirect (place : MemPlace Provenance) (whole : destination.offset = none)
      (encoding : destination.oldOperand = .indirect place) : LocalView destination
  | projectedImmediate (offset : Size) (value : Immediate Provenance)
      (projected : destination.offset = some offset)
      (encoding : destination.oldOperand = .immediate value) : LocalView destination
  | projectedIndirect (offset : Size) (place : MemPlace Provenance)
      (projected : destination.offset = some offset)
      (encoding : destination.oldOperand = .indirect place) : LocalView destination

theorem local_view {s : Static} {p : Packet} {tracker : MachineHooks.BorrowState}
    (destination : LocalDestination s p tracker) : LocalView destination := by
  cases offset : destination.offset <;> cases operand : destination.oldOperand with
  | immediate value => first | exact .wholeImmediate value offset operand | exact .projectedImmediate _ value offset operand
  | indirect place => first | exact .wholeIndirect place offset operand | exact .projectedIndirect _ place offset operand

inductive DestinationView (s : Static) (p : Packet) (input : CurrentInputDraft s p) : Prop where
  | localCase (destination : LocalDestination s p input.tracker) (view : LocalView destination) : DestinationView s p input
  | memory (destination : MemoryDestination s p input.tracker)
      (view : PointerView s p destination.place.mplace.ptr) : DestinationView s p input

theorem partition (s : Static) (p : Packet) (input : CurrentInputDraft s p) : DestinationView s p input := by
  rcases input.destination with localInput | memoryInput
  · obtain ⟨destination⟩ := localInput
    exact .localCase destination (local_view destination)
  · obtain ⟨destination⟩ := memoryInput
    exact .memory destination (pointer_view s p input.tracker _ destination.pointer)

/-- These are INTERNAL family theorem obligations, not initial-state validity
fields. The dispatcher has no implementation of missing cases. In particular,
projected/latent/local mixed kinds cannot be dropped by declaring them invalid. -/
structure FamilyTheorems (s : Static) (ResourceFamily : Packet → Prop) : Prop where
  localFamily : ∀ (metadata : Specification.Metadata s) (profile : Specification.Profile s)
    (p : Packet) (runtime : Specification.RuntimeProfile s p) (input : CurrentInputDraft s p),
    ResourceFamily p → ∀ destination : LocalDestination s p input.tracker,
    LocalView destination → WholeCall.Result s (Preservation.Preserves s) p
  memoryFamily : ∀ (metadata : Specification.Metadata s) (profile : Specification.Profile s)
    (p : Packet) (runtime : Specification.RuntimeProfile s p) (input : CurrentInputDraft s p),
    ResourceFamily p → ∀ destination : MemoryDestination s p input.tracker,
    PointerView s p destination.place.mplace.ptr → WholeCall.Result s (Preservation.Preserves s) p

/-- Pure exhaustive assembly skeleton. Supplying FamilyTheorems is still OPEN;
this theorem is neither CandidateTarget nor a proof of the missing operations. -/
theorem assemble (s : Static) (ResourceFamily : Packet → Prop)
    (families : FamilyTheorems s ResourceFamily)
    (metadata : Specification.Metadata s) (profile : Specification.Profile s)
    (p : Packet) (runtime : Specification.RuntimeProfile s p) (input : CurrentInputDraft s p)
    (resources : ResourceFamily p) : WholeCall.Result s (Preservation.Preserves s) p := by
  cases partition s p input with
  | localCase destination view => exact families.localFamily metadata profile p runtime input resources destination view
  | memory destination view => exact families.memoryFamily metadata profile p runtime input resources destination view

end EmptyFunction.DispatcherSkeleton

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.DispatcherSkeleton.").length != 1 then
      count := count+1
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved dispatcher skeleton axiom {name}: {dependency}"
  logInfo m!"Audited {count} dispatcher declarations; family proofs remain obligations"
