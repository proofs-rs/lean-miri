import empty_function.AddressChoicePlan
import empty_function.InputDraft

/-! Bind choice demand to actual ordered compiler relocation rows and actual
extern symbol selection. Plans are derived from this raw binding, rather than
accepted as an arbitrary environment-supplied plan. Whole-call demand inclusion
and runtime choice preservation remain separate proof obligations. -/
namespace EmptyFunction.SourceChoicePlan
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open WholeCall EmptyFunction.ChoiceSupply EmptyFunction.AddressChoicePlan
set_option autoImplicit false

/-- Existing shim/weak pointers need no root-address request. An exported
winner takes the actual root-address path for its resolved backing ID. -/
def selectedAddress (s : Static) (before : State) (definition : DefId) (backing : AllocId) :
    ExternMapping.Selection s before definition backing → Option AllocId
  | .shim .. => none
  | .weak .. => none
  | .exported .. => some backing

/-- Raw branch precedence for one actual source relocation. The direct case
uses ordinary declaration metadata; foreign cases use the real selected symbol
mapping. A fabricated no-draw branch has no constructor. -/
inductive Demand (s : Static) (before : State) (declared : AllocId) : Option AllocId → Prop where
  | direct
      (mapping : ExternMapping.Target s before declared declared)
      (format : ∀ global, before.machine.memory.findGlobal? declared = some global →
        ∀ definition isStatic tls foreign,
        global.payload = some (.static definition isStatic tls foreign) →
        tls = false ∧ foreign = false) : Demand s before declared (some declared)
  | foreign (global : GlobalAllocation) (definition : DefId) (backing : AllocId)
      (descriptor : before.machine.memory.findGlobal? declared = some global)
      (payload : global.payload = some (.static definition true false true))
      (selection : ExternMapping.Selection s before definition backing) :
        Demand s before declared (selectedAddress s before definition backing selection)

/-- The same raw metadata record assembled by MachineAddress for an uncached
root-address attempt. The actual lookup is pure current data; no address,
materialization or choice operation is assumed to succeed. -/
def info (before : State) (id : AllocId) : Except AllocationLookupError AllocAddresses.AllocationAddressInfo :=
  (before.machine.memory.getAllocInfo id).map fun metadata => {
    kind := if metadata.kind == .dead then .dead else if metadata.kind == .typeId then .typeId else .liveData
    live := before.machine.memory.isAllocLive id
    size := metadata.size
    align := metadata.align
    memoryKind := some .other
    thread := UInt32.ofNat before.machine.threads.activeThread.toNat }

/-- Relocation order updates the actual pure address state. Repeated targets
therefore use newly cached bases, and reuse-pool removals affect later requests.
Missing metadata is an explicit non-choice halt, never a successful no-draw case. -/
def ordered (before : State) : (demands : List (Option AllocId)) →
    AllocAddresses.GlobalAddressState → Plan (3*demands.length)
  | [], _ => .done
  | none::rest, current => by
      simpa only [List.length_cons,Nat.mul_add,Nat.mul_one,Nat.add_assoc,Nat.reduceAdd] using
        (((ordered before rest current).pad).pad).pad
  | some id::rest, current => by
      let continuation := ordered before rest
      let stage : Plan (3*rest.length+3) :=
        if (current.baseAddr.find? (fun row => row.allocId == id)).isSome then
          (((continuation current).pad).pad).pad
        else match info before id with
          | .error error => .halted (reprStr error)
          | .ok metadata => AddressChoicePlan.attempt current id metadata continuation
      simpa only [List.length_cons,Nat.mul_add,Nat.mul_one,Nat.add_assoc,Nat.reduceAdd] using stage

/-- Ordered raw correspondence, including every occurrence and duplicate. -/
inductive Rows {A B : Type} (relation : A → B → Prop) : List A → List B → Prop where
  | nil : Rows relation [] []
  | cons {a : A} {b : B} {as : List A} {bs : List B} :
      relation a b → Rows relation as bs → Rows relation (a::as) (b::bs)

theorem Rows.length_eq {A B : Type} {relation : A → B → Prop} {as : List A} {bs : List B}
    (rows : Rows relation as bs) : as.length=bs.length := by
  induction rows with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- Only actual source relocation order and current symbol-resolution data
can determine this list. Neither future success nor a demand-trace inclusion
law is a field. Binding-to-machine adequacy must still be proved. -/
structure Binding (s : Static) (before : State) (source : Allocation CtfeProvenance Unit) where
  demands : List (Option AllocId)
  correspondence : Rows
    (fun row demand => Demand s before row.2.allocId demand)
    source.provenanceMap.ptrs.toList demands

def actualPlan {s : Static} {before : State} {source : Allocation CtfeProvenance Unit}
    (binding : Binding s before source) : Plan (3*binding.demands.length) :=
  ordered before binding.demands before.machine.user.addresses

/-- Environment support is bound to the source-derived plan. Whole-call
quantification must range over every current tape satisfying this condition. -/
def Environment {s : Static} {before : State} {source : Allocation CtfeProvenance Unit}
    (binding : Binding s before source) : Prop :=
  ChoiceSupply.Environment (actualPlan binding)
    before.machine.user.payload.payload.user.choices

theorem binding_length {s : Static} {before : State} {source : Allocation CtfeProvenance Unit}
    (binding : Binding s before source) : binding.demands.length = source.provenanceMap.ptrs.size := by
  have same := Rows.length_eq binding.correspondence
  simpa using same.symm

/-- The raw source window reserve bounds all target attempts, including
foreign exported winners and arbitrary repeated cached targets. -/
theorem source_reserve {s : Static} {before : State} {source : Allocation CtfeProvenance Unit}
    (binding : Binding s before source) (physical : InputDraft.CompilerAllocation source) :
    3*binding.demands.length ≤ source.len := by
  have counted := relocation_draw_reserve source.provenanceMap.ptrs.toList source.len
    physical.ordered (by simpa using physical.windows)
  rw [binding_length]
  simp only [addressBudget,Array.length_toList] at counted
  omega

/-- Exact projected-immediate representation which will need an enclosing
stack allocation at Return. The source layout/slot/projection comes from the
current input record, not from a guessed execution endpoint. -/
structure ProjectedBinding (s : Static) (p : Packet) where
  tracker : MachineHooks.BorrowState
  destination : InputDraft.LocalDestination s p tracker
  offset : Size
  projected : destination.offset = some offset
  value : Immediate Provenance
  immediate : destination.oldOperand = .immediate value

/-- The initial allocation-ID supply is processed by the real pure reserve
operation. Failure is retained as a halt without restricting choice supply.
A fresh stack address uses current caller
parent layout and the source stack-kind policy (only one slack request). -/
def projectedPlan {s : Static} {p : Packet} (binding : ProjectedBinding s p) : Plan 3 :=
  match p.before.machine.memory.reserveAllocId with
  | (_, .error error) => .halted (reprStr error)
  | (_, .ok id) =>
      let layout := binding.destination.baseLayout
      let metadata : AllocAddresses.AllocationAddressInfo := {
        kind := .liveData, live := true, size := layout.layout.size,
        align := layout.layout.align.abi, memoryKind := some .stack,
        thread := UInt32.ofNat p.before.machine.threads.activeThread.toNat }
      AddressChoicePlan.attempt p.before.machine.user.addresses id metadata (fun _ => .done)

def ProjectedEnvironment {s : Static} {p : Packet} (binding : ProjectedBinding s p) : Prop :=
  ChoiceSupply.Environment (projectedPlan binding)
    p.before.machine.user.payload.payload.user.choices

end EmptyFunction.SourceChoicePlan

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "EmptyFunction.SourceChoicePlan." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved empty_function source-plan axiom {dependency}"
