import Miri.Interpreter.MachineAddress
import Lean

/-! Raw environmental choice supply for the empty-function proof. A Unit
external configuration still reads this tape at actual address requests.
Halted plans retain non-choice algorithm errors and accept the remaining tape;
choice supply never implies address-operation success. This file proves typed
request legality from raw entries. It does not prove
that every empty_function path follows a supplied request plan; that connection is an
explicit remaining implementation obligation. No diagnostic seed is selected.
-/
namespace EmptyFunction.ChoiceSupply
open Miri Miri.ABI Miri.Memory Miri.Interpreter ExecutionChoices
set_option autoImplicit false

inductive IndexKind where
  | slack | pool
  deriving DecidableEq, Repr

def IndexKind.site : IndexKind → IndexSite
  | .slack => .addressSlack
  | .pool => .addressPool

inductive BoolKind where
  | reuse | crossThread
  deriving DecidableEq, Repr

def BoolKind.site : BoolKind → BoolSite
  | .reuse => .addressReuse
  | .crossThread => .addressCrossThread

inductive AddressRequest where
  | index (kind : IndexKind) (count : Nat)
  | bernoulli (kind : BoolKind) (rateBits : UInt64)
  deriving Repr

def sourceRequest : AddressRequest → ExecutionChoices.Request
  | .index kind count => .index kind.site count
  | .bernoulli kind bits => .bernoulli kind.site bits

/-- Every value in the source support is admitted. Probability support uses
rand's exact threshold, including endpoint probabilities and tiny rates. -/
inductive Supported : AddressRequest → Input → Prop where
  | index (kind : IndexKind) (count value : Nat) (bound : value < count) :
      Supported (.index kind count) (.index kind.site value)
  | bernoulli (kind : BoolKind) (rateBits : UInt64) (value validFalse : Bool)
      (probability : TerminatorMachine.permitsPreemption rateBits false = .ok validFalse)
      (support : TerminatorMachine.permitsPreemption rateBits value = .ok true) :
      Supported (.bernoulli kind rateBits) (.boolean kind.site value)

/-- The exact source tape bookkeeping, independent of machine operations. -/
def advance (tape : Tape) (request : AddressRequest) (input : Input) : Tape :=
  {tape with cursor := tape.cursor+1, events := tape.events.push ⟨sourceRequest request,input⟩}

/-- A wrapper around the actual two source choice consumers, solely to state
one typed request theorem. This is not a substitute MIR/address interpreter. -/
def perform {S : Type} (access : Access S) : AddressRequest → ExecutionChoices.M S Input
  | .index kind count => do
      let value ← ExecutionChoices.index access kind.site count
      pure (.index kind.site value)
  | .bernoulli kind rateBits => do
      let value ← ExecutionChoices.bernoulli access kind.site rateBits
      pure (.boolean kind.site value)

/-- Typed head/site/support and strict supplied data suffice for the actual
consumer. No callback, memory access or successful choice is an input field. -/
theorem perform_supported {S : Type} (access : Access S) (state : S) (tape : Tape)
    (request : AddressRequest) (input : Input)
    (current : access.get state = tape) (strict : tape.policy = .strict)
    (head : tape.inputs[tape.cursor]? = some input) (support : Supported request input) :
    perform access request state = .ok input (access.put state (advance tape request input)) := by
  cases support with
  | index kind count value bound =>
    unfold perform
    have actual := ExecutionChoices.index_supplied access state tape kind.site count value
      current strict head bound
    simp only [bind,EStateM.bind,actual,pure,EStateM.pure]
    rfl
  | bernoulli kind rateBits value validFalse probability supported =>
    unfold perform
    have actual := ExecutionChoices.bernoulli_supplied access state tape kind.site rateBits value validFalse
      current strict head probability supported
    simp only [bind,EStateM.bind,actual,pure,EStateM.pure]
    rfl

/-- A finite response-dependent grammar. Subsequent sites/support may depend
on a previous response (reuse controls whether cross-thread/pool is requested).
Done may use less than the remaining numeric draw reserve. -/
inductive Plan : Nat → Type where
  | done {budget : Nat} : Plan budget
  | blocked {budget : Nat} : Plan budget
  | halted {budget : Nat} (reason : String) : Plan budget
  | request {budget : Nat} (nextRequest : AddressRequest)
      (next : (input : Input) → Supported nextRequest input → Plan budget) : Plan (budget+1)

/-- Increase the finite reserve without adding a request or admitting a
blocked branch. Used by cache hits and shorter response-dependent paths. -/
def Plan.pad {budget : Nat} : Plan budget → Plan (budget+1)
  | .done => .done
  | .blocked => .blocked
  | .halted reason => .halted reason
  | .request req next => .request req (fun input supported => (next input supported).pad)

/-- Pure matching of raw entries against a plan, starting at the CURRENT
cursor. It neither runs a machine operation nor predicts successful execution.
Safety must quantify over every tape that fits the actual demand grammar. -/
def Fits {budget : Nat} : Plan budget → Tape → Prop
  | .done, _ => True
  | .blocked, _ => False
  | .halted _, _ => True
  | .request request next, tape =>
      ∃ input, ∃ supported : Supported request input,
        tape.inputs[tape.cursor]? = some input ∧
          Fits (next input supported) (advance tape request input)

/-- Exact chosen-path draw count, including a valid terminal cursor. Padding
changes only the maximum reserve, not the amount of supplied input required. -/
inductive FitsCount : {budget : Nat} → Plan budget → Tape → Nat → Prop where
  | done {budget : Nat} {tape : Tape} (cursor : tape.cursor ≤ tape.inputs.size) :
      FitsCount (Plan.done : Plan budget) tape 0
  | halted {budget : Nat} {tape : Tape} (reason : String)
      (cursor : tape.cursor ≤ tape.inputs.size) :
      FitsCount (Plan.halted reason : Plan budget) tape 0
  | request {budget count : Nat} {req : AddressRequest}
      {next : (input : Input) → Supported req input → Plan budget} {tape : Tape}
      (input : Input) (support : Supported req input)
      (head : tape.inputs[tape.cursor]? = some input)
      (tail : FitsCount (next input support) (advance tape req input) count) :
      FitsCount (.request req next) tape (count+1)

/-- Numeric supply is separate from typed-site/support coherence. A sufficient
reserve does not by itself make an index or Bernoulli response legal. -/
structure Resources (tape : Tape) (budget : Nat) : Prop where
  cursor : tape.cursor ≤ tape.inputs.size
  supplied : tape.cursor+budget ≤ tape.inputs.size

structure Environment {budget : Nat} (plan : Plan budget) (tape : Tape) : Prop where
  strict : tape.policy = .strict
  supplied : ∃ used, FitsCount plan tape used

/-- Exact event/cursor cost of one supplied request, even at probability 0/1. -/
theorem advance_cost (tape : Tape) (request : AddressRequest) (input : Input) :
    (advance tape request input).cursor = tape.cursor+1 ∧
    (advance tape request input).events.size = tape.events.size+1 ∧
    (advance tape request input).inputs = tape.inputs := by
  simp [advance]

theorem resources_tail (tape : Tape) (request : AddressRequest) (input : Input)
    (budget : Nat) (resource : Resources tape (budget+1)) :
    Resources (advance tape request input) budget := by
  constructor <;> simp only [advance]
  · have := resource.supplied; omega
  · have := resource.supplied; omega

/-- Exact maximum source draw cost per address request family: cached bases
make no request; a stack miss requests slack once; another managed miss
requests reuse, optional cross-thread, and one pool/slack selection. -/
inductive AddressFamily where
  | cached | stackMiss | otherMiss
  deriving DecidableEq, Repr

def maxDraws : AddressFamily → Nat
  | .cached => 0
  | .stackMiss => 1
  | .otherMiss => 3

/-- This reserve counts address attempts, not source bytes or a PRNG seed.
The whole-call proof must bound actual attempts by initial relocation/current
projection data and show its response-dependent demand plan has this budget. -/
def addressBudget (stackMisses otherMisses : Nat) : Nat := stackMisses+3*otherMisses

theorem addressBudget_add (stack₁ stack₂ other₁ other₂ : Nat) :
    addressBudget (stack₁+stack₂) (other₁+other₂) =
      addressBudget stack₁ other₁ + addressBudget stack₂ other₂ := by
  simp [addressBudget]; omega

/-- Concrete demand grammar of a stack-address miss: the source requests
one Fin16 slack value and admits every one of its sixteen possibilities. -/
def stackMissPlan : Plan 1 :=
  .request (.index .slack 16) (fun _ _ => .done)

/-- Source grammar for a non-stack managed miss. The pool-size continuation
is computed from current reuse-pool metadata by the eventual address adapter;
none means no reusable candidate, some count requests that pool support.
The adapter must establish positive pool counts and correspondence to the
actual candidate range. This function contains no successful address law. -/
def otherMissPlan (reuseRate crossRate : UInt64)
    (poolCount : Bool → Option Nat) : Plan 3 :=
  .request (.bernoulli .reuse reuseRate) fun input _ =>
    match input with
    | .boolean _ false => .request (.index .slack 16) (fun _ _ => .done)
    | .boolean _ true => .request (.bernoulli .crossThread crossRate) fun input _ =>
      match input with
      | .boolean _ cross =>
        match poolCount cross with
        | none => .request (.index .slack 16) (fun _ _ => .done)
        | some count => .request (.index .pool count) (fun _ _ => .done)
      | _ => .done
    | _ => .done

/-- Cached addresses execute the real source fast path with no choice request
and leave the entire current machine, including its choice tape, unchanged. -/
theorem cached_no_draw {K U : Type}
    (access : Access (MachineAddress.State K U)) (hooks : MachineAddress.Hooks K U)
    (state : MachineAddress.State K U) (id : AllocId) (base : UInt64)
    (kind : Option AllocAddresses.AddressMemoryKind)
    (cached : state.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩) :
    MachineAddress.addrFromAllocId access hooks id kind state = .ok base state := by
  simp [MachineAddress.addrFromAllocId,cached,
    get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure]


/-- Nonoverlapping eight-byte relocation windows bound the number of possible
managed target-address attempts by initial source storage, independently of
whether target roots/bases are already cached. -/
theorem relocation_windows_bound {P : Type} (rows : List (Size × P))
    (lower storage : Nat)
    (frontier : lower ≤ storage)
    (ordered : rows.Pairwise (fun left right => left.1.bytes.toNat+8 ≤ right.1.bytes.toNat))
    (above : ∀ row ∈ rows, lower ≤ row.1.bytes.toNat)
    (bounds : ∀ row ∈ rows, row.1.bytes.toNat+8 ≤ storage) :
    lower + 8*rows.length ≤ storage := by
  induction rows generalizing lower with
  | nil =>
    simp only [List.length_nil,Nat.mul_zero,Nat.add_zero]
    exact frontier
  | cons first rest ih =>
    have order := List.pairwise_cons.mp ordered
    have next := ih (first.1.bytes.toNat+8)
      (bounds first List.mem_cons_self) order.2
      (fun row present => order.1 row present)
      (fun row present => bounds row (List.mem_cons_of_mem first present))
    have initial := above first (List.mem_cons_self)
    simp only [List.length_cons]
    omega

/-- Three draws per relocation fit within the bytes occupied by its ordered
8-byte window. The optional projected-stack attempt adds at most one draw. -/
theorem relocation_draw_reserve {P : Type} (rows : List (Size × P)) (storage : Nat)
    (ordered : rows.Pairwise (fun left right => left.1.bytes.toNat+8 ≤ right.1.bytes.toNat))
    (bounds : ∀ row ∈ rows, row.1.bytes.toNat+8 ≤ storage) :
    addressBudget 1 rows.length ≤ 1+storage := by
  have counted := relocation_windows_bound rows 0 storage (by omega) ordered
    (by intros; omega) bounds
  simp only [addressBudget]
  omega

/-- Padding cannot turn an exhausted or blocked path into a supplied path. -/
theorem fits_pad {budget : Nat} (plan : Plan budget) (tape : Tape) :
    Fits plan.pad tape ↔ Fits plan tape := by
  induction plan generalizing tape with
  | done => rfl
  | blocked => rfl
  | halted _ => rfl
  | request req next ih =>
    simp only [Plan.pad,Fits]
    constructor
    · rintro ⟨input,support,head,tail⟩
      exact ⟨input,support,head,(ih input support _).mp tail⟩
    · rintro ⟨input,support,head,tail⟩
      exact ⟨input,support,head,(ih input support _).mpr tail⟩

/-- A stack miss admits every legal slack but rejects an empty strict suffix. -/
theorem stack_fits (tape : Tape) : Fits stackMissPlan tape ↔
    ∃ value, value < 16 ∧ tape.inputs[tape.cursor]? = some (.index .addressSlack value) := by
  constructor
  · rintro ⟨input,support,head,_⟩
    cases support with
    | index kind count value bound => exact ⟨value,bound,head⟩
  · rintro ⟨value,bound,head⟩
    exact ⟨.index .addressSlack value,Supported.index .slack 16 value bound,head,True.intro⟩

theorem exhausted_stack_rejected (tape : Tape)
    (exhausted : tape.inputs[tape.cursor]? = none) : ¬ Fits stackMissPlan tape := by
  rw [stack_fits]
  rintro ⟨value,_,head⟩
  rw [exhausted] at head
  contradiction

/-- Raw matching gives a bound on actual consumed draws and exactly sufficient
numeric supply. A cache hit/done plan accepts an empty remaining suffix. -/
theorem fitsCount_resources {budget used : Nat} {plan : Plan budget} {tape : Tape}
    (matched : FitsCount plan tape used) : used ≤ budget ∧ Resources tape used := by
  induction matched with
  | done cursor => exact ⟨by omega,⟨cursor,by simpa⟩⟩
  | halted _ cursor => exact ⟨by omega,⟨cursor,by simpa⟩⟩
  | request input support head tail ih =>
    rcases ih with ⟨bounded,resource⟩
    have remaining := resource.supplied
    simp only [advance] at remaining
    constructor
    · omega
    · constructor <;> omega

theorem fits_of_count {budget used : Nat} {plan : Plan budget} {tape : Tape}
    (matched : FitsCount plan tape used) : Fits plan tape := by
  induction matched with
  | done _ => trivial
  | halted _ _ => trivial
  | request input support head _ ih => exact ⟨input,support,head,ih⟩

theorem Environment.fits {budget : Nat} {plan : Plan budget} {tape : Tape}
    (environment : Environment plan tape) : Fits plan tape := by
  obtain ⟨used,matched⟩ := environment.supplied
  exact fits_of_count matched

/-- Choice supply accepts a non-choice algorithm failure. Proving NoErrors
must separately rule out this halted state from raw runtime/resource facts. -/
theorem halted_environment (budget : Nat) (reason : String) (tape : Tape)
    (strict : tape.policy = .strict) (cursor : tape.cursor ≤ tape.inputs.size) :
    Environment (Plan.halted reason : Plan budget) tape :=
  ⟨strict,⟨0,FitsCount.halted reason cursor⟩⟩

end EmptyFunction.ChoiceSupply

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "EmptyFunction.ChoiceSupply." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved empty_function choice-supply axiom {dependency}"
