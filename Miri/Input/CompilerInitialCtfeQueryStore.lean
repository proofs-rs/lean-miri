import Miri.Input.CompilerInitialCtfeRootResult
import Miri.Input.CtfeQueryBridge

/-! Run-owned typed query completion for the checked fresh literal-u32 slice.
No frontend memo is invented or inferred from equal allocation bytes. The
initial selected keys are empty ONLY because their four captured memberships
were absent. Successful completion follows the real Codegen→PostAnalysis
provider dependencies; capability/fuel/diagnostic failures are NOT cache values.
The public state can only be initialized and advanced through this provider. -/
namespace Miri.Input.CompilerInitialCtfeQueryStore
open Miri.Memory Miri.ABI Miri.Interpreter CompilerInitialAllocation
set_option autoImplicit false
inductive Answer where
  | value (type : TypeId) (value : UInt32)
  | allocation (type : TypeId) (root : AllocId)
  deriving Repr, DecidableEq
private structure Entry where
  key : CtfeQueryBridge.QueryKey
  answer : Answer
  deriving DecidableEq
structure State where
  private mk ::
  compiler : CompilerProviders.Prepared
  image : AllocationImage.Imported
  types : RuntimeArrayTypes.World
  allocations : AllocatorWorld Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind
  run : Nat
  roots : Array CompilerInitialCtfeRootSource.Registered
  private entries : Array Entry := #[]
  blocked : Bool := false
  lastPCs : Array (Nat × Nat) := #[]
  executions : Nat := 0

/-- Persistent query data ONLY. Memory and the type arena are supplied afresh
from the current runtime machine at every callback. Constructors/entries remain
owned by this provider; callers cannot seed answers from compatible bytes. -/
structure Memo where
  private mk ::
  run : Nat
  roots : Array CompilerInitialCtfeRootSource.Registered
  private entries : Array Entry
  blocked : Bool
  lastPCs : Array (Nat × Nat)
  executions : Nat

def State.memo (state : State) : Memo :=
  ⟨state.run,state.roots,state.entries,state.blocked,state.lastPCs,state.executions⟩

/-- Reattach current memory/types after runtime/local allocations. This is NOT
fresh initialization: current counters are allowed to have advanced, and prior
success/failure memo effects must not be reset. -/
def Memo.attach (memo : Memo) (compiler : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (types : RuntimeArrayTypes.World)
    (allocations : AllocatorWorld Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind) : Except String State := do
  unless allocations.memory.activeInitialCompilerRun == some memo.run &&
      allocations.runs.any (fun row => row.1 == memo.run) do
    throw "runtime CTFE memo does not own the active shared source counter"
  for source in memo.roots do
    let actual ← match ← types.instances.lookup source.callee with
      | .material key | .constructed key => pure key
    unless actual == source.query.global.callee do throw "runtime CTFE source instance left current World"
    let .constructed (.template key) ← types.bodies.lookup source.body.identity.index
      | throw "runtime CTFE source body key absent from current World"
    unless key == source.key && key.role == .ctfe do throw "runtime CTFE source body role/key changed"
  pure ⟨compiler,image,types,allocations,memo.run,memo.roots,memo.entries,memo.blocked,memo.lastPCs,memo.executions⟩

def memoSize (state : State) : Nat := state.entries.size
def cached (state : State) (key : CtfeQueryBridge.QueryKey) : Option Answer :=
  (state.entries.find? (fun row => decide (row.key = key))).map (·.answer)
private def complete (state : State) (key : CtfeQueryBridge.QueryKey) (answer : Answer) : State :=
  {state with entries := state.entries.push ⟨key,answer⟩}

def init (compiler : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (types : RuntimeArrayTypes.World) (preparedRoots : Array CompilerInitialCtfeRootSource.Prepared)
    (run : Nat) (allocations : AllocatorWorld Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind) : Except String State := do
  let roots := preparedRoots.map CompilerInitialCtfeRootSource.Prepared.registered
  let some (_,initialNext) := allocations.runs.find? (fun row => row.1 == run)
    | throw "selected CTFE provider run absent"
  unless allocations.memory.live.isEmpty && allocations.memory.dead.isEmpty do
    throw "selected CTFE provider is limited to the pre-runtime query boundary"
  let mut seen : Array CtfeQueryBridge.QueryKey := #[]
  for source in roots do
    unless source.initialNext == initialNext && source.freshness.definition == source.query.global.callee.definition &&
        source.query.family == .value && source.query.environment == CompilerTypingEnv.fullyMonomorphized do
      throw "selected CTFE provider source/frozen run boundary mismatch"
    if seen.any (fun key => decide (key = source.query)) then throw "ambiguous selected CTFE root query"
    seen := seen.push source.query
    let actual ← match ← types.instances.lookup source.callee with
      | .material key | .constructed key => pure key
    unless actual == source.query.global.callee do throw "selected CTFE provider instance left actual World"
    let .constructed (.template key) ← types.bodies.lookup source.body.identity.index
      | throw "selected CTFE provider body key absent"
    unless key == source.key && key.role == .ctfe do throw "selected CTFE provider physical body role differs"
  pure ⟨compiler,image,types,allocations,run,roots,#[],false,#[],0⟩

private def postKey (key : CtfeQueryBridge.QueryKey) (family : CtfeQueryBridge.Family) : CtfeQueryBridge.QueryKey :=
  {key with family,environment := {key.environment with mode := .postAnalysis}}
private def valueFromAllocation (state : State) (type : TypeId) (root : AllocId) : Except String Answer := do
  let shape ← match ← state.types.arena.lookupType type with
    | .constructed value => pure (some value) | .material node => state.types.arena.materialKey node
  unless shape == some (.integer false .u32) do throw "cached allocation result is not actual World u32"
  let some global := state.allocations.memory.findGlobal? root | throw "completed CTFE allocation global absent"
  let some (.memory allocation) := global.payload | throw "completed CTFE root has no memory payload"
  unless allocation.mutability == .Not do throw "completed CTFE root is not immutable"
  let scalar ← (allocation.readScalar state.compiler.runtime.target.base (allocRange .ZERO (Size.ofBytes 4)) false).mapError toString
  pure (.value type (← scalar.toUInt32.mapError reprStr))

/-- Actual typed provider hook. Cold admitted roots execute the real engine;
repeated queries reuse only results derived from its genuine allocated root. -/
def evaluateWith (execute : CompilerInitialCtfeRootResult.Engine) (key : CtfeQueryBridge.QueryKey) : CtfeQueryBridge.Action State String Answer := fun initial => Id.run do
  let state := {initial with lastPCs := #[]}
  if state.blocked then return (.error (.unsupported "selected CTFE source scope closed after an unsupported/failing prefix"),state)
  if let some answer := cached state key then return (.ok answer,state)
  let selected := state.roots.filter (fun source => decide (source.query.global = key.global))
  let some source := selected[0]? | return (.error (.unsupported "query has no selected raw CTFE source"),state)
  unless selected.size == 1 do return (.error (.unsupported "ambiguous selected raw CTFE source"),state)
  let empty := source.query.environment.paramEnv
  unless key.environment.paramEnv == empty && (key.environment.mode == .codegen || key.environment.mode == .postAnalysis) do
    return (.error (.unsupported "selected CTFE provider typing environment outside guarded domain"),state)
  if key.family == .staticInitializer then return (.error (.unsupported "selected Const root is not a static initializer"),state)
  let allocationKey := postKey key .allocation
  let valueKey := postKey key .value
  let mut state := state
  let mut allocationAnswer := cached state allocationKey
  if allocationAnswer.isNone then
    let activeSource ← match CompilerInitialCtfeRootSource.Registered.forProviderKey source allocationKey with
      | .ok source => pure source
      | .error error => return (.error (.unsupported error),state)
    let attempted := execute state.compiler state.image state.types activeSource state.allocations
    state := {state with allocations := attempted.allocations,types := attempted.types,blocked := attempted.blocked,executions := state.executions+1}
    match attempted.outcome with
    | .error error =>
      return (.error (.unsupported s!"selected CTFE engine: {error}; diagnostic-result memoization is outside this source slice"),{state with blocked := true})
    | .ok result =>
      let answer := Answer.allocation result.type result.root
      state := complete {state with lastPCs := result.pcs} allocationKey answer
      allocationAnswer := some answer
  let some (.allocation type root) := allocationAnswer
    | return (.error (.internal "typed CTFE allocation memo has a value-family result"),{state with blocked := true})
  if key.family == .allocation then
    let answer := Answer.allocation type root
    if key.environment.mode == .codegen then state := complete state key answer
    return (.ok answer,state)
  let answer ← match cached state valueKey with
    | some (.value type value) => pure (Answer.value type value)
    | some _ => return (.error (.internal "typed CTFE value memo has allocation-family result"),{state with blocked := true})
    | none =>
      match valueFromAllocation state type root with
      | .error error => return (.error (.unsupported error),{state with blocked := true})
      | .ok answer =>
        state := complete state valueKey answer
        pure answer
  if key.environment.mode == .codegen then state := complete state key answer
  return (.ok answer,state)
end Miri.Input.CompilerInitialCtfeQueryStore
