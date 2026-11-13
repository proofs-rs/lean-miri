import Miri.Input.CompilerInitialSelectedMemoWorld

/-! Successful cached selected-query slice. The persistent Memo is memory-free;
Current is supplied afresh by the owning run for every request. Cold allocation
misses remain Unsupported until an actual child CTFE engine is connected. -/
namespace Miri.Input.CompilerInitialSelectedMemo
open Miri.Memory Miri.ABI CompilerInitialAllocation
set_option autoImplicit false
variable {P E K : Type}
structure Current (P E K : Type) where
  target : TargetDataLayout
  types : RuntimeArrayTypes.World
  allocations : AllocatorWorld P E K
structure Attempt (P E K : Type) where
  outcome : Except (CtfeQueryBridge.Failure String) Answer
  memo : Memo
  current : Current P E K

private def evaluateCore (key : CtfeQueryBridge.QueryKey) (initial : Memo) (current : Current P E K) :
    Except (CtfeQueryBridge.Failure String) Answer × Memo := Id.run do
  let memo := initial.beginQuery
  let fail := fun (message : String) (memo : Memo) =>
    ((.error (.unsupported message),memo) : Except (CtfeQueryBridge.Failure String) Answer × Memo)
  unless current.target.pointerWidth.bits.toNat == 64 && current.target.endian == .little &&
      current.allocations.runs.any (fun row => row.1 == memo.run) &&
      !current.allocations.memory.sourceAllocIdWorldActive do
    return fail "selected memo current target/run/profile differs" memo
  if memo.blocked then return fail "selected memo run is blocked after a failing prefix" memo
  match validateCurrent memo current.types with
  | .error error => return fail error memo
  | .ok () => pure ()
  unless key.global == memo.registered.global && key.environment.paramEnv.callerBounds.isEmpty &&
      (key.environment.mode == .codegen || key.environment.mode == .postAnalysis) &&
      (key.family == .value || key.family == .allocation) do
    return fail "query is outside exact selected successful empty-ParamEnv domain" memo
  if let some answer := cached memo key then
    return (.ok answer,memo)
  let mut memo := memo
  if key.family == .value then
    -- Source eval_to_const_value_raw retries PostVALUE BEFORE demanding an
    -- allocation. A captured scalar hit needs no heap operation whatsoever.
    if (cached memo (queryKey memo.registered .value .postAnalysis)).isNone then
      return fail "selected VALUE miss requires source trivial_const/nontrivial evidence; an allocation memo alone does not choose the compiler VALUE dependency path" memo
  else
    if (cached memo (queryKey memo.registered .allocation .postAnalysis)).isNone then
      return fail "selected allocation miss requires genuine CTFE execution, not a scalar-to-root conversion" memo
  if key.environment.mode == .codegen then
    match memo.completeRetry key.family with
    | .error error => return fail error memo
    | .ok next => memo := next
  let some answer := cached memo key
    | return fail "selected provider dependency completed no requested result" memo
  return (.ok answer,memo)
/-- This cached slice has no allocator or type-construction capability. Its
result exposes the exact current context supplied by the caller. -/
def evaluate (key : CtfeQueryBridge.QueryKey) (memo : Memo) (current : Current P E K) : Attempt P E K :=
  let (outcome,next) := evaluateCore key memo current
  ⟨outcome,next,current⟩

theorem evaluate_current (key : CtfeQueryBridge.QueryKey) (memo : Memo) (current : Current P E K) :
    (evaluate key memo current).current = current := rfl
structure RegistryAttempt (P E K : Type) where
  outcome : Except (CtfeQueryBridge.Failure String) Answer
  registry : Registry
  current : Current P E K

def evaluateRegistry (key : CtfeQueryBridge.QueryKey) (registry : Registry) (current : Current P E K) : RegistryAttempt P E K := Id.run do
  let selected := registry.memos.zipIdx |>.filter (fun row => decide (row.1.registered.global = key.global))
  let some (memo,index) := selected[0]?
    | return ⟨.error (.unsupported "query has no selected initial memo table"),registry,current⟩
  unless selected.size == 1 do
    return ⟨.error (.unsupported "query has ambiguous selected initial memo tables"),registry,current⟩
  let result := evaluate key memo current
  match registry.commitMemo index result.memo with
  | .error error => return ⟨.error (.internal error),registry,current⟩
  | .ok registry => return ⟨result.outcome,registry,current⟩
end Miri.Input.CompilerInitialSelectedMemo
