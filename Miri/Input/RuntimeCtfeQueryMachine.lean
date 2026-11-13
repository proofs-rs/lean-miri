import Miri.Input.CompilerInitialCtfeQueryStore
import Miri.Input.CompilerInitialSelectedMemoProvider
import Miri.Input.CompilerInitialAllocationByteMachine
import Miri.Input.RuntimeArrayQueries
import Miri.Interpreter.ConstantMachine

/-! Runtime Unevaluated source binding. The memo is memory-free; every action
uses and commits the current machine memory, type universe and source counter.
There is no evaluated-constant-row fallback. The fixed engine's current
pre-runtime restriction remains an explicit Unsupported cold-runtime boundary. -/
namespace Miri.Input.RuntimeCtfeQueryMachine
open Miri.MIR Miri.Memory Miri.Interpreter CompilerInitialAllocation
set_option autoImplicit false
variable {User : Type}
structure Memo where
  private mk ::
  fresh : CompilerInitialCtfeQueryStore.Memo
  initial : CompilerInitialSelectedMemo.Registry

/-- Cached declarations and fresh source bodies are distinct capabilities.
An initial table with present entries cannot be overwritten by a contradictory
fresh-only source header. Empty tables may share a genuinely fresh body. -/
def Memo.create (fresh : CompilerInitialCtfeQueryStore.Memo)
    (initial : CompilerInitialSelectedMemo.Registry) : Except String Memo := do
  unless initial.run == fresh.run do throw "initial/fresh query capabilities belong to different runs"
  for memo in initial.memos do
    let matching := fresh.roots.filter (fun source => source.query.global == memo.registered.global)
    for source in matching do
      unless CompilerInitialSelectedMemo.memoSize memo == 0 && source.callee == memo.registered.callee &&
          source.body.body.locals[0]? == some memo.registered.type do
        throw "fresh source capability contradicts initial selected compiler memo"
  -- Retain every table, including empty tables. Fresh-owned keys route to the
  -- independently admitted body and its run-owned dynamic memo; no row is lost.
  pure ⟨fresh,initial⟩

structure MemoAccess (User : Type) where
  getMemo : User → Option Memo
  setMemo : Memo → User → User
  get_set : ∀ memo user, getMemo (setMemo memo user) = some memo

inductive Capability where
  | unavailable
  /-- Consume only exact frozen initial answers; cold queries are Unsupported. -/
  | cachedOnly
  | selected (execute : CompilerInitialCtfeRootResult.Engine)

private def shape (types : RuntimeArrayTypes.World) (ty : TyId) : Except String Unit := do
  let value ← match ← types.arena.lookupType ty with
    | .constructed key => pure (some key)
    | .material source => types.arena.materialKey source
  unless value == some (.integer false .u32) do
    throw "runtime selected CTFE operand supports actual World u32 only"

private def access (execute : CompilerInitialCtfeRootResult.Engine) :
    CtfeQueryBridge.Access CompilerInitialCtfeQueryStore.State String CompilerInitialCtfeQueryStore.Answer where
  validate := fun operand state =>
    let result : Except String Unit := do
      unless operand.source.arguments.isEmpty && operand.source.promoted.isNone do
        throw "runtime selected CTFE operand requires empty arguments and no promoted body"
      shape state.types operand.declaredType
    (result.mapError CtfeQueryBridge.Failure.unsupported,state)
  resolve := fun (environment : CompilerTypingEnv.Env) (raw : UnevaluatedConst)
      (state : CompilerInitialCtfeQueryStore.State) =>
    let result : Except String (Option InstanceArena.Key) := do
      unless environment.paramEnv.callerBounds.isEmpty &&
          (environment.mode == CompilerTypingEnv.Mode.codegen || environment.mode == CompilerTypingEnv.Mode.postAnalysis) do
        throw "runtime selected CTFE resolution requires empty ParamEnv in Codegen/PostAnalysis"
      unless raw.arguments.isEmpty && raw.promoted.isNone do
        throw "runtime selected CTFE resolution needs unavailable generic/promoted resolution"
      let physical ← state.types.arena.identity raw.definition
      let candidates := state.roots.filter (fun source => source.query.global.callee.definition == physical)
      let [source] := candidates.toList | throw "runtime Unevaluated has no unique admitted physical Const source"
      let actual ← match ← state.types.instances.lookup source.callee with
        | .material key | .constructed key => pure key
      unless actual == source.query.global.callee && actual.arguments.isEmpty do
        throw "runtime Unevaluated selected instance does not belong to current World"
      -- Return the actual admitted Const instance, never fabricate an Item for
      -- an unresolved trait/default or reconstruct a key from allocation bytes.
      pure (some actual)
    (result.mapError CtfeQueryBridge.Failure.unsupported,state)
  queryInput := fun (proposed : CtfeQueryBridge.ResolvedInput)
      (state : CompilerInitialCtfeQueryStore.State) =>
    let result : Except String CtfeQueryBridge.QueryKey := do
      unless proposed.environment.paramEnv.callerBounds.isEmpty &&
          (proposed.environment.mode == CompilerTypingEnv.Mode.codegen || proposed.environment.mode == CompilerTypingEnv.Mode.postAnalysis) &&
          proposed.global.callee.arguments.isEmpty && proposed.global.promoted.isNone do
        throw "runtime CTFE query-input normalization/region erasure outside empty guarded scope"
      -- Empty args/ParamEnv have no aliases, regions or inference variables:
      -- with_post_analysis_normalized_invalidating_rigid_aliases and region
      -- erasure preserve this exact key. Other domains are not approximated.
      pure (CtfeQueryBridge.QueryKey.mk proposed.family proposed.environment proposed.global)
    (result.mapError CtfeQueryBridge.Failure.unsupported,state)
  evaluate := CompilerInitialCtfeQueryStore.evaluateWith execute

private def failure (usage : SpanRef) : CtfeQueryBridge.Failure String → StepError
  | .unsupported reason => .unsupported s!"runtime CTFE operand at span {usage.id}: {reason}"
  | .internal reason => .invalidProgram s!"runtime CTFE operand at span {usage.id}: {reason}"
  | .tooGeneric span => .unsupported s!"runtime CTFE TooGeneric; source usage={usage.id}; query span={reprStr span}"
  | .reported diagnostic span => .unsupported s!"runtime CTFE diagnostic unavailable: {diagnostic}; usage={usage.id}; query span={reprStr span}"

def evaluate (capability : Capability) (compiler : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (types : RuntimeArrayQueries.Access (MachineHooks.State MiriMemoryKind User))
    (storeAccess : CompilerInitialAllocation.ByteMachine.Access User) (memoAccess : MemoAccess User)
    (environment : CompilerTypingEnv.Env) (operand : ConstOperand) :
    MachineHooks.M MiriMemoryKind User (TyId × ConstValue) := do
  let .Unevaluated raw declared := operand.value
    | throw (.invalidProgram "runtime CTFE source hook received an evaluated/Ty operand")
  let execute := match capability with
    | .unavailable => none
    | .cachedOnly => none
    | .selected engine => some engine
  if let .unavailable := capability then
    throw (.unsupported "runtime Unevaluated requires an installed typed query provider")
  let original ← get
  let some store := storeAccess.getStore original.machine.user
    | throw (.unsupported "runtime Unevaluated has no complete initial typed allocation store")
  let some memo := memoAccess.getMemo original.machine.user
    | throw (.unsupported "runtime Unevaluated has no run-owned typed query memo")
  unless original.machine.memory.activeInitialCompilerRun == some memo.fresh.run &&
      memo.initial.run == memo.fresh.run && !original.machine.memory.sourceAllocIdWorldActive do
    throw (.unsupported "runtime Unevaluated memo is not attached to the active central source-counter run")
  unless raw.arguments.isEmpty && raw.promoted.isNone && environment.paramEnv.callerBounds.isEmpty &&
      (environment.mode == CompilerTypingEnv.Mode.codegen || environment.mode == CompilerTypingEnv.Mode.postAnalysis) do
    throw (.unsupported "runtime Unevaluated is outside empty-argument/unpromoted empty-ParamEnv domain")
  match shape (types.get original) declared with
  | .error error => throw (.unsupported error)
  | .ok () => pure ()
  let physical ← match (types.get original).arena.identity raw.definition with
    | .ok physical => pure physical
    | .error error => throw (.unsupported error)
  let freshOwned := memo.fresh.roots.any (fun source => source.query.global.callee.definition == physical)
  let indices := if freshOwned then [] else (List.range memo.initial.memos.size).filter (fun index =>
    (memo.initial.memos[index]?).any (fun selected => selected.registered.definition == physical))
  let allocationWorld := store.withMemory original.machine.memory
  let (outcome,updatedMemo,updatedTypes,updatedAllocations) ← match indices with
    | [index] => do
      let some selected := memo.initial.memos[index]?
        | throw (.invalidProgram "selected compiler memo disappeared")
      let key : CtfeQueryBridge.QueryKey := ⟨.value,environment,selected.registered.global⟩
      let current : CompilerInitialSelectedMemo.Current Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind :=
        ⟨compiler.runtime.target.base,types.get original,allocationWorld⟩
      let attempt := CompilerInitialSelectedMemo.evaluateRegistry key memo.initial current
      let result := attempt.outcome.map fun answer => match answer with
        | .value type value => Sum.inl (type,value)
        | .allocation type root => Sum.inr (type,root)
      pure (result,{memo with initial := attempt.registry},attempt.current.types,attempt.current.allocations)
    | [] => do
      let some execute := execute
        | throw (.unsupported "runtime Unevaluated has no exact initial memo; cold evaluation is unavailable")
      let attached ← match memo.fresh.attach compiler image (types.get original) allocationWorld with
        | .ok attached => pure attached
        | .error error => throw (.unsupported error)
      let (result,successor) := CtfeQueryBridge.evaluate (access execute) environment
        ⟨raw,declared,some operand.span⟩ attached
      let result := result.map fun answer => match answer with
        | .value type value => Sum.inl (type,value)
        | .allocation type root => Sum.inr (type,root)
      pure (result,{memo with fresh := successor.memo},successor.types,successor.allocations)
    | _ => throw (.invalidProgram "runtime Unevaluated has ambiguous initial query tables")
  -- Commit on both success and failure. Never restore original memory/arena or
  -- silently reset the memo after a consumed allocation or interned root.
  let user := memoAccess.setMemo updatedMemo
    (storeAccess.setStore updatedAllocations.store original.machine.user)
  let committed := {original with machine := {original.machine with memory := updatedAllocations.memory,user := user}}
  set (types.set committed updatedTypes)
  match outcome with
  | .error error => throw (failure operand.span error)
  | .ok (.inr _) => throw (.invalidProgram "runtime MIR value query returned an allocation-family answer")
  | .ok (.inl (resultType,value)) =>
    unless resultType == declared do
      throw (.invalidProgram "runtime CTFE result type differs from source operand type")
    pure (resultType,.Scalar (.Int value.toNat 4))

end Miri.Input.RuntimeCtfeQueryMachine
