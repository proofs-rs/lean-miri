import duplicate_prefix.GlobalRelocationTwoWords

/-! A source-derived name for the existing adjustFromTcx forIn body. This term
extracts the lambda from the pinned definition without changing its guards or
callback behavior. The enclosing conversion equation must still be kernel
proved; extraction alone is not a safety theorem. -/
namespace DuplicatePrefix.GlobalRelocationSourceExtraction
open Lean Lean.Meta

private partial def findLoop (value : Expr) : MetaM (Option Expr) := do
  if value.getAppFn.isConstOf ``ForIn.forIn then
    if let some action := value.getAppArgs.back? then
      if action.isLambda then return some action
  match value with
  | .letE _ _ assigned body _ => findLoop (body.instantiate1 assigned)
  | .lam name ty body info => withLocalDecl name info ty fun x => findLoop (body.instantiate1 x)
  | .app fn arg =>
    if let some action ← findLoop fn then return some action
    findLoop arg
  | .mdata _ body => findLoop body
  | _ => return none

private partial def findFinish (value : Expr) : MetaM (Option Expr) := do
  let arguments := value.getAppArgs
  if arguments.size ≥ 2 then
    let previous := arguments[arguments.size-2]!
    let last := arguments[arguments.size-1]!
    if previous.getAppFn.isConstOf ``ForIn.forIn && last.isLambda then return some last
  match value with
  | .letE _ _ assigned body _ => findFinish (body.instantiate1 assigned)
  | .lam name ty body info => withLocalDecl name info ty fun x => findFinish (body.instantiate1 x)
  | .app fn arg =>
    if let some action ← findFinish fn then return some action
    findFinish arg
  | .mdata _ body => findFinish body
  | _ => return none

elab "actual_relocation_step" : term => do
  let .defnInfo info ← getConstInfo ``Miri.Memory.Allocation.adjustFromTcx
    | throwError "expected pinned allocation conversion definition"
  lambdaTelescope info.value fun arguments body => do
    let some action ← findLoop body | throwError "expected pinned relocation loop"
    mkLambdaFVars arguments action

elab "actual_relocation_finish" : term => do
  let .defnInfo info ← getConstInfo ``Miri.Memory.Allocation.adjustFromTcx
    | throwError "expected pinned allocation conversion definition"
  lambdaTelescope info.value fun arguments body => do
    let some action ← findFinish body | throwError "expected pinned relocation continuation"
    mkLambdaFVars arguments action

end DuplicatePrefix.GlobalRelocationSourceExtraction

namespace DuplicatePrefix.GlobalRelocationActualStep
noncomputable def step := actual_relocation_step
noncomputable def finish := actual_relocation_finish
open Miri.ABI Miri.Memory Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

attribute [local irreducible] Array.extract Array.append

/-- Exact source equation: all pre-loop storage/fragment checks and the original
post-loop provenance construction remain part of the real conversion. -/
theorem adjust_eq_loop {Error State : Type}
    (source : Allocation CtfeProvenance Unit) (layout : TargetDataLayout)
    (pointer : Pointer CtfeProvenance → EStateM Error State (Pointer Provenance))
    (before : State) (noFragments : source.provenanceMap.byteFragments = none) :
    Allocation.adjustFromTcx source layout (fun _ _ state => .ok (AllocationCopy.snapshot source) state) pointer before =
      (forIn source.provenanceMap.ptrs (none,AllocationCopy.snapshot source,before,#[])
        (step source layout (fun _ _ state => .ok (AllocationCopy.snapshot source) state) pointer before)) >>=
        (finish source layout (fun _ _ state => .ok (AllocationCopy.snapshot source) state) pointer before) := by
  unfold DuplicatePrefix.GlobalRelocationActualStep.step DuplicatePrefix.GlobalRelocationActualStep.finish
  cases source
  rename_i raw size provenance mask align mutability extra native
  change provenance.byteFragments=none at noFragments
  simp only [Allocation.adjustFromTcx,AllocationCopy.snapshot,Allocation.inspectWithUninitAndPtrOutsideInterpreter,
    Allocation.len,Array.extract_size]
  simp [noFragments,pure,Pure.pure,Except.pure,Except.toOption,bind,Bind.bind,Id.run] <;> rfl
end DuplicatePrefix.GlobalRelocationActualStep
