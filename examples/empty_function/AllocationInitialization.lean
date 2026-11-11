import Miri.Interpreter.PlaceMachine

open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
/-! Compatibility equation for the fixed diagnostic-off proof configuration.
The source initialization order and every success/failure state are preserved. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.constructorNameAsVariable false

namespace EmptyFunction.AllocationInitialization
variable {K U A : Type}

def oldInitialize (config : PlaceMachine.AllocationConfig K U)
    (id : AllocId) (size : Size) (align : Align) : MachineHooks.M K U BorrowTree := fun state =>
  let action : PlaceMachine.MachineM K U BorrowTree := do
    config.diagnostic id size align
    PlaceMachine.initStackExtra config.allocationTail id size align
  match action state.machine with
  | .ok tree machine => .ok tree {state with machine}
  | .error error machine => .error error {state with machine}

def liftMachine (action : PlaceMachine.MachineM K U A) : MachineHooks.M K U A := fun state =>
  match action state.machine with
  | .ok value machine => .ok value {state with machine}
  | .error error machine => .error error {state with machine}

def explicitInitialize (config : PlaceMachine.AllocationConfig K U)
    (id : AllocId) (kind : MemoryKind K) (size : Size) (align : Align) : MachineHooks.M K U BorrowTree := do
  liftMachine (config.diagnostic id size align)
  let tree ← liftMachine (PlaceMachine.initStackExtra config.allocationTail id size align)
  try
    if let some capture := config.allocationBacktrace then capture id kind
    liftMachine (config.allocationSpan id size align)
    return tree
  catch error =>
    liftMachine (config.discardUninserted id)
    throw error

theorem initialize_none (config : PlaceMachine.AllocationConfig K U)
    (id : AllocId) (kind : MemoryKind K) (size : Size) (align : Align)
    (noCapture : config.allocationBacktrace = none)
    (noSpan : config.allocationSpan = fun _ _ _ => pure ()) :
    PlaceMachine.initializeAllocation config id kind size align = oldInitialize config id size align := by
  funext state
  change explicitInitialize config id kind size align state = _
  unfold explicitInitialize oldInitialize
  simp only [noCapture,noSpan]
  cases diag : config.diagnostic id size align state.machine with
  | error error machine =>
    simp [liftMachine,diag,bind,Bind.bind,EStateM.bind]
  | ok unit machine =>
    cases unit
    cases root : PlaceMachine.initStackExtra config.allocationTail id size align machine with
    | error error machine => simp [liftMachine,diag,root,bind,Bind.bind,EStateM.bind,
        tryCatch,tryCatchThe,MonadExceptOf.tryCatch,EStateM.tryCatch,
        pure,Pure.pure,EStateM.pure,EarlyReturnT.return,EarlyReturn.runK,
        throw,throwThe,MonadExceptOf.throw,EStateM.throw,ExceptT.run,ExceptT.mk,ExceptT.bind,ExceptT.bindCont,ExceptT.pure,
        EStateM.nonBacktrackable,EStateM.dummySave,EStateM.dummyRestore]
    | ok tree machine => simp [liftMachine,diag,root,bind,Bind.bind,EStateM.bind,
        tryCatch,tryCatchThe,MonadExceptOf.tryCatch,EStateM.tryCatch,
        pure,Pure.pure,EStateM.pure,EarlyReturnT.return,EarlyReturn.runK,
        throw,throwThe,MonadExceptOf.throw,EStateM.throw,ExceptT.run,ExceptT.mk,ExceptT.bind,ExceptT.bindCont,ExceptT.pure,
        EStateM.nonBacktrackable,EStateM.dummySave,EStateM.dummyRestore]
end EmptyFunction.AllocationInitialization
