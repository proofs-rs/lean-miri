import empty_function.LocalInit
import empty_function.TerminatorStep
import empty_function.FrameExit
import empty_function.ReturnContinuation
namespace EmptyFunction.LocalModel
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false

def caller (s : Static) (p : Packet) (tracker : MachineHooks.BorrowState)
    (destination : InputDraft.LocalDestination s p tracker)
    (bound : destination.localId < destination.caller.locals.size) :=
  LocalImmediate.cached destination.caller destination.localId destination.slot s.abi.ret.layout bound

def initializedMachine (s : Static) (p : Packet) (tracker : MachineHooks.BorrowState)
    (destination : InputDraft.LocalDestination s p tracker) (older : Array LocalUnit.F)
    (bound : destination.localId < destination.caller.locals.size) (frame previous : LocalUnit.F) :=
  FrameRelevance.pushedMachine (older.push (caller s p tracker destination bound)) frame previous
    (s.cfg.lifecycle.freshLocalsIdentity p.before.machine).1

def machine (s : Static) (p : Packet) (tracker : MachineHooks.BorrowState)
    (destination : InputDraft.LocalDestination s p tracker) (older : Array LocalUnit.F)
    (bound : destination.localId < destination.caller.locals.size) (frame previous : LocalUnit.F) (index : Nat) :=
  let frames := older.push (caller s p tracker destination bound)
  FrameExit.afterRelevanceAt frames frame
    (TerminatorStep.after (LocalUnit.current frames frame
      (initializedMachine s p tracker destination older bound frame previous))).machine index

def finish (s : Static) (p : Packet) (tracker : MachineHooks.BorrowState)
    (destination : InputDraft.LocalDestination s p tracker) (older : Array LocalUnit.F)
    (bound : destination.localId < destination.caller.locals.size) (frame previous : LocalUnit.F) (index : Nat) : State :=
  ReturnContinuation.resume older (caller s p tracker destination bound)
    (machine s p tracker destination older bound frame previous index) p.returnBlock

end EmptyFunction.LocalModel
