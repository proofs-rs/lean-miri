import Lean

/-! Ordered CTFE frame-entry control, matching pinned interpret/stack.rs
push_stack_frame_raw. The caller must already have pushed a pending frame with
dead locals and the definition span. Its required-constant callback performs
actual frame substitution, normalization and evaluation in the current World.
Only the final callback may finish arguments/locals and enter bb0[0].

No callback implementation or query-admission capability is supplied here.
World effects commit on failure; a repeated required-constant occurrence is
still requested, even if the query provider can reuse an execution-local memo. -/
namespace Miri.Interpreter.CompileTime.FrameEntry

inductive FailureStage where
  | requiredConstant (index : Nat)
  | initialization
  deriving Repr, DecidableEq

/-- Errors are values so compiler state changes survive an unsuccessful entry. -/
abbrev Action (World Error Value : Type) := World → Except Error Value × World

inductive Result (World Pending Ready Error : Type) where
  | ready (frame : Ready) (world : World) (requiredCount : Nat)
  | failed (error : Error) (stage : FailureStage) (pending : Pending)
      (world : World) (completedRequired : Nat)
  deriving Repr

private def runRequired (required : List Source)
    (evaluate : Pending → Source → Action World Error Unit)
    (finish : Pending → Action World Error Ready)
    (pending : Pending) (world : World) (checked : Nat) : Result World Pending Ready Error :=
  match required with
  | [] =>
    let (result,world) := finish pending world
    match result with
    | .ok frame => .ready frame world checked
    | .error error => .failed error .initialization pending world checked
  | source::rest =>
    let (result,world) := evaluate pending source world
    match result with
    | .error error => .failed error (.requiredConstant checked) pending world checked
    | .ok () => runRequired rest evaluate finish pending world (checked+1)

/-- Preserve source order and duplicates; stop at the first error. Ordinary-call
ABI checks precede this operation. Query-root setup must bypass function ABI
handling separately, as in eval_queries.rs; this function does not provide it. -/
def enter (required : Array Source)
    (evaluate : Pending → Source → Action World Error Unit)
    (finish : Pending → Action World Error Ready)
    (pending : Pending) (world : World) : Result World Pending Ready Error :=
  runRequired required.toList evaluate finish pending world 0

end Miri.Interpreter.CompileTime.FrameEntry
