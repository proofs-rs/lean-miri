import Miri.Interpreter.Constant
import Miri.Interpreter.FunctionPointers

/-! Canonical constant-operand machine binding. Compiler CTFE pointer IDs
remain allocation IDs until actual root-tag/address adjustment; they are never
used directly as absolute guest addresses. -/
namespace Miri.Interpreter.ConstantMachine
open Miri.ABI Miri.Memory Miri.MIR
open Miri.TreeBorrows (BorrowTree)
structure Context (K User : Type) where
  state : MachineHooks.State K User
  pendingError : Option StepError

private def machineAction (action : MachineHooks.M K User A) :
    ConstantM Provenance BorrowTree K (Context K User) A := fun constant =>
  let initial := {constant.hooks.state with machine := {constant.hooks.state.machine with memory := constant.memory}}
  match action initial with
  | .ok value result => .ok value {constant with memory := result.machine.memory, hooks := ⟨result,constant.hooks.pendingError⟩}
  | .error error result => .error (.query "constant machine operation failed")
      {constant with memory := result.machine.memory, hooks := ⟨result,some error⟩}

/-- Source M::adjust_alloc_root_pointer with the original CTFE offset. -/
private def adjustedPointer (functions : FunctionPointers.Hooks K User Other)
    (arithmetic : PointerArithmetic) (pointer : Pointer CtfeProvenance) :
    ConstantM Provenance BorrowTree K (Context K User) (Pointer Provenance) := machineAction do
  let root ← FunctionPointers.rootPointer functions pointer.provenance.allocId
  match root.wrappingOffset pointer.offset arithmetic with
  | .ok pointer => pure pointer
  | .error error => throw (.invalidProgram s!"constant root pointer offset: {reprStr error}")

/-- Conversion retains machine effects preceding failure because pointer
materialization can allocate runtime provenance before a later check fails. -/
def evalValueWithLayout (runtime : Input.RuntimeMetadata)
    (functions : FunctionPointers.Hooks K User Other) (arithmetic : PointerArithmetic)
    (externStatic : DefId → MachineHooks.M K User (Pointer Provenance))
    (classifyConstantError : ConstantError → StepError)
    (value : ConstValue) (ty : TyId) (known : Option LocalLayout)
    (checkKnown : Option (LocalLayout → LocalLayout → MachineHooks.M K User Bool)) :
    MachineHooks.M K User (OpTy Provenance) := fun initial =>
  let compiler : ConstantValueQueries Provenance BorrowTree K (Context K User) :=
    ⟨adjustedPointer functions arithmetic, fun definition => machineAction (externStatic definition)⟩
  let source : ConstantState Provenance BorrowTree K (Context K User) :=
    ⟨initial.machine.memory,⟨initial,none⟩⟩
  match valueToOpWithLayout runtime compiler value ty known
      (checkKnown.map fun check left right => machineAction (check left right)) source with
  | .ok value result => .ok value {result.hooks.state with machine :=
      {result.hooks.state.machine with memory := result.memory}}
  | .error error result => .error (result.hooks.pendingError.getD (classifyConstantError error))
      {result.hooks.state with machine := {result.hooks.state.machine with memory := result.memory}}
/-- Resolved MIR operands carry the compiler's final value and type. -/
def evalOperandWithLayout (runtime : Input.RuntimeMetadata)
    (functions : FunctionPointers.Hooks K User Other) (arithmetic : PointerArithmetic)
    (externStatic : DefId → MachineHooks.M K User (Pointer Provenance))
    (classifyConstantError : ConstantError → StepError)
    (constant : ConstOperand) (known : Option LocalLayout)
    (checkKnown : Option (LocalLayout → LocalLayout → MachineHooks.M K User Bool)) :
    MachineHooks.M K User (OpTy Provenance) := do
  match constant.value with
  | .Val value ty =>
    evalValueWithLayout runtime functions arithmetic externStatic classifyConstantError value ty known checkKnown

end Miri.Interpreter.ConstantMachine
