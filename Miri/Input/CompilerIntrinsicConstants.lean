import Miri.Input.CompilerInstance
import Miri.Input.RuntimeArrayQueries
import Miri.Interpreter.ExecutionMachine

/-! Direct source `const_at/expect_const`, `to_value`, `to_branch` and
`to_leaf` queries for atomic and SIMD intrinsics. These inspect canonical
compiler constants; they do not normalize aliases or invent const evaluation.
Source compiler invariants are explicit invalid-program errors, while absent
imported metadata remains unsupported. -/
namespace Miri.Input.CompilerIntrinsicConstants
open Miri.Interpreter Miri.MIR Miri.Memory Miri.ABI
private def invalid (message : String) : StepError :=
  .invalidProgram s!"intrinsic generic constant: {message}"
private def value (world : RuntimeArrayTypes.World) (id : TypeConstId) :
    Except StepError ValTree := do
  let constant ← (world.arena.lookupConstant id).mapError StepError.unsupported
  match constant with
  | .Value _ tree => pure tree
  | _ => throw (invalid "source to_value requires ConstKind::Value")
private def node (tree : ValTree) : Except StepError ValTreeNode := do
  let some result := tree.nodes[tree.root]? | throw (invalid "invalid ValTree root")
  pure result
private def branch (tree : ValTree) : Except StepError (Array TypeConstId) := do
  match ← node tree with
  | .Branch fields => pure fields
  | _ => throw (invalid "source to_branch requires a branch")
private def leaf (tree : ValTree) : Except StepError ScalarInt := do
  let .Leaf bits bytes ← node tree | throw (invalid "source to_leaf requires a leaf")
  unless bytes > 0 && bytes ≤ 16 && bits < 2 ^ (bytes * 8) do
    throw (invalid "invalid compiler ScalarInt representation")
  match ScalarInt.tryFromUInt (BitVec.ofNat 128 bits) (Size.ofBytes (UInt64.ofNat bytes)) with
  | .ok (some scalar) => pure scalar
  | _ => throw (invalid "invalid compiler ScalarInt width")
private def argument (world : RuntimeArrayTypes.World) (callee : CallInstance)
    (index : Nat) : Except StepError ValTree := do
  let args ← CompilerInstance.argsOf world callee
    |>.mapError StepError.unsupported
  let some (.Const id) := args[index]?
    | throw (invalid "const_at/expect_const requires a constant argument")
  value world id
private def firstLeaf (world : RuntimeArrayTypes.World) (tree : ValTree) :
    Except StepError ScalarInt := do
  let fields ← branch tree
  let some first := fields[0]? | throw (invalid "enum ValTree has no discriminant")
  leaf (← value world first)
def ordering (world : RuntimeArrayTypes.World) (callee : CallInstance) (index : Nat) := do
  let scalar ← firstLeaf world (← argument world callee index)
  let result ← scalar.toAtomicOrdering.mapError (fun _ => invalid "invalid atomic ordering discriminant")
  pure (match result with
    | .relaxed => Miri.Concurrency.AtomicOrdering.Relaxed
    | .release => .Release
    | .acquire => .Acquire
    | .acqRel => .AcqRel
    | .seqCst => .SeqCst)
/-- Source atomic_load/store only calls to_value; the volatile value is ignored. -/
def volatile (world : RuntimeArrayTypes.World) (callee : CallInstance) (index : Nat) :
    Except StepError Unit := do
  let _ ← argument world callee index
  pure ()
def shuffle (world : RuntimeArrayTypes.World) (callee : CallInstance) (index : Nat) :
    Except StepError (Array UInt32) := do
  let fields ← branch (← argument world callee index)
  fields.mapM fun field => do
    let scalar ← leaf (← value world field)
    scalar.toUInt32.mapError (fun _ => invalid "shuffle index is not a u32 ScalarInt")
def alignment (world : RuntimeArrayTypes.World) (callee : CallInstance) (index : Nat) := do
  let scalar ← firstLeaf world (← argument world callee index)
  scalar.toSimdAlignment.mapError (fun _ => invalid "invalid SIMD alignment discriminant")
private def lift (result : Except StepError A) : MachineHooks.M K User A :=
  match result with
  | .ok value => pure value
  | .error error => throw error

def hooks (access : RuntimeArrayQueries.Access (MachineHooks.State K User))
    (base : ExecutionMachine.Config K User C Other Extern Host) :
    ExecutionMachine.Config K User C Other Extern Host :=
  {base with intrinsics := fun callee =>
    let context := base.intrinsics callee
    {context with
      atomicHooks := {context.atomicHooks with
        orderingConst := fun _ index => do lift (ordering (access.get (← get)) callee index)
        volatileConst := fun _ index => do lift (volatile (access.get (← get)) callee index)}
      simdHooks := {context.simdHooks with
        shuffleConst := fun _ index => do lift (shuffle (access.get (← get)) callee index)
        alignmentConst := fun _ index => do lift (alignment (access.get (← get)) callee index)}}}
end Miri.Input.CompilerIntrinsicConstants
