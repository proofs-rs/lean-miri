import Miri.Input.CompilerProviders
import Miri.Interpreter.CompilerExecutionProviders
import Miri.Interpreter.ExecutionIntrinsic

/-! Direct compiler-only queries for ordinary intrinsics.rs. variant_count
peels exactly one Pat, handles ADT declarations without requiring mono, rejects
source generic/bound cases and returns zero for the source non-ADT kinds. -/
namespace Miri.Input.CompilerCoreIntrinsic
open Lean Miri.ABI Miri.Interpreter
/-- Pinned intrinsics.rs:249–291: peel one Pat, count raw ADT variants without
monomorphization or layout, reject aliases, and return zero for other World kinds.
The caller supplies the same execution universe that owns `ty`. -/
def variantCountInWorld (p : CompilerProviders.Prepared) (world : TypeArena.World)
    (ty : MIR.TyId) : Except StepError Nat := do
  let lookup := fun id => (world.lookupType id).mapError StepError.unsupported
  let view ← lookup ty
  let ty ← match view with
    | .material source => match source.shape with
      | .patternType base _ => pure base
      | _ => pure ty
    | .constructed (.patternType base _) => pure base
    | .constructed _ => pure ty
  let kind ← (world.shapeKind ty).mapError StepError.unsupported
  match kind with
  | .alias => throw (.invalidProgram "TooGeneric in variant_count")
  | .patternType => throw (.invalidProgram "source invariant: invalid nested pattern/bound type in variant_count")
  | .adt =>
    let (declaration,_) ← ((RuntimeMetadata.adtDeclarationInWorld p.runtime ty).run world).mapError StepError.unsupported
    pure declaration.variants.size
  | _ => pure 0

end Miri.Input.CompilerCoreIntrinsic
