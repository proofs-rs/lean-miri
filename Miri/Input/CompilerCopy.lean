import Miri.Input.CompilerProviders
import Miri.Input.SourceCompilerRuntime
import Miri.Interpreter.GlobalMemoryCopyMachine

/-! Direct source place.rs copy_op_no_validate padding decision and physical
copy dictionary. Type compatibility remains the real rustc covariance query;
no source-copy or source-validation result callback is accepted. -/
namespace Miri.Input.CompilerCopy
open Miri.ABI Miri.Memory Miri.Interpreter

def hasPadding (runtime : RuntimeMetadata) (debug : Bool) (layout : LocalLayout) :
    Except StepError Bool := do
  match layout.layout.backendRepr with
  | .Scalar _ => pure false
  | .ScalarPair (a := a) (b := b) =>
    let node ← (runtime.node layout.ty).mapError (fun e => StepError.unsupported (toString e))
    let wide := node.shapeKind == .reference || node.shapeKind == .rawPointer
    if wide && !debug then return false
    let sizeA ← a.size runtime.target |>.mapError (fun e => StepError.invalidProgram (reprStr e))
    let sizeB ← b.size runtime.target |>.mapError (fun e => StepError.invalidProgram (reprStr e))
    let total ← sizeA.add sizeB |>.mapError (fun e => StepError.invalidProgram (reprStr e))
    if wide then
      unless total == layout.layout.size do throw (.invalidProgram "wide pointer scalar sizes disagree with layout")
      pure false
    else pure (total != layout.layout.size)
  | .SimdVector .. | .SimdScalableVector .. | .Memory .. => pure true

/-- Only the scalar-pair branch inspects type shape. Read its canonical identity
from the current World; geometry and the pinned padding rule stay unchanged. -/
def hasPaddingCurrent (runtime : RuntimeMetadata) (world : SourceCompilerWorld.Access S)
    (debug : Bool) (layout : LocalLayout) : EStateM StepError S Bool := do
  let runtime ← match layout.layout.backendRepr with
    | .ScalarPair .. =>
      if runtime.source.sourceMaterial.isSome then
        SourceCompilerRuntime.current runtime.target world
      else pure runtime
    | _ => pure runtime
  match hasPadding runtime debug layout with
  | .ok value => pure value
  | .error error => throw error

def hooks [DecidableEq K] (runtime : RuntimeMetadata) (world : SourceCompilerWorld.Access (ValidityMachine.State K U))
    (debug : Bool)
    (compatible : LocalLayout → LocalLayout → Except StepError Bool)
    (access : ValidityMachine.Access K U)
    (addresses : ValidityMachine.UserState U → AllocAddresses.GlobalAddressState)
    (arithmetic : PointerArithmetic)
    (visitor : ValidityVisitor.Hooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra F A Pad)
    (validationBudget : Nat) :
    PlaceCopyHooks Provenance (ValidityMachine.State K U) C where
  compatible := compatible
  hasPadding := hasPaddingCurrent runtime world debug
  readRaw := fun _ => PlaceMachine.readRaw access
  memoryCopy := GlobalMemoryCopyMachine.typedCopy access addresses arithmetic visitor.projection.dynamic
    visitor.projection.dynamicFuel debug
  validateSource := fun c source destination => do
    if !source.layout.isSized || !destination.layout.layout.isSized || source.layout.size != destination.layout.layout.size then
      throw (.invalidProgram "source validation transmute requires equally sized layouts")
    let sourcePlace ← PlaceDynamic.offsetWithMeta visitor.projection c destination .ZERO .wrapping .none source
    ValidityMachine.validateRuntime visitor c validationBudget sourcePlace true
end Miri.Input.CompilerCopy
