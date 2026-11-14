import Miri.Input.CompilerProviders
import Miri.Interpreter.GlobalMemoryCopyMachine

/-! Direct source place.rs copy_op_no_validate padding decision and physical
copy dictionary. Type compatibility remains the real rustc covariance query;
no source-copy or source-validation result callback is accepted. -/
namespace Miri.Input.CompilerCopy
open Miri.ABI Miri.Memory Miri.Interpreter

private def physical (value : Except StepError A) : EStateM StepError S A :=
  match value with | .ok result => pure result | .error error => throw error

def hasPadding (runtime : RuntimeMetadata) (types : RuntimeArrayQueries.Access S)
    (debug : Bool) (layout : LocalLayout) : EStateM StepError S Bool := do
  match layout.layout.backendRepr with
  | .Scalar _ => pure false
  | .ScalarPair (a := a) (b := b) =>
    let arena ← RuntimeArrayQueries.snapshot types
    let kind ← physical ((arena.shapeKind layout.ty).mapError StepError.unsupported)
    let wide := kind == .reference || kind == .rawPointer
    if wide && !debug then return false
    let sizeA ← physical (a.size runtime.target |>.mapError (fun e => StepError.invalidProgram (reprStr e)))
    let sizeB ← physical (b.size runtime.target |>.mapError (fun e => StepError.invalidProgram (reprStr e)))
    let total ← physical (sizeA.add sizeB |>.mapError (fun e => StepError.invalidProgram (reprStr e)))
    if wide then
      unless total == layout.layout.size do throw (.invalidProgram "wide pointer scalar sizes disagree with layout")
      pure false
    else pure (total != layout.layout.size)
  | .SimdVector .. | .SimdScalableVector .. | .Memory .. => pure true

def hooks [DecidableEq K] (runtime : RuntimeMetadata)
    (types : RuntimeArrayQueries.Access (ValidityMachine.State K U)) (debug : Bool)
    (compatible : LocalLayout → LocalLayout → Except StepError Bool)
    (access : ValidityMachine.Access K U)
    (addresses : ValidityMachine.UserState U → AllocAddresses.GlobalAddressState)
    (arithmetic : PointerArithmetic)
    (visitor : ValidityVisitor.Hooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra F A Pad)
    (validationBudget : Nat) :
    PlaceCopyHooks Provenance (ValidityMachine.State K U) C where
  compatible := compatible
  hasPadding := hasPadding runtime types debug
  readRaw := fun _ => PlaceMachine.readRaw access
  memoryCopy := GlobalMemoryCopyMachine.typedCopy access addresses arithmetic visitor.projection.dynamic
    visitor.projection.dynamicFuel debug
  validateSource := fun c source destination => do
    if !source.layout.isSized || !destination.layout.layout.isSized || source.layout.size != destination.layout.layout.size then
      throw (.invalidProgram "source validation transmute requires equally sized layouts")
    let sourcePlace ← PlaceDynamic.offsetWithMeta visitor.projection c destination .ZERO .wrapping .none source
    ValidityMachine.validateRuntime visitor c validationBudget sourcePlace true
end Miri.Input.CompilerCopy
