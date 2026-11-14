import Miri.Input.MirTemplate

/-! Raw ordinary direct-call material. This is a component for the next body
category, not enabled by the production BodySeed selector yet. In particular,
constructing MIR does not establish instance resolution, ABI or transfer facts.
Those providers must consume the same source callee identity before integration.

Pinned instance.rs substitutes the complete MIR tree, including FnDef generic
arguments. For this binder-free category the region eraser then preserves bound
regions and erases other regions; closedness excludes residual bound variables.
Trait methods, virtual calls, function pointers and shims are outside this type. -/
namespace Miri.Input.MirDirectCall
open Miri.MIR GenericSubstitution

structure Callee where
  definition : DefinitionIdentity
  arguments : Array Term
  deriving Repr, DecidableEq

structure Argument where
  span : SpanRef
  operand : MirTemplate.Operand
  deriving Repr, DecidableEq

structure Template where
  callee : Callee
  constantSpan : SpanRef
  source : SourceInfo
  arguments : Array Argument
  destination : LocalId
  target : Option BasicBlockId
  unwind : UnwindAction
  callSource : CallSource
  functionSpan : SpanRef
  deriving Repr, DecidableEq

/-- Early substitution and the restricted pinned region eraser are separate
operations. No trait or alias normalization is inferred from representations. -/
def instantiateCallee (fuel : Nat) (arguments : Array Term) (source : Callee) :
    Except String Callee := do
  let instantiated ← source.arguments.mapM fun value => do
    let value ← GenericSubstitution.instantiate fuel arguments value
    let value ← MirTemplate.eraseFreeRegions fuel value
    MirTemplate.validateClosed fuel value
    pure value
  pure {source with arguments := instantiated}

/-- A direct FnDef constant is zero-sized; its exact type must be resolved by
the caller. A type/layout-compatible substitute is never sufficient. -/
def instantiate (fuel : Nat) (arguments : Array Term) (source : Template)
    (resolveFunctionType : Callee → Except String TyId) : Except String Terminator := do
  let callee ← instantiateCallee fuel arguments source.callee
  let functionType ← resolveFunctionType callee
  let function := Operand.Constant {
    span := source.constantSpan, userType := none,
    value := .Val .ZeroSized functionType }
  let operands := source.arguments.map fun argument =>
    ({span := argument.span, operand := argument.operand.instantiate} : SpannedOperand)
  pure ⟨source.source, .Call function operands ⟨source.destination,#[]⟩ source.target
    source.unwind source.callSource source.functionSpan⟩

end Miri.Input.MirDirectCall
