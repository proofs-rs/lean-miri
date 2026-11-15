import Miri.Input.SourceCompilerDiscriminants
import Miri.Input.CompilerProviders
import Miri.Input.CompilerDiscriminantFacts
import Miri.Interpreter.CompilerExecutionProviders
import Miri.Interpreter.ExecutionScalar
import Miri.Interpreter.ExecutionLeaves

/-! Direct scalar/discriminant compiler providers. Canonical query identities
select result types; physical null/provenance checks remain actual operations.
-/
namespace Miri.Input.CompilerScalarLeaves
open Miri.ABI Miri.Interpreter Miri.Memory
private def lift (value : Except String A) : EStateM StepError S A :=
  match value with | .ok value => pure value | .error e => throw (.unsupported e)
private def physical (value : Except StepError A) : EStateM StepError S A :=
  match value with | .ok value => pure value | .error e => throw e

def boolLayout (p : CompilerProviders.Prepared) (_ : C) : EStateM StepError S LocalLayout :=
  lift (p.primitiveLayout "bool")

def runtimeChecks (p : CompilerProviders.Prepared) (_ : C) (kind : MIR.RuntimeChecks) :
    EStateM StepError S Bool :=
  lift (CompilerIntrinsicFacts.runtimeChecks p.intrinsics kind)

def scalar (p : CompilerProviders.Prepared) : ExecutionScalar.Leaves S C :=
  let context := p.lifecycle.calls.symbols.facts.context
  { classify := fun _ ty => physical (CompilerExecutionProviders.scalarClass context ty)
    boolLayout := fun _ => lift (context.primitiveLayout "bool")
    orderingLayout := fun _ => lift context.orderingLayout
    overflowLayout := fun _ element => lift (context.runtime.overflowTupleLayout element |>.mapError toString)
    metadataLayout := fun _ ty => physical (CompilerExecutionProviders.metadataLayout context ty)
    unitLayout := fun _ => lift (CompilerFacts.unitLayout context) }

def discriminant (p : CompilerProviders.Prepared) (world : SourceCompilerWorld.Access S)
    (scalarMayBeNull : C → Scalar Provenance → RvalueM S Bool) :
    ExecutionLeaves.Discriminant S C :=
  let context := p.lifecycle.calls.symbols.facts.context
  let sourceMode := p.program.input.sourceMaterial.isSome
  let current := SourceCompilerRuntime.current p.runtime.target world
  { discriminantLayout := fun _ ty => if sourceMode then do
      let runtime ← current
      lift (SourceCompilerDiscriminants.layout runtime ty)
    else lift (CompilerDiscriminantFacts.discriminantLayout context ty)
    tagLayout := fun _ tag => if sourceMode then do
      let runtime ← current
      lift (CompilerDiscriminantFacts.tagLayout {context with runtime} tag)
    else lift (CompilerDiscriminantFacts.tagLayout context tag)
    discriminantValue := fun _ ty index => if sourceMode then do
      let runtime ← current
      lift (SourceCompilerDiscriminants.value runtime ty index)
    else lift (CompilerDiscriminantFacts.discriminantValue context ty index)
    variantForDiscriminant := fun _ ty bits => if sourceMode then do
      let runtime ← current
      lift (SourceCompilerDiscriminants.variantForDiscriminant runtime ty bits)
    else lift (CompilerDiscriminantFacts.variantForDiscriminant context ty bits)
    adtVariantCount := fun _ ty => if sourceMode then do
      let runtime ← current
      lift (SourceCompilerDiscriminants.variantCount runtime ty)
    else lift (CompilerDiscriminantFacts.adtVariantCount context ty)
    scalarMayBeNull := scalarMayBeNull }
end Miri.Input.CompilerScalarLeaves
