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

def scalar (p : CompilerProviders.Prepared) (types : RuntimeArrayQueries.Access S) : ExecutionScalar.Leaves S C :=
  let context := p.lifecycle.calls.symbols.facts.context
  { classify := fun _ ty => CompilerExecutionProviders.worldClass types context ty
    boolLayout := fun _ => CompilerExecutionProviders.worldBool types context
    orderingLayout := fun _ => lift context.orderingLayout
    overflowLayout := fun _ element => RuntimeArrayQueries.perform types do
      let boolean ← TypeArena.World.internType .bool
      let tuple ← TypeArena.World.internType (.tuple #[element.ty,boolean])
      RuntimeMetadata.layoutInWorld context.runtime tuple
    metadataLayout := fun _ ty => RuntimeArrayQueries.perform types do
      let pointee ← CompilerFacts.requiredTypeInWorld context ty "builtin_deref_explicit"
      let metadata ← CompilerFacts.requiredTypeInWorld context pointee "pointer_metadata_type"
      RuntimeMetadata.layoutInWorld context.runtime metadata
    unitLayout := fun _ => RuntimeArrayQueries.perform types (CompilerFacts.unitLayoutInWorld context) }

def discriminant (p : CompilerProviders.Prepared) (types : RuntimeArrayQueries.Access S)
    (scalarMayBeNull : C → Scalar Provenance → RvalueM S Bool) :
    ExecutionLeaves.Discriminant S C :=
  let context := p.lifecycle.calls.symbols.facts.context
  { discriminantLayout := fun _ ty => RuntimeArrayQueries.perform types (CompilerDiscriminantFacts.discriminantLayout context ty)
    tagLayout := fun _ tag => RuntimeArrayQueries.perform types (CompilerDiscriminantFacts.tagLayout context tag)
    discriminantValue := fun _ ty index => RuntimeArrayQueries.perform types (CompilerDiscriminantFacts.discriminantValue context ty index)
    variantForDiscriminant := fun _ ty bits => RuntimeArrayQueries.perform types (CompilerDiscriminantFacts.variantForDiscriminant context ty bits)
    adtVariantCount := fun _ ty => RuntimeArrayQueries.perform types (CompilerDiscriminantFacts.adtVariantCount context ty)
    scalarMayBeNull := scalarMayBeNull }
end Miri.Input.CompilerScalarLeaves
