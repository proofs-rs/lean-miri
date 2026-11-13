import Miri.Input.CompilerCallPipeline

/-! Complete compiler dictionary for source virtual/drop/caller-location
drivers. All identities refer to the pipeline's final shared tables. -/
namespace Miri.Input.CompilerVirtualLeaves
open Miri.Interpreter
private def lift (value : Except String A) : EStateM StepError S A :=
  match value with
  | .ok value => pure value
  | .error reason => throw (.unsupported s!"compiler virtual query: {reason}")

def make (p : CompilerCallPipeline.Prepared) (types : RuntimeArrayQueries.Access S) : VirtualCalls.CompilerHooks S C :=
  let facts := p.symbols.facts
  WorldVirtualHooks.hooks types <| CompilerVirtualFacts.scopeHooks p.scopes types {
    instanceArgs := fun inst => do lift (CompilerInstance.argsOf (← RuntimeArrayQueries.compilerSnapshot types) inst)
    classifyReceiver := fun ty => RuntimeArrayQueries.perform types (CompilerVirtualFacts.receiverKindInWorld facts.context ty)
    fieldLayout := fun layout index => RuntimeArrayQueries.perform types (RuntimeMetadata.fieldLayoutForInWorld facts.context.runtime layout index)
    structTailForCodegen := fun ty => RuntimeArrayQueries.perform types (RuntimeMetadata.metadataTailInWorld facts.context.runtime ty)
    dynamicData := fun ty => RuntimeArrayQueries.perform types (CompilerVirtualFacts.dynamicDataInWorld facts ty)
    mutPointerType := fun ty => RuntimeArrayQueries.perform types (CompilerRuntimeQueries.mutPointerType p.runtime ty)
    mutReferenceType := fun ty => RuntimeArrayQueries.perform types (CompilerRuntimeQueries.mutReferenceType p.runtime ty)
    builtinDeref := fun ty => RuntimeArrayQueries.perform types (CompilerVirtualFacts.builtinDerefInWorld facts.context ty)
    layoutOf := fun ty => RuntimeArrayQueries.perform types (RuntimeMetadata.layoutInWorld facts.context.runtime ty)
    parentTrait := fun method => lift (CompilerRuntimeQueries.parentTrait p.runtime method)
    rebaseVirtualArgs := fun args parent concrete => RuntimeArrayQueries.perform types (CompilerRuntimeQueries.rebaseVirtualArgs p.runtime args parent concrete)
    expectResolveForVTable := fun _ method args => lift (CompilerRuntimeQueries.expectResolveForVTable p.runtime method args)
    resolveDropGlue := fun ty => RuntimeArrayQueries.perform types (CompilerRuntimeQueries.resolveDropGlue p.runtime ty)
    requiresCallerLocation := fun callee => RuntimeArrayQueries.performCompiler types (CompilerRuntimeQueries.requiresCallerLocation p.runtime callee)
    sourceScope := fun identity _ body index => do
      let actual ← RuntimeArrayQueries.performCompiler types (p.scopes.program.resolveBodyIdentity identity)
      unless actual.body == body do throw (.invalidProgram "frame body identity/content mismatch")
      RuntimeArrayQueries.performCompiler types (CompilerScopes.sourceScopeIdentity p.scopes identity index)
    unitLayout := lift (CompilerFacts.unitLayout facts.context) }
end Miri.Input.CompilerVirtualLeaves
