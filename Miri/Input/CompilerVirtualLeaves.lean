import Miri.Input.CompilerCallPipeline
import Miri.Input.SourceCallerLocation

/-! Complete compiler dictionary for source virtual/drop/caller-location
drivers. All identities refer to the pipeline's final shared tables. -/
namespace Miri.Input.CompilerVirtualLeaves
open Miri.Interpreter
private def lift (value : Except String A) : EStateM StepError S A :=
  match value with
  | .ok value => pure value
  | .error reason => throw (.unsupported s!"compiler virtual query: {reason}")

private def source (access : SourceCompilerWorld.Access S) (operation : SourceCompilerWorld.World → Except String A) :
    EStateM StepError S A := do
  let some world := access.get (← get) | throw (.unsupported "compiler virtual World unavailable")
  lift (operation world)

def make (p : CompilerCallPipeline.Prepared) (access : SourceCompilerWorld.Access S) : VirtualCalls.CompilerHooks S C :=
  let facts := p.symbols.facts
  let sourceMode := p.calls.program.input.sourceMaterial.isSome
  let hooks : VirtualCalls.CompilerHooks S C := {
    instanceArgs := fun inst => lift (CompilerInstance.argsOf facts.context.loweringContext.instances inst)
    classifyReceiver := fun ty => lift (CompilerVirtualFacts.receiverKind facts.context ty)
    fieldLayout := fun layout index => lift ((facts.context.runtime.field layout index).mapError toString)
    structTailForCodegen := fun ty => lift (CompilerFacts.requiredType facts.context ty "metadata_tail")
    dynamicData := fun ty => lift (CompilerVirtualFacts.dynamicData facts ty)
    mutPointerType := fun ty => lift (CompilerRuntimeQueries.mutPointerType p.runtime ty)
    mutReferenceType := fun ty => lift (CompilerRuntimeQueries.mutReferenceType p.runtime ty)
    builtinDeref := fun ty => lift (CompilerFacts.builtinDeref facts.context ty true)
    layoutOf := fun ty => lift (CompilerFacts.layoutOf facts.context ty)
    parentTrait := fun method => lift (CompilerRuntimeQueries.parentTrait p.runtime method)
    rebaseVirtualArgs := fun args parent concrete => lift (CompilerRuntimeQueries.rebaseVirtualArgs p.runtime args parent concrete)
    expectResolveForVTable := fun _ method args => lift (CompilerRuntimeQueries.expectResolveForVTable p.runtime method args)
    resolveDropGlue := fun ty => lift (CompilerRuntimeQueries.resolveDropGlue p.runtime ty)
    requiresCallerLocation := fun callee => if sourceMode then
      source access (SourceCallerLocation.requiresCallerLocation · callee)
      else lift (CompilerRuntimeQueries.requiresCallerLocation p.runtime callee)
    sourceScope := fun identity callee body index => do
      if sourceMode then return ← source access (SourceCallerLocation.sourceScope · identity callee body index)
      let some actual := p.scopes.program.bundle.bodies[identity.index]?
        | throw (.unsupported "canonical frame body identity is absent")
      unless actual.body == body do throw (.invalidProgram "frame body identity/content mismatch")
      lift (CompilerScopes.sourceScope p.scopes identity.index index)
    unitLayout := lift (CompilerFacts.unitLayout facts.context) }
  if sourceMode then hooks else CompilerVirtualFacts.scopeHooks p.scopes hooks
/-- Exact live query boundary, including the legacy inline override and all
missing-World/query errors. No successful machine action is a hypothesis. -/
theorem requiresCallerLocation_at {C : Type} (p : CompilerCallPipeline.Prepared)
    (access : SourceCompilerWorld.Access S) (callee : CallInstance) (before : S) :
    (make (C := C) p access).requiresCallerLocation callee before =
      if p.calls.program.input.sourceMaterial.isSome then
        match access.get before with
        | none => .error (.unsupported "compiler virtual World unavailable") before
        | some world => match SourceCallerLocation.requiresCallerLocation world callee with
          | .ok value => .ok value before
          | .error reason => .error (.unsupported s!"compiler virtual query: {reason}") before
      else match CompilerVirtualFacts.inlineAttribute p.scopes callee with
        | some value => .ok value before
        | none => match CompilerRuntimeQueries.requiresCallerLocation p.runtime callee with
          | .ok value => .ok value before
          | .error reason => .error (.unsupported s!"compiler virtual query: {reason}") before := by
  cases mode : p.calls.program.input.sourceMaterial.isSome with
  | false =>
    cases inline : CompilerVirtualFacts.inlineAttribute p.scopes callee with
    | some value => simp [make, mode, CompilerVirtualFacts.scopeHooks, inline, pure, EStateM.pure]
    | none =>
      cases result : CompilerRuntimeQueries.requiresCallerLocation p.runtime callee <;>
        simp [make, mode, CompilerVirtualFacts.scopeHooks, inline, lift, result,
          get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure] <;> rfl
  | true =>
    cases current : access.get before with
    | none =>
      simp [make, mode, source, current, get, getThe, MonadStateOf.get, EStateM.get,
        bind, EStateM.bind, pure, EStateM.pure] <;> rfl
    | some world =>
      cases result : SourceCallerLocation.requiresCallerLocation world callee <;>
        simp [make, mode, source, lift, current, result, get, getThe, MonadStateOf.get,
          EStateM.get, bind, EStateM.bind, pure, EStateM.pure] <;> rfl

end Miri.Input.CompilerVirtualLeaves
