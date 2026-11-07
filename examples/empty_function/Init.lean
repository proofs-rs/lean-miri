import Miri.Input.CompilerFrameMetadata
import Miri.Input.CompilerLifecycle

namespace EmptyFunction.Init
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.Concurrency
set_option autoImplicit false
variable {K U C : Type}
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

def raw (h : CallMachine.Lifecycle K U C) (before : MachineHooks.State K U)
    (body : LoadedBody) (fnInstance : CallInstance) (destination : RuntimeStackPlace Provenance)
    (continuation : ReturnContinuation) (span : SpanRef) : Frame Provenance LocalLayout Unit :=
  Frame.create body fnInstance () continuation destination span (h.freshLocalsIdentity before.machine).2

def created (h : CallMachine.Lifecycle K U C) (before : MachineHooks.State K U)
    (body : LoadedBody) (fnInstance : CallInstance) (destination : RuntimeStackPlace Provenance)
    (continuation : ReturnContinuation) (span : SpanRef)
    (metadata : CompilerFrameMetadata.Prepared) (relevant : Array Nat) (definition : DefinitionId) :=
  CompilerFrameMetadata.resolvedFrame (raw h before body fnInstance destination continuation span)
    (h.freshLocalsIdentity before.machine).1
    (CompilerFrameMetadata.resolvedRank metadata.localCrate definition.crateIndex relevant)

theorem push_raw (h : CallMachine.Lifecycle K U C) (before : MachineHooks.State K U)
    (body : LoadedBody) (fnInstance : CallInstance) (destination : RuntimeStackPlace Provenance)
    (continuation : ReturnContinuation) (span : SpanRef)
    (metadata : CompilerFrameMetadata.Prepared) (relevant : Array Nat) (definition : DefinitionId)
    (lifecycle : CompilerLifecycle.Prepared) (actual : LoweredBody)
    (compiler : h.compiler = CompilerFrameMetadata.hooks metadata relevant)
    (preamble : h.preambleSpan = CompilerLifecycle.preambleSpan lifecycle)
    (required : h.requiredConstants = CompilerLifecycle.requiredConstants lifecycle)
    (inline : CompilerVirtualFacts.inlineAttribute metadata.calls.scopes fnInstance = .ok none ∨
      CompilerVirtualFacts.inlineAttribute metadata.calls.scopes fnInstance = .ok (some false))
    (track : CompilerRuntimeQueries.requiresCallerLocation metadata.calls.runtime fnInstance = .ok false)
    (definitionAt : metadata.calls.calls.program.compilerTables.definitions[fnInstance.defId]? = some definition)
    (row : lifecycle.program.bundle.bodies[body.identity.index]? = some actual)
    (contents : actual.body = body.body)
    (wire : actual.bodyId = body.bodyId)
    (evidence : lifecycle.entries[body.identity.index]? = some ⟨.ok span,.ok fnInstance,.ok #[]⟩)
    (thread : ThreadRecord) (index : Nat)
    (active : (h.freshLocalsIdentity before.machine).1.threads.activeThread? = some thread)
    (previous : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (cached : FrameRelevance.top ⟨before.stack.frames.push
      (created h before body fnInstance destination continuation span metadata relevant definition)⟩
      thread.topUserRelevantFrame = some index)
    (selected : (before.stack.frames.push
      (created h before body fnInstance destination continuation span metadata relevant definition))[index]? = some previous) :
    CallMachine.pushRaw h false fnInstance body destination continuation before =
      .ok () ⟨⟨before.stack.frames.push
        (created h before body fnInstance destination continuation span metadata relevant definition)⟩,
        FrameRelevance.pushedMachine before.stack.frames
          (created h before body fnInstance destination continuation span metadata relevant definition)
          previous (h.freshLocalsIdentity before.machine).1⟩ := by
  have spanQuery := CompilerLifecycle.preamble_known (K := K) (U := U)
    lifecycle body actual span fnInstance row contents wire evidence
  have initialized := CompilerFrameMetadata.initFrame_explicit metadata relevant
    (raw h before body fnInstance destination continuation span) definition inline track definitionAt
    ({before with machine := (h.freshLocalsIdentity before.machine).1})
  have constants := CompilerLifecycle.required_empty lifecycle body actual span fnInstance row contents wire evidence
    before.stack.frames (created h before body fnInstance destination continuation span metadata relevant definition)
    (h.freshLocalsIdentity before.machine).1 rfl rfl
  have relevance := FrameRelevance.afterPush_known before.stack.frames
    (created h before body fnInstance destination continuation span metadata relevant definition)
    previous (h.freshLocalsIdentity before.machine).1 thread index active cached selected
  unfold CallMachine.pushRaw
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,
    set,MonadStateOf.set,EStateM.set,pure,EStateM.pure]
  rw [preamble, spanQuery]
  simp only [bind,EStateM.bind,pure,EStateM.pure]
  rw [compiler]
  change ((do
    let frame ← MachineHooks.initFrame (FrameMetadata.userRelevance (CompilerFrameMetadata.hooks metadata relevant))
      (raw h before body fnInstance destination continuation span)
    modify fun state => {state with stack := ⟨state.stack.frames.push frame⟩}
    h.requiredConstants body
    FrameRelevance.afterStackPush false) : MachineHooks.M K U Unit)
    {before with machine := (h.freshLocalsIdentity before.machine).1} = _
  simp only [bind,EStateM.bind]
  rw [initialized]
  simp only [modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet]
  change ((do
    h.requiredConstants body
    FrameRelevance.afterStackPush false) : MachineHooks.M K U Unit)
    (⟨⟨before.stack.frames.push (created h before body fnInstance destination continuation span metadata relevant definition)⟩,
      (h.freshLocalsIdentity before.machine).1⟩ : MachineHooks.State K U) = _
  rw [required]
  simp only [bind,EStateM.bind]
  rw [constants]
  exact relevance

theorem mode_pure (mode : Miri.TreeBorrows.RetagPolicy.RetagMode)
    {A : Type} (value : A) (state : MachineHooks.State K U) :
    MachineHooks.withRetagMode mode (pure value) state = .ok value state := by
  cases tracker : state.machine.borrowTracker with
  | none => simp [MachineHooks.withRetagMode,tracker,
      get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure]
  | some before =>
    simp [MachineHooks.withRetagMode,tracker,
      get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
      modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet]
    change {state with machine := {state.machine with borrowTracker := some before}} = state
    rw [←tracker]
end EmptyFunction.Init
