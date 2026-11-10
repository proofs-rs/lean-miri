import empty_function.LocalModel
namespace EmptyFunction.ProjectedSpan
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open EmptyFunction.WholeCall EmptyFunction.Specification EmptyFunction.Configuration
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

 theorem declaration (p : CompilerProviders.Prepared) (frame : LocalUnit.F) (id : MIR.LocalId) (ty : TyId)
    (aligned : ∀ body ∈ p.program.bundle.bodies,
      body.input.localSources.size = body.input.mir.locals.size)
    (normalized : CompilerFrameContext.localType p frame id = .ok ty) :
    ∃ body decl, CompilerFrameContext.bodyOfFrame p frame = .ok body ∧
      body.input.localSources[id]? = some decl ∧ body ∈ p.program.bundle.bodies := by
  cases bodyEq : CompilerFrameContext.bodyOfFrame p frame with
  | error error =>
    simp [CompilerFrameContext.localType,LoweredBody.body,bodyEq,bind,Bind.bind,Except.bind] at normalized
  | ok body =>
    have member : body ∈ p.program.bundle.bodies := by
      unfold CompilerFrameContext.bodyOfFrame at bodyEq
      cases row : p.program.bundle.bodies[frame.bodyIdentity.index]? with
      | none => simp [row,bind,Bind.bind,Except.bind,throw,throwThe,MonadExceptOf.throw,Except.error] at bodyEq
      | some actual =>
        have member := Array.mem_of_getElem? row
        simp only [row] at bodyEq
        repeat' (split at bodyEq <;> try simp_all [bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure])
    cases declEq : body.input.mir.locals[id]? with
    | none => simp [CompilerFrameContext.localType,LoweredBody.body,bodyEq,declEq,bind,Bind.bind,Except.bind] at normalized
    | some localTy =>
      obtain ⟨inRange, _⟩ := Array.getElem?_eq_some_iff.mp declEq
      have sourceRange : id < body.input.localSources.size := by
        simpa only [aligned body member] using inRange
      exact ⟨body, body.input.localSources[id], rfl, Array.getElem?_eq_getElem sourceRange, member⟩

 theorem local_span (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (frames : Array LocalUnit.F) (frame : LocalUnit.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser) (id : MIR.LocalId) (ty : TyId)
    (normalized : CompilerFrameContext.localType s.prepared.compiler frame id = .ok ty) :
    ∃ span, s.cfg.compiler.localSpan frame.body id (LocalUnit.current frames frame machine) =
      .ok span (LocalUnit.current frames frame machine) := by
  obtain ⟨body,decl,bodyEq,declEq,member⟩ := declaration s.prepared.compiler frame id ty metadata.compilerLocalSourceAlignment normalized
  have declMember := Array.mem_of_getElem? declEq
  have bounded := metadata.compilerLocalSourceSpans body member decl declMember
  let index := decl.spanId
  obtain ⟨remaining,eq⟩ : ∃ n : Nat, s.capacity = n+1 := ⟨s.capacity-1,by omega⟩
  have source := BodyPlaceDictionaries.fields_of_make s.prepared.compiler s.prepared.image s.bytes s.options
    (Configuration.leaves s.prepared s.options.place.debugAssertions) remaining metadata.construction s.cfg
    (by simpa only [Configuration.rootConfig,eq] using s.built)
  refine ⟨⟨index⟩,?_⟩
  rw [source.localSpan]
  with_unfolding_all
    simp [CompilerFrameContext.localSpan,MachineHooks.currentFrame,LocalUnit.current,Stack.currentFrame?,
      bodyEq,declEq,bounded,index,get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,
      EStateM.pure,Except.pure,Except.bind]
  simp_all!
  simp [pure,Pure.pure,EStateM.pure,declEq,bounded,index]

end EmptyFunction.ProjectedSpan
