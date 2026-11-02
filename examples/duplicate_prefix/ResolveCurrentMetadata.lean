import duplicate_prefix.MetadataCallQueries
namespace DuplicatePrefix.ResolveCurrentMetadata
open Miri Miri.ABI Miri.Input Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem resolve
    (compiler : CompilerProviders.Prepared)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState K User) (location : Location)
    (source : LoweredBody) (loaded : LoadedBody) (block : MIR.BasicBlock)
    (resolution : CallResolution.Resolution) (definition : DefId) (args : Array GenericArg) (ty : TyId)
    (located : frame.location = .mir location)
    (sourceAt : compiler.program.bundle.bodies[frame.bodyIdentity.index]? = some source)
    (sameBody : source.body = frame.body)
    (loadedAt : CallResolution.loadedBodyOfInstance compiler.lifecycle.calls.calls frame.functionInstance = .ok loaded)
    (sameIdentity : loaded.identity = frame.bodyIdentity)
    (blockAt : source.body.basicBlocks[location.block]? = some block)
    (atEnd : location.statementIndex = block.statements.size)
    (resolveAt : CallResolution.atSite compiler.lifecycle.calls.calls ⟨frame.bodyIdentity.index,location.block⟩ = .ok resolution)
    (functionType : (resolution.source.getObjVal? "function_type").bind
      (fun object => (object.getObjVal? "type_id").bind Lean.Json.getNat?) = .ok ty)
    (kind : CompilerFunctionFacts.kind compiler.functions ty = .ok (.FnDef definition args))
    (argsSelf : (args == args) = true) :
    CompilerProviders.resolveCurrent compiler definition args (Storage.withCurrent frames frame machine) =
      .ok resolution.callee (Storage.withCurrent frames frame machine) := by
  have frameBlock : frame.body.basicBlocks[location.block]? = some block := by
    rw [← sameBody]
    exact blockAt
  unfold CompilerProviders.resolveCurrent
  simp only [MachineHooks.currentFrame,Storage.withCurrent,Stack.currentFrame?,Array.back?_push,
    bind,EStateM.bind,get,getThe,MonadStateOf.get,EStateM.get,pure,EStateM.pure,located]
  unfold_provider_lift
  simp only [sourceAt,sameBody,beq_self_eq_true,ite_true,loadedAt,sameIdentity,
    Except.bind,Except.pure,bind,EStateM.bind,pure,EStateM.pure]
  simp only [frameBlock,atEnd,beq_self_eq_true,ite_true]
  simp only [resolveAt,Except.bind,Except.pure,bind,EStateM.bind,pure,EStateM.pure]
  cases first : resolution.source.getObjVal? "function_type" with
  | error reason => simp [first,Except.bind] at functionType
  | ok object =>
    cases second : object.getObjVal? "type_id" with
    | error reason => simp [first,second,Except.bind] at functionType
    | ok number =>
      cases third : number.getNat? with
      | error reason => simp [first,second,third,Except.bind] at functionType
      | ok typeId =>
        have same : typeId = ty := by simpa [first,second,third,Except.bind] using functionType
        subst typeId
        simp [first,second,third,kind,argsSelf,pure,Pure.pure,EStateM.pure]

#print axioms resolve
end DuplicatePrefix.ResolveCurrentMetadata
