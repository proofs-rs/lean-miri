import empty_function.ProjectedInit
import empty_function.BodyAssignment
namespace EmptyFunction.ProjectedModel
open Miri Miri.Memory Miri.Interpreter
open EmptyFunction.WholeCall EmptyFunction.Configuration
set_option autoImplicit false

def caller (s : Static) (p : Packet) (tracker : MachineHooks.BorrowState)
    (destination : EmptyFunction.InputDraft.LocalDestination s p tracker)
    (bound : destination.localId < destination.caller.locals.size) : LocalUnit.F :=
  EmptyFunction.LocalImmediate.cached destination.caller destination.localId destination.slot destination.baseLayout bound

def initializedMachine (s : Static) (p : Packet) (tracker : MachineHooks.BorrowState)
    (destination : EmptyFunction.InputDraft.LocalDestination s p tracker) (older : Array LocalUnit.F)
    (bound : destination.localId < destination.caller.locals.size) (frame previous : LocalUnit.F) :
    MachineHooks.MachineState MiriMemoryKind RootUser :=
  FrameRelevance.pushedMachine (older.push (caller s p tracker destination bound)) frame previous
    (s.cfg.lifecycle.freshLocalsIdentity p.before.machine).1
end EmptyFunction.ProjectedModel
namespace EmptyFunction.ProjectedBody
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open EmptyFunction.Configuration EmptyFunction.CanonicalDictionaries EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
 theorem init_body (s : Static) (metadata : Metadata s) [SuccessfulConstant metadata] (profile : Profile s)
    (p : Packet) (runtime : RuntimeProfile s p) (input : InputDraft.CurrentInputDraft s p)
    {choiceCondition : Prop} (resources : ResourceMargins s p choiceCondition) (destination : InputDraft.LocalDestination s p input.tracker)
    (offset : Size) (projected : destination.offset = some offset)
    (immediate : destination.oldOperand = .immediate .uninit) :
    ∃ (older : Array LocalUnit.F) (bound : destination.localId < destination.caller.locals.size)
      (installed : State) (frame : LocalUnit.F) (machine : MachineHooks.MachineState MiriMemoryKind RootUser),
      p.before.stack.frames = older.push destination.caller ∧
      WholeCall.install s p = .ok () installed ∧ installed.stack.frames.size = depth p ∧
      ExecutionMachine.step s.cfg s.limits () installed =
        (LocalUnit.current (older.push (ProjectedModel.caller s p input.tracker destination bound)) frame machine,.ok true) ∧
      Meaning.FrameMatches frame s.loaded ∧ frame.bodyIdentity = s.loaded.identity ∧
      frame.functionInstance = s.functionInstance ∧ frame.location = .mir ⟨0,1⟩ ∧
      frame.locals = #[{value := .live (.immediate .uninit),layout := some s.abi.ret.layout}] ∧
      frame.extra.borrowTracker = some {} ∧ frame.extra.dataRace = none ∧ frame.returnPlace = p.destination ∧
      frame.returnContinuation = CanonicalInit.normalizedContinuation s (.goto (some p.returnBlock) p.unwind) ∧
      frame.vaList = #[] ∧ machine.user.payload.ghost = false ∧ machine.user.payload.validation = .Shallow ∧
      (∃ previous, machine = ProjectedModel.initializedMachine s p input.tracker destination older bound frame previous) ∧
      machine.borrowTracker = p.before.machine.borrowTracker := by
  have budget : 64 ≤ resources.budget := by have bound := resources.reserve; unfold work at bound; omega
  obtain ⟨remaining,capacity⟩ : ∃ n : Nat, s.capacity = n+2 := ⟨s.capacity-2,by have bound := resources.capacity; omega⟩
  have validation : 0 < s.options.limits.validation := by have bound := resources.configuredValidation; omega
  obtain ⟨older,bound,entry,machine,original,installed,body,identity,function,location,locals,tracked,noClocks,
    returnPlace,continuation,varargs,noGhost,shallow,⟨previous,machineEq⟩,machineTracked⟩ :=
      ProjectedInit.uninit s metadata profile p runtime input resources destination offset projected immediate
  let frames := older.push (ProjectedModel.caller s p input.tracker destination bound)
  have entrySame : BodyStep.withUnit entry .uninit none = entry := by
    change {entry with locals := #[{value := .live (.immediate .uninit),layout := none}]} = entry
    rw [←locals]
  have first := BodyAssignment.step s metadata profile remaining capacity validation frames entry machine
    identity body function location noClocks noGhost shallow
  rw [entrySame] at first
  let next : LocalUnit.F := {(BodyStep.withUnit entry .uninit (some s.abi.ret.layout)) with location := .mir ⟨0,1⟩}
  refine ⟨older,bound,LocalUnit.current frames entry machine,next,machine,original,installed,?_,first,
    ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,noGhost,shallow,⟨previous,?_⟩,machineTracked⟩
  · simp [LocalUnit.current,frames,depth,original]
  all_goals try rfl
  all_goals try simpa only [Meaning.FrameMatches,next,BodyStep.withUnit,LocalUnit.withUnit] using body
  all_goals try simpa only [next,BodyStep.withUnit,LocalUnit.withUnit] using identity
  all_goals try simpa only [next,BodyStep.withUnit,LocalUnit.withUnit] using function
  all_goals try simpa only [next,BodyStep.withUnit,LocalUnit.withUnit] using tracked
  all_goals try simpa only [next,BodyStep.withUnit,LocalUnit.withUnit] using noClocks
  all_goals try simpa only [next,BodyStep.withUnit,LocalUnit.withUnit] using returnPlace
  all_goals try simpa only [next,BodyStep.withUnit,LocalUnit.withUnit] using continuation
  all_goals try simpa only [next,BodyStep.withUnit,LocalUnit.withUnit] using varargs
  rw [machineEq]
  rfl

end EmptyFunction.ProjectedBody
