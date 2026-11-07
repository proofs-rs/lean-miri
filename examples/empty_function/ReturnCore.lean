import empty_function.ReturnSingleton
namespace EmptyFunction.ReturnCore
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.Configuration EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem core (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+2) (positive : 0 < s.options.limits.validation)
    (older : Array LocalUnit.F) (caller frame : LocalUnit.F)
    (before after : MachineHooks.MachineState MiriMemoryKind RootUser)
    (body : Meaning.FrameMatches frame s.loaded) (location : frame.location = .mir ⟨0,1⟩)
    (locals : frame.locals = #[{value := .live (.immediate .uninit),layout := some s.abi.ret.layout}])
    (noClocks : frame.extra.dataRace = none)
    (popped : (ReturnStep.control s).popFrame () (LocalUnit.current (older.push caller) frame before) =
      ((⟨⟨older.push caller⟩,after⟩ : WholeCall.State),.ok frame))
    (copyEq : (ReturnStep.control s).copyReturn () ⟨.immediate .uninit,s.abi.ret.layout⟩ frame.returnPlace
      (⟨⟨older.push caller⟩,after⟩ : WholeCall.State) = ((⟨⟨older.push caller⟩,after⟩ : WholeCall.State),.ok ()))
    (target : BasicBlockId) (unwind : UnwindAction)
    (continuation : frame.returnContinuation = .goto (some target) unwind) (varargs : frame.vaList = #[])
    (noGhost : after.user.payload.ghost = false) (shallow : after.user.payload.validation = .Shallow) :
    (ExecutionMachine.stepHooks s.cfg s.limits).returnFromCurrentFrame () false
      (LocalUnit.current (older.push caller) frame before) =
      (ReturnContinuation.resume older caller after target,.ok ()) := by
  have readEq := ReturnStep.read s metadata profile remaining capacity (older.push caller) frame before locals noClocks
  have cleanupEq := ReturnStep.cleanup s metadata remaining capacity frame
    (⟨⟨older.push caller⟩,after⟩ : WholeCall.State) target unwind continuation locals varargs
  have references := metadata.entry_references
  have block : frame.body.basicBlocks[0]? = some metadata.entry.blockId := by
    rw [body.1]; exact references.block
  have blockNode : frame.mirTables.blocks.lookup metadata.entry.blockId.index = .ok metadata.entry.block := by
    rw [body.2.2]; exact references.blockNode
  have cleanup := (ReturnStep.block_observations s metadata).1
  rw [ReturnStep.source]
  generalize actualControl : ReturnStep.control s = hooks at readEq popped copyEq cleanupEq ⊢
  cases hooks
  unfold ControlFlow.returnFromCurrentFrame
  simp only [BodyStep.current,LocalUnit.current,Stack.currentFrame?,Array.back?_push,location,block,blockNode,cleanup,
    Bool.false_bne,Bool.false_and,Bool.not_false,Bool.false_eq_true,
    bne_self_eq_false,Id.run,bind,Bind.bind,pure,Pure.pure,↓reduceIte]
  simp only [BodyStep.current,LocalUnit.current] at readEq popped copyEq cleanupEq
  erw [readEq]
  erw [popped]
  simp only
  erw [copyEq]
  erw [cleanupEq]
  simp only [continuation]
  exact ReturnContinuation.returnToBlock_push older caller after target

end EmptyFunction.ReturnCore
