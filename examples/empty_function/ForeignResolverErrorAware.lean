import empty_function.ForeignResolverPrelude
namespace EmptyFunction.ForeignResolverErrorAware
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.WholeCall
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

/-- Raw shim/weak/exported selection discharges all compiler/layout UB guards.
Only the actual backing root operation is an internal effectful stage. Its
exact typed failure is propagated, including its changed state. -/
theorem resolve (s : Static) (address : ChoiceExecution.H) (before : State)
    (current : ChoiceExecution.S) (memory : current.memory = before.machine.memory)
    (runtime : current.user.payload.payload.user.runtime.externStatics = ExternMapping.runtime before)
    (definition : DefId) (backing : AllocId)
    (selection : ExternMapping.Selection s before definition backing)
    (Post : ChoiceExecution.S → Prop) (initial : Post current)
    (rootStage :
      (∃ pointer after, ForeignResolverPrelude.root address backing current = .ok pointer after ∧
        after.memory = before.machine.memory ∧ Post after) ∨
      (∃ error final, ForeignResolverPrelude.root address backing current = .error error final ∧
        RunLoop.reportsUB error = false)) :
    (∃ pointer after, ForeignResolverPrelude.resolver s address definition current = .ok pointer after ∧
      after.memory = before.machine.memory ∧ Post after ∧ pointer.provenance.getAllocId = some backing) ∨
    (∃ error final, ForeignResolverPrelude.resolver s address definition current = .error error final ∧
      RunLoop.reportsUB error = false) := by
  cases selection with
  | shim decl pointer declaration selected identity cached layout symbols foreignMetadata clash =>
    exact Or.inl ⟨pointer,current,ForeignResolverPrelude.shim s address before current memory runtime definition backing
      decl pointer declaration selected identity layout symbols foreignMetadata clash,memory,initial,identity⟩
  | weak decl pointer declaration noShim linkage size selected identity cached =>
    exact Or.inl ⟨pointer,current,ForeignResolverPrelude.weak s address before current runtime definition decl pointer
      declaration noShim linkage size selected,memory,initial,identity⟩
  | exported decl winner winnerDefinition exportId global declaration noShim linkage lookup supported kind
      definitionEq allocation image mapping descriptor payload layout mutability =>
    rcases rootStage with ⟨pointer,after,rooted,afterMemory,post⟩ | ⟨error,final,rooted,nonUB⟩
    · have identity := ForeignResolverPrelude.root_identity_actual address current after backing pointer rooted
      exact Or.inl ⟨pointer,after,ForeignResolverPrelude.exported s address before current after memory runtime
        definition winnerDefinition backing decl winner exportId global declaration noShim linkage lookup supported kind
        definitionEq allocation image mapping descriptor payload layout mutability pointer rooted identity afterMemory,
        afterMemory,post,identity⟩
    · exact Or.inr ⟨error,final,ForeignResolverPrelude.exported_error s address before current final memory runtime
        definition winnerDefinition backing decl winner exportId global declaration noShim linkage lookup supported kind
        definitionEq allocation image mapping descriptor payload layout mutability error rooted,nonUB⟩

/-- This is the exact source foreign-pointer branch; its CTFE offset is not
added to the externally resolved pointer in the fixed interpreter. -/
theorem foreign (s : Static) (address : ChoiceExecution.H) (current : ChoiceExecution.S)
    (provenance : CtfeProvenance) (offset : Size) (global : GlobalAllocation) (definition : DefId)
    (descriptor : current.memory.findGlobal? provenance.allocId = some global)
    (payload : global.payload = some (.static definition true false true)) :
    PointerSource.globalRootPointer ChoiceExecution.tapeAccess address (ForeignResolverPrelude.resolver s address)
      (Pointer.new provenance offset) current = ForeignResolverPrelude.resolver s address definition current := by
  simp [PointerSource.globalRootPointer,Pointer.new,descriptor,payload,
    get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,Pure.pure]
end EmptyFunction.ForeignResolverErrorAware
open Lean in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.ForeignResolverErrorAware.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved A foreign resolver axiom {dependency} in {name}"
