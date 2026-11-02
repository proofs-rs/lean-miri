import duplicate_prefix.GeneralBorrowSubsliceCaller
import duplicate_prefix.GenericFunctionPoolSafety
namespace DuplicatePrefix.GeneralBorrowSubsliceFunctionSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open Miri.DataStructures Miri.TreeBorrows.Tree
open ActualReferenceContext GeneralBorrowPartitionState
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

/-- A recurring partition state supplies every count's genuine ROOT invocation
for any positive in-bounds allocation-interior slice, through physical return
and NoUB. Borrow-state formation is separate; the physical Caller retains all
address, initialized-slice, resource, runtime and compiler-metadata conditions. -/
theorem invoke (tree : BorrowTree) (root : UniIndex) (bytes : UInt64)
    (state : State tree root bytes) (tag : BorTag)
    (freshTag : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (reserve : Fin 5 → BorTag)
    (reserved : ∀ index, GeneralBorrowTagMap.Fresh tree.tagMapping (reserve index))
    (s : GeneralBorrowSubsliceCaller.Caller tree root bytes state tag reserve)
    (count : UInt64) :
    let cfg := config s.options (s.remaining+1) s.span
    ∃ installed finalState,
      Call.initStackFrame (ExecutionMachine.callHooks cfg s.limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
          (Pointer.new (.concrete s.id s.parentTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm,
          ActualReferenceMetadata.reference⟩,.Copy (EmptyRootArguments.second count)] false (.memory s.place) (.stop true)
        ⟨⟨#[]⟩,s.before⟩ = .ok () installed ∧
      SuccessfulTrace.Trace cfg s.limits installed finalState ∧
      ExecutionMachine.step cfg s.limits () finalState = (finalState,.ok false) ∧
      finalState.stack.frames = #[] ∧
      CallSafety.NoUBBeforeReturn
        (⟨cfg,s.limits,fun _ _ => True⟩ : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit)
        1 installed ∧
      (∀ before, SuccessfulTrace.Trace cfg s.limits installed before →
        ∃ after continuing, ExecutionMachine.step cfg s.limits () before = (after,.ok continuing)) := by
  exact GenericFunctionPoolSafety.invoke
    (GeneralBorrowSubsliceCaller.pool tree root bytes state tag freshTag reserve reserved s) count
end
end DuplicatePrefix.GeneralBorrowSubsliceFunctionSafety
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowSubsliceFunctionSafety.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved recurring function safety dependency {dependency}"
