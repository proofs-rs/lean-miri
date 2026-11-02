import duplicate_prefix.GeneralBorrowForestCaller
import duplicate_prefix.GenericFunctionPoolSafety
namespace DuplicatePrefix.GeneralBorrowForestFunctionSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open Miri.DataStructures Miri.TreeBorrows.Tree
open ActualReferenceContext
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

/-- General arbitrary-depth forest resources and data-only entry ownership
suffice for all counts' genuine ROOT invocation through physical return and
NoUB, without a star or homogeneous-map restriction. Allocation/history final
theorems derive this helper Data rather than expose it as a final premise. -/
theorem invoke (tree : BorrowTree) (root : UniIndex)
    (resources : GeneralBorrowRecursiveSharedResources.Resources tree root)
    (incomingTag newTag : BorTag) (inputOffset inputLen : UInt64)
    (data : GenericAsMutPtrEntryValidity.Data tree {} incomingTag newTag inputOffset inputLen)
    (reserve : Fin 5 → BorTag)
    (reserved : ∀ index, GeneralBorrowTagMap.Fresh tree.tagMapping (reserve index))
    (s : GeneralBorrowForestCaller.Caller tree incomingTag newTag inputOffset inputLen reserve)
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
    (GeneralBorrowForestCaller.pool tree root resources incomingTag newTag inputOffset inputLen data reserve reserved s) count
end
end DuplicatePrefix.GeneralBorrowForestFunctionSafety
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowForestFunctionSafety.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved recurring function safety dependency {dependency}"
