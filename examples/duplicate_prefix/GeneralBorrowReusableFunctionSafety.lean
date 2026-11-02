import duplicate_prefix.GeneralBorrowReusableCaller
import duplicate_prefix.GenericFunctionPoolSafety
namespace DuplicatePrefix.GeneralBorrowReusableFunctionSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open Miri.DataStructures Miri.TreeBorrows.Tree
open ActualReferenceContext GeneralBorrowReusableStar
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

/-- A recurring sparse star state and separate physical caller conditions
suffice for every count's genuine ROOT invocation through physical return.
The initial graph/profile are explicit in this bridge; generated-history
formation is a separate theorem. -/
theorem invoke (tree : BorrowTree) (root : UniIndex) (bytes : UInt64)
    (state : State tree root bytes) (tag : BorTag)
    (freshTag : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (reserve : Fin 5 → BorTag)
    (reserved : ∀ index, GeneralBorrowTagMap.Fresh tree.tagMapping (reserve index))
    (s : GeneralBorrowReusableCaller.Caller tree root bytes state tag reserve)
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
    (GeneralBorrowReusableCaller.pool tree root bytes state tag freshTag reserve reserved s) count
end
end DuplicatePrefix.GeneralBorrowReusableFunctionSafety
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowReusableFunctionSafety.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved recurring function safety dependency {dependency}"
