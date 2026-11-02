import duplicate_prefix.GeneralBorrowPositiveWildcardWindowInvocationBase
import duplicate_prefix.GeneralBorrowPositiveWildcardWindowOriginalInput
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardWindowOriginalDepth
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
/-- Determinism of the actual original initStackFrame result supplies its
installed depth, independent of the later permission/copy branch. -/
theorem one (s : GeneralBorrowPositiveWildcardWindowOriginalInput.Base)
    (installed : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (actual : Call.initStackFrame (ExecutionMachine.callHooks (config s.options (s.remaining+1) s.span) s.limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
          (Pointer.new .wildcard (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm,
          ActualReferenceMetadata.reference⟩,.Copy (EmptyRootArguments.second s.count)] false (.memory s.place) (.stop true) ⟨⟨#[]⟩,s.before⟩ = .ok () installed) : installed.stack.frames.size=1 := by
  obtain ⟨updated,call,slotTree,slotSize,slotLen,slotMask,slotProv,slotBytes,slotMut⟩ :=
    GeneralBorrowPositiveWildcardWindowInvocationBase.enters s s.count
  have equality:=actual.symm.trans call
  have depth:=congrArg (fun result=>match result with | .ok _ state=>state.stack.frames.size | _=>0) equality
  exact depth
end
end DuplicatePrefix.GeneralBorrowPositiveWildcardWindowOriginalDepth
