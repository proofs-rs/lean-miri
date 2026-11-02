import duplicate_prefix.GeneralBorrowPositiveWildcardOriginalInput
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardOriginalDepth
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
/-- Determinism of the actual original initStackFrame result supplies its
installed depth, independent of the later permission/copy branch. -/
theorem one (s : GeneralBorrowPositiveWildcardOriginalInput.Base)
    (installed : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (actual : Call.initStackFrame (ExecutionMachine.callHooks (config s.options (s.remaining+1) s.span) s.limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
          (Pointer.new .wildcard (Size.ofBytes s.base)) s.len ActualReferenceMetadata.reference).imm,
          ActualReferenceMetadata.reference⟩,.Copy (EmptyRootArguments.second s.count)] false (.memory s.place) (.stop true) ⟨⟨#[]⟩,s.before⟩ = .ok () installed) : installed.stack.frames.size=1 := by
  obtain ⟨updated,call,slotTree,slotSize,slotLen,slotMask,slotProv,slotBytes,slotMut⟩ :=
    GeneralBorrowPositiveWildcardFunctionInvocation.enters s.options s.limits s.remaining s.span s.ctx s.debugOff s.cmp s.dynamicFuel s.validityFuel s.fuelEq s.validationEq s.id s.tracker s.base s.len s.count s.nonzero s.entry s.positive s.signedFits s.bounds s.before s.ghost s.shallow s.cachedAddress s.present s.enabled s.fresh s.position s.positionValid s.ordered s.addressRow s.addressMode s.exposedAlloc s.location s.head s.headNode s.extraRoots s.nodes s.states s.locations s.roots s.headPresent s.headLeaf s.headExposed s.headStored s.coherent s.short s.data s.tagFresh s.noFree s.fits s.race s.metadata s.notConstructed s.retagCtx s.place s.layout s.slotId s.slotEntry s.slotBase s.slotRoot s.slotPointer s.aligned s.slotCached s.slotTree s.slotSize s.slotPresent s.separate s.slotFresh s.slotDistinct s.slotParentDistinct s.slotFree s.mutable s.storage s.maskLength s.provenance s.noBackend s.extras s.thread s.active s.noCache
  have equality:=actual.symm.trans call
  have depth:=congrArg (fun result=>match result with | .ok _ state=>state.stack.frames.size | _=>0) equality
  exact depth
end
end DuplicatePrefix.GeneralBorrowPositiveWildcardOriginalDepth
