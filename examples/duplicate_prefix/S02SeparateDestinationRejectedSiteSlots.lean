import duplicate_prefix.S02SeparateDestinationSharedShapeSite
import duplicate_prefix.S02SeparateDestinationInstalledLocals

namespace DuplicatePrefix.S02SeparateDestinationRejectedSiteSlots
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification ActualReferenceContext CanonicalConfigFacts
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

/-- The actual positive call's nonzero prefix fixes all remaining rejected-guard locals. -/
theorem at_shared_site
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (different : id ≠ input.contract.destination.id)
    (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance =
      .concrete input.contract.destination.id returnTag)
    (entry frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (actual : Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] entry machine))
    (shape : GenericFunctionEntryPrefix.Shape entry frame count) :
    frame.locals[0]? = some ⟨.live (.immediate .uninit),none⟩ ∧
    frame.locals[13]? = some ⟨.live (.immediate .uninit),none⟩ ∧
    frame.locals[7]? = some ⟨.live (.immediate .uninit),none⟩ ∧
    frame.locals[8]? = some ⟨.live (.immediate .uninit),none⟩ ∧
    frame.locals[9]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),
      some RootCompilerFacts.usizeLayout⟩ ∧
    frame.locals[10]? = some ⟨.live (.immediate .uninit),none⟩ := by
  obtain ⟨_reference,otherFrame,otherMachine,otherActual,_size,_location,slots,_clocks,_immediate⟩ :=
    S02SeparateDestinationInstalledLocals.ready id tag address len count input nonempty different
      returnTag returnConcrete
  have same : Storage.withCurrent #[] otherFrame otherMachine = Storage.withCurrent #[] entry machine :=
    (EStateM.Result.ok.inj (otherActual.symm.trans actual)).2
  have frameEq : otherFrame = entry := by
    have h := congrArg (fun s : RootState => s.stack.frames[0]?) same
    exact Option.some.inj (by simpa [Storage.withCurrent] using h)
  have installed0 : entry.locals[0]? = some ⟨.live (.immediate .uninit),none⟩ := by
    rw [←frameEq]
    simpa using slots ⟨0,by decide⟩
  have installed13 : entry.locals[13]? = some ⟨.live (.immediate .uninit),none⟩ := by
    rw [←frameEq]
    simpa using slots ⟨13,by decide⟩
  exact ⟨shape.slot0.trans installed0,(shape.keep 13 (by decide)).trans installed13,
    shape.slot7,shape.slot8,shape.slot9,shape.slot10⟩

end
end DuplicatePrefix.S02SeparateDestinationRejectedSiteSlots

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SeparateDestinationRejectedSiteSlots.at_shared_site) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved rejected site locals dependency {dependency}"
