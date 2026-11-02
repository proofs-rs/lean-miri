import duplicate_prefix.S02AcceptedSharedFullSiteShapeBothNode

namespace DuplicatePrefix.S02AcceptedGuardCells
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- The accepted comparison prelude's untouched locals are inherited from
the actual installed frame, for arbitrary positive source and separate return. -/
theorem at_actual_site
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
    (entry site : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (actual : Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] entry machine))
    (shape : GenericFunctionEntryPrefix.Shape entry site count) :
    site.locals[0]? = some ⟨.live (.immediate .uninit),none⟩ ∧
    site.locals[13]? = some ⟨.live (.immediate .uninit),none⟩ ∧
    site.locals[15]? = some ⟨.dead,none⟩ ∧
    site.locals[16]? = some ⟨.dead,none⟩ ∧
    site.locals[7]? = some ⟨.live (.immediate .uninit),none⟩ ∧
    site.locals[8]? = some ⟨.live (.immediate .uninit),none⟩ ∧
    site.locals[9]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩ ∧
    site.locals[10]? = some ⟨.live (.immediate .uninit),none⟩ := by
  obtain ⟨_reference,profile,_other,actual2,_size,_location,slots,_clocks,_immediate⟩ :=
    S02SeparateDestinationInstalledLocals.ready id tag address len count input nonempty different
      returnTag returnConcrete
  have same : Storage.withCurrent #[] profile _other = Storage.withCurrent #[] entry machine :=
    (EStateM.Result.ok.inj (actual2.symm.trans actual)).2
  have frameEq : profile = entry := by
    have h := congrArg (fun s : RootState => s.stack.frames[0]?) same
    exact Option.some.inj (by simpa [Storage.withCurrent] using h)
  have cell (i : Fin 25) := slots i
  rw [frameEq] at cell
  have zero : entry.locals[0]? = some ⟨.live (.immediate .uninit),none⟩ := by
    simpa only [show 14 ≠ 0 by decide,show 13 ≠ 0 by decide,show 6 ≠ 0 by decide,
      show 0 = 0 by rfl,or_true,ite_true] using cell ⟨0,by decide⟩
  have thirteen : entry.locals[13]? = some ⟨.live (.immediate .uninit),none⟩ := by
    simpa using cell ⟨13,by decide⟩
  have fifteen : entry.locals[15]? = some ⟨.dead,none⟩ := by
    simpa using cell ⟨15,by decide⟩
  have sixteen : entry.locals[16]? = some ⟨.dead,none⟩ := by
    simpa using cell ⟨16,by decide⟩
  exact ⟨shape.slot0.trans zero,(shape.keep 13 (by decide)).trans thirteen,
    (shape.keep 15 (by decide)).trans fifteen,(shape.keep 16 (by decide)).trans sixteen,
    shape.slot7,shape.slot8,shape.slot9,shape.slot10⟩

end
end DuplicatePrefix.S02AcceptedGuardCells

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02AcceptedGuardCells.at_actual_site) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved accepted guard cells dependency {dependency}"
