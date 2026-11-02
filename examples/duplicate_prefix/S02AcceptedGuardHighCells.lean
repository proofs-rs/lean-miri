import duplicate_prefix.S02AcceptedGuardCells

namespace DuplicatePrefix.S02AcceptedGuardHighCells
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- Count and unused-high-local facts at the accepted guard result, following
the actual installed caller and exact prefix/guard frame equalities. -/
theorem at_guard
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
    (entry site result : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (actual : Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] entry machine))
    (shape : GenericFunctionEntryPrefix.Shape entry site count)
    (countCell : result.locals[2]? = site.locals[2]?)
    (high : ∀ index, 17 ≤ index → result.locals[index]? = site.locals[index]?) :
    result.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩ ∧
    (∀ index, 17 ≤ index → index ≤ 24 → result.locals[index]? = some ⟨.dead,none⟩) := by
  obtain ⟨_reference,profile,other,actual2,_size,_location,slots,_clocks,_immediate⟩ :=
    S02SeparateDestinationInstalledLocals.ready id tag address len count input nonempty different
      returnTag returnConcrete
  have same : Storage.withCurrent #[] profile other = Storage.withCurrent #[] entry machine :=
    (EStateM.Result.ok.inj (actual2.symm.trans actual)).2
  have frameEq : profile = entry := by
    have h := congrArg (fun s : RootState => s.stack.frames[0]?) same
    exact Option.some.inj (by simpa [Storage.withCurrent] using h)
  have slotsEntry (i : Fin 25) := slots i
  rw [frameEq] at slotsEntry
  have installedCount : entry.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩ := by
    simpa using slotsEntry ⟨2,by decide⟩
  refine ⟨countCell.trans (shape.slot2.trans installedCount),?_⟩
  intro index lower upper
  have valid : index < 25 := by omega
  have dead : entry.locals[index]? = some ⟨.dead,none⟩ := by
    have h := slotsEntry ⟨index,valid⟩
    have n14 : 14 ≠ index := by omega
    have n13 : 13 ≠ index := by omega
    have n6 : 6 ≠ index := by omega
    have n0 : 0 ≠ index := by omega
    have n2 : 2 ≠ index := by omega
    have n1 : 1 ≠ index := by omega
    simpa [n14,n13,n6,n0,n2,n1] using h
  exact (high index lower).trans ((shape.keep index (by omega)).trans dead)

end
end DuplicatePrefix.S02AcceptedGuardHighCells

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02AcceptedGuardHighCells.at_guard) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved accepted guard high cells dependency {dependency}"
