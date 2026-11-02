import duplicate_prefix.GlobalRelocationConversion
import duplicate_prefix.GlobalDataOnlyAdjust

/-! Managed global materialization with a genuine singleton relocation. Bytes
and concrete provenance come from the real relocation callback; canonical tree
and extras initialization follow conversion in their actual source order. -/
namespace DuplicatePrefix.GlobalRelocationAdjust
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem adjust_singleton {K U P : Type} [DecidableEq K] (choices : ExecutionChoices.Access (MachineAddress.State K U))
    (hooks : MachineAddress.Hooks K U)
    (externStatic : Miri.MIR.DefId → MachineAddress.M K U (Pointer Provenance))
    (extras : MemoryExtras.Hooks K (PointerMachine.User U) P)
    (allocationId : AllocId) (allocationRoot : BorTag)
    (before : MachineAddress.State K U) (tracker : MachineHooks.BorrowState)
    (provenance : CtfeProvenance) (base : UInt64) (root : BorTag)
    (targetSource source : Allocation CtfeProvenance Unit) (layout : TargetDataLayout)
    (descriptor : before.memory.findGlobal? provenance.allocId = some
      ⟨provenance.allocId,.memory,targetSource.byteSize,targetSource.align,targetSource.mutability,some (.memory targetSource)⟩)
    (enabled : before.borrowTracker = some tracker)
    (rootCached : tracker.global.rootTag? provenance.allocId = some root)
    (addressCached : before.user.addresses.baseAddr.find? (fun row => row.allocId == provenance.allocId) =
      some ⟨provenance.allocId,base⟩)
    (arithmetic : hooks.arithmetic = ⟨Size.ofBytes 8⟩) (width : layout.pointerWidth = .w64)
    (rawBytes : AllocationCopy.snapshot source = #[0,0,0,0,0,0,0,0])
    (allocationRootCached : tracker.global.rootTag? allocationId = some allocationRoot)
    (race : before.dataRace = none)
    (noExtras : ((extras.get before.user).allocations.any (fun row => row.1 == allocationId)) = false)
    (relocation : source.provenanceMap.ptrs = #[(Size.ZERO,provenance)])
    (noFragments : source.provenanceMap.byteFragments = none) :
    ∃ converted : Allocation Provenance Unit, ∃ encoded : Array UInt8,
      GlobalRelocationConversion.Attributes source converted ∧
      target_bytes layout (Size.ofBytes 8) (BitVec.ofNat 128 base.toNat) = .ok encoded ∧
      encoded.size = 8 ∧ AllocationCopy.snapshot converted = encoded ∧
      converted.provenanceMap.ptrs = #[(Size.ZERO,Provenance.concrete provenance.allocId root)] ∧
      converted.provenanceMap.byteFragments = none ∧
      GlobalAllocationMachine.adjust layout extras
        (GlobalDataOnlyAdjust.leaves (PointerSource.globalRootPointer choices hooks externStatic)) allocationId source before =
        .ok (.owned (converted.mapExtra (fun _ => BorrowTree.new allocationRoot source.byteSize)))
          (MemoryExtras.putAllocation extras before allocationId ⟨none,#[]⟩) := by
  obtain ⟨converted,encoded,conversion,facts,encoding,encodedSize,bytes,ptrs,fragments⟩ :=
    GlobalRelocationConversion.singleton_zero choices hooks externStatic before tracker provenance base root targetSource source
      layout descriptor enabled rootCached addressCached arithmetic width rawBytes relocation noFragments
  refine ⟨converted,encoded,facts,encoding,encodedSize,bytes,ptrs,fragments,?_⟩
  have inspect : source.inspectWithUninitAndPtrOutsideInterpreter 0 source.len =
      .ok (AllocationCopy.snapshot source) := by
    cases source
    simp [AllocationCopy.snapshot,Allocation.inspectWithUninitAndPtrOutsideInterpreter,Allocation.len,
      pure,Pure.pure,Except.pure,Except.toOption]
  have init := GlobalDataOnlyExtra.init_extra extras before tracker allocationId allocationRoot source.byteSize source.align
    enabled allocationRootCached race noExtras
  simp only [GlobalAllocationMachine.adjust,GlobalDataOnlyAdjust.leaves,GlobalAllocationMachine.managedBytes,
    inspect,conversion,facts.size,facts.align,GlobalAllocationMachine.init,
    get,getThe,MonadStateOf.get,EStateM.get,set,EStateM.set,
    bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
    tryCatch,tryCatchThe,MonadExceptOf.tryCatch,EStateM.tryCatch]
  simp only [pure,Pure.pure,EStateM.pure] at init
  rw [init]

end DuplicatePrefix.GlobalRelocationAdjust

open Lean Elab Command in
run_cmd do
  for dependency in (←collectAxioms ``DuplicatePrefix.GlobalRelocationAdjust.adjust_singleton) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved real relocated global adjustment dependency {dependency}"
