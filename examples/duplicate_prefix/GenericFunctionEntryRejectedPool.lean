import duplicate_prefix.GenericFunctionEntryRejected
import duplicate_prefix.GenericFunctionEntryPoolSharedData
import duplicate_prefix.GenericSharedRejectedPoolInput
namespace DuplicatePrefix.GenericFunctionEntryRejectedPool
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext GenericFunctionEntryState GenericFunctionEntryRejected
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

set_option autoImplicit false in
/-- Original caller resources with an arbitrary coherent allocator pool and
separate cleanliness of all vacant permission slots. Four conservative node
places cover ROOT, shared-expression, shared-helper and default staging. -/
structure Initial extends GenericFunctionEntryRejected.InitialBase where
  pool : GeneralBorrowFreshAllocatorInvariant.Pool entry.allocation.extra.nodes entry.allocation.extra.tagMapping.deassigned
  accounting : GeneralBorrowFreshStagePool.Accounting entry.allocation.extra
  nodeRoom : entry.allocation.extra.nodes.size+4 ≤ 4294967295
  cleanVacant : ∀ query, entry.allocation.extra.nodes.get query = none → GeneralBorrowFreshFutureClean.Clean entry.allocation.extra query

/-- Genuine ROOT call and nonzero prefix, constructing shared-pool input
internally from original data. No intermediate Data or operation success is supplied. -/
theorem prepare (s : Initial) :
    ∃ input : GenericSharedRejectedPoolInput.Input,
      input.options=s.options ∧ input.limits=s.limits ∧ input.remaining=s.remaining ∧ input.span=s.span ∧
      input.id=s.id ∧ input.count=s.count ∧ input.place=s.place ∧
      ∃ installed,
        Call.initStackFrame (ExecutionMachine.callHooks (config s.options (s.remaining+1) s.span) s.limits) ()
          RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
          #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
            (Pointer.new (.concrete s.id s.parentTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm,
            ActualReferenceMetadata.reference⟩,.Copy (EmptyRootArguments.second s.count)] false (.memory s.place) (.stop true)
          ⟨⟨#[]⟩,s.before⟩ = .ok () installed ∧
        SuccessfulTrace.Trace (config s.options (s.remaining+1) s.span) s.limits installed
          (Storage.withCurrent #[] input.frame input.machine) ∧ installed.stack.frames.size=1 := by
  classical
  have bounds : s.offset.toNat+s.len.toNat ≤ s.entry.allocation.extra.locations.size.bytes.toNat := by rw [s.capacity];exact s.bounds
  have nonzero := UInt64.pos_iff_ne_zero.mp s.positive
  have oldDifferent : s.tracker.global.nextPointerTag ≠ (seed s.tracker s.fresh s.slotFresh).global.nextPointerTag := by
    have growth0 := GenericFunctionEntryNumerics.successor_value s.tracker.global.nextPointerTag s.fresh
    have growth1 := GenericFunctionEntryNumerics.successor_value (next s.tracker s.fresh).global.nextPointerTag s.slotFresh
    change (next s.tracker s.fresh).global.nextPointerTag.value.toNat = s.tracker.global.nextPointerTag.value.toNat+1 at growth0
    change (seed s.tracker s.fresh s.slotFresh).global.nextPointerTag.value.toNat = (next s.tracker s.fresh).global.nextPointerTag.value.toNat+1 at growth1
    intro same
    have equal := congrArg (fun tag : BorTag => tag.value.toNat) same
    omega
  let supplied := GenericFunctionEntryPoolSharedData.first s.entry.allocation.extra s.tracker s.parentTag s.offset s.len nonzero s.data bounds
    s.pool s.accounting (by have h:=s.nodeRoom;omega) s.cleanVacant (seed s.tracker s.fresh s.slotFresh).global.nextPointerTag
    (s.futureMap ⟨0,by decide⟩) (s.futureNodes ⟨0,by decide⟩) oldDifferent
  obtain ⟨common,options,limits,remaining,span,id,count,place,treeEq,installed,call,trace,depth⟩ :=
    GenericFunctionEntryRejected.prepare_base s.toInitialBase supplied.val supplied.property.1 supplied.property.2.1
  have allocator := GenericFunctionEntryPool.allocator s.entry.allocation.extra s.tracker s.parentTag s.offset s.len nonzero s.data bounds s.pool s.accounting
  let input : GenericSharedRejectedPoolInput.Input := {
    toBase := common
    pool := by rw [treeEq];exact allocator.1
    accounting := by rw [treeEq];exact allocator.2.1
    cleanVacant := by
      intro query vacant
      rw [treeEq] at vacant ⊢
      exact (GenericFunctionEntryPoolSharedData.vacant_clean s.entry.allocation.extra s.tracker s.parentTag s.offset s.len
        nonzero s.data bounds s.pool s.accounting s.cleanVacant query vacant).2
    nodeRoom := by rw [treeEq];have size:=allocator.2.2.1;have room:=s.nodeRoom;omega }
  exact ⟨input,options,limits,remaining,span,id,count,place,installed,call,trace,depth⟩
end DuplicatePrefix.GenericFunctionEntryRejectedPool
