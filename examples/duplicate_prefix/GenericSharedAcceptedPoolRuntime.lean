import duplicate_prefix.GenericSharedAcceptedForm
import duplicate_prefix.GenericSharedLenAcceptedStrong
import duplicate_prefix.GeneralBorrowFreshSharedPoolReleasedMetadata
namespace DuplicatePrefix.GenericSharedAcceptedPoolRuntime
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open GenericSharedAcceptedStages
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

private theorem metadata_release (s : GenericSharedAcceptedInput.PoolInput) (tree : BorrowTree)
    (equation : ((child_pool s).releaseProtector (one_base s.toBase).global.nextPointerTag
      (held_base s.toBase).global.protectedTags).tree = tree) :
    Nonempty (GeneralBorrowFreshSharedPoolReleasedMetadata.Output s.entry.allocation.extra tree
      s.tracker.global.nextPointerTag (one_base s.toBase).global.nextPointerTag
      (GeneralBorrowFreshSharedSequence.index s.first) (GeneralBorrowFreshSharedSequence.index (second_pool s))) := by
  have facts := GeneralBorrowFreshSharedPoolReleasedMetadata.build s.entry.allocation.extra s.tracker.global.protectedTags
    s.target s.tracker.global.nextPointerTag (one_base s.toBase).global.nextPointerTag s.offset s.len s.first
    s.pool s.accounting (by change s.entry.allocation.extra.nodes.size+1 ≤ 4294967295;have room := s.nodeRoom;omega) s.tagFresh s.protectorFresh s.different s.cleanVacant s.owned
  have result : Nonempty (GeneralBorrowFreshSharedPoolReleasedMetadata.Output s.entry.allocation.extra
      ((child_pool s).releaseProtector (one_base s.toBase).global.nextPointerTag
        (held_base s.toBase).global.protectedTags).tree
      s.tracker.global.nextPointerTag (one_base s.toBase).global.nextPointerTag
      (GeneralBorrowFreshSharedSequence.index s.first) (GeneralBorrowFreshSharedSequence.index (second_pool s))) := facts.2
  rw [equation] at result
  exact result

/-- Genuine shared/len/release/accepted guard from INITIAL arbitrary-pool data;
all following suffix data and operation success are derived internally. -/
theorem prepare (s : GenericSharedAcceptedInput.PoolInput) :
    ∃ ready : GenericAsMutDefaultPoolToCall.Input,
      PreparedContracts.actualConfig ready.common.base.data.start.options () (ready.common.base.data.start.remaining+1) ready.common.base.data.start.span =
        PreparedContracts.actualConfig s.options () (s.remaining+1) s.span ∧ ready.common.base.data.start.limits = s.limits ∧
      SuccessfulTrace.Trace (PreparedContracts.actualConfig s.options () (s.remaining+1) s.span) s.limits
        (Storage.withCurrent #[] s.frame s.machine)
        (Storage.withCurrent #[] ready.common.base.caller ready.common.base.data.start.machine) := by
  obtain ⟨frame,machine,tree,tracker,previous,runtime,track,active,well,capacity,treeFrame,releaseFacts,frameFacts,memory⟩ :=
    GenericSharedLenAcceptedStrong.executes_full_data
    s.options s.limits s.remaining s.budget s.dispatchFuel s.span s.precise s.implicitWrites s.debug
    s.cmp s.dynamicFuel s.validityFuel s.dynamicEq s.validationEq s.id s.entry s.base s.offset
    s.len s.positive s.nonnull s.signedFits s.frame s.machine s.tracker s.enabled s.defaultMode
    s.fresh s.target s.first s.capacity s.owned (second_pool s) (second_pool_parent s)
    (by change s.entry.allocation.extra.nodes.size+1 ≤ 4294967295;have room := s.nodeRoom;omega) s.fresh2 s.different s.v1 s.v11 s.v12 s.sourceLive s.sourceCached s.lenLive
    s.lenUncached s.exprLive s.exprUncached s.body s.identity s.callee s.location s.frameRace s.race
    s.ghost s.shallow s.cached s.present s.metadata s.notConstructed s.backend s.thread s.active
    s.threadCache s.unchecked s.noGc s.fixed s.source s.rangePositive s.exprUnheld s.size s.count
    s.countPositive s.within s.all s.live0 s.cache0 s.live7 s.cache7 s.live8 s.cache8
    s.live9 s.cache9 s.live10 s.cache10 s.live13 s.cache13 s.dead15 s.cache15 s.dead16
    s.cache16 s.initialActive
  rcases previous with ⟨prefixTrace,location,tracked,present,body,identity,callee,extra,size,slot1,slot2,slot15,slot16,immediate,owned⟩
  have endedEq : tracker = ended_base s.toBase := releaseFacts.2
  let boundary : GenericSharedAcceptedForm.Boundary s.toBase frame machine tree := {
    location := location, tracked := by rw [←endedEq];exact tracked
    present := present, body := body, identity := identity, callee := callee, extra := extra, size := size
    slot1 := slot1, slot2 := slot2, slot15 := slot15, slot16 := slot16, immediate := immediate
    owned := by rw [←endedEq];exact owned
    runtime := runtime, track := track, active := active, well := well, capacity := capacity, facts := frameFacts, memory := memory }
  have released : ((child_pool s).releaseProtector (one_base s.toBase).global.nextPointerTag
      (held_base s.toBase).global.protectedTags).tree = tree :=
    congrArg BorrowTree.ProtectorReleaseResult.tree releaseFacts.1
  obtain ⟨metadata⟩ := metadata_release s tree released
  obtain ⟨ready,frameEq,machineEq,configEq,limitsEq⟩ := GenericSharedAcceptedForm.pool_form s frame machine tree boundary metadata
  rw [←frameEq,←machineEq] at prefixTrace
  exact ⟨ready,configEq,limitsEq,prefixTrace⟩
end DuplicatePrefix.GenericSharedAcceptedPoolRuntime
