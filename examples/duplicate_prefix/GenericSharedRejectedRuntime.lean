import duplicate_prefix.GenericSharedRejectedForm
import duplicate_prefix.GenericSharedLenAcceptedStrong
namespace DuplicatePrefix.GenericSharedRejectedRuntime
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open GenericSharedRejectedStages
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
-- Keep child trees symbolic while comparing record-update frame equations.
attribute [local irreducible] GeneralBorrowFreshSharedSequence.child

private theorem staged (s : GenericSharedRejectedInput.Input) :
    Nonempty (GeneralBorrowFreshSharedReleasedMetadata.Output s.entry.allocation.extra (child s) s.target s.first.parentNode s.first.parentTag) :=
  GeneralBorrowFreshSharedReleasedMetadata.stages s.entry.allocation.extra s.tracker.global.protectedTags s.target
    s.tracker.global.nextPointerTag (one s).global.nextPointerTag s.offset s.len s.first s.noFree s.room
    s.tagFresh s.protectorFresh s.different s.cleanFuture s.owned

set_option backward.isDefEq.respectTransparency true in
/-- Shared runtime composition boundary. Public allocator-specific wrappers
construct second and metadata from their original data. -/
theorem prepare_data (s : GenericSharedRejectedInput.Base)
    (secondData : GeneralBorrowFreshSharedSequence.Data
      (GeneralBorrowFreshSharedSequence.child s.first s.tracker.global.protectedTags false).tree
      (one_base s).global.nextPointerTag (GeneralBorrowFreshSharedSequence.index s.first) s.offset s.len)
    (parentTag : secondData.parentTag = s.tracker.global.nextPointerTag)
    (room : s.entry.allocation.extra.nodes.data.size+1 ≤ 4294967295)
    (metadata : ∀ tree,
      (GeneralBorrowFreshSharedSequence.child secondData s.tracker.global.protectedTags true).tree.releaseProtector
        (one_base s).global.nextPointerTag
        (GeneralBorrowFreshSharedSequence.registered s.tracker.global.protectedTags (one_base s).global.nextPointerTag true) = ⟨tree,.Released⟩ →
      tree = {(GeneralBorrowFreshSharedSequence.child secondData s.tracker.global.protectedTags true).tree with locations:=tree.locations} →
      Nonempty (GenericSharedRejectedForm.Metadata s tree)) :
    ∃ ready : GenericRootRejectedPhysical.Input,
      PreparedContracts.actualConfig ready.options () (ready.remaining+1) ready.span =
        PreparedContracts.actualConfig s.options () (s.remaining+1) s.span ∧ ready.limits=s.limits ∧
      SuccessfulTrace.Trace (PreparedContracts.actualConfig s.options () (s.remaining+1) s.span) s.limits
        (Storage.withCurrent #[] s.frame s.machine) (Storage.withCurrent #[] ready.before ready.machine) := by
  obtain ⟨frame,machine,tree,tracker,previous,releaseFacts,runtime,frameFacts,memory,active,well,capacity,treeFrame⟩ :=
    GenericSharedLenAcceptedStrong.before_guard_full_data
      s.options s.limits s.remaining s.budget s.dispatchFuel s.span s.precise s.implicitWrites s.debug s.cmp
      s.dynamicFuel s.validityFuel s.dynamicEq s.validationEq s.id s.entry s.base s.offset s.len s.positive s.nonnull s.signedFits
      s.frame s.machine s.tracker s.enabled s.defaultMode s.fresh s.target s.first s.capacity s.owned secondData parentTag room s.fresh2
      s.different s.v1 s.v11 s.v12 s.sourceLive s.sourceCached s.lenLive s.lenUncached
      s.exprLive s.exprUncached s.body s.identity s.callee s.location s.frameRace s.race s.ghost s.shallow s.cached s.present
      s.metadata s.notConstructed s.backend s.thread s.active s.threadCache s.unchecked s.noGc s.fixed s.source s.rangePositive s.exprUnheld
      s.size s.all s.initialActive
  rcases previous with ⟨trace,tracked,present,owned⟩
  have endedEq : tracker = ended_base s := releaseFacts.2
  let boundary : GenericSharedRejectedForm.Boundary s frame machine tree := {
    tracked := by rw [←endedEq];exact tracked
    present := present,owned := by rw [←endedEq];exact owned
    runtime := runtime,facts := frameFacts,active := active,well := well,memory := memory }
  have releasedEq : (GeneralBorrowFreshSharedSequence.child secondData s.tracker.global.protectedTags true).tree.releaseProtector
      (one_base s).global.nextPointerTag
      (GeneralBorrowFreshSharedSequence.registered s.tracker.global.protectedTags (one_base s).global.nextPointerTag true) = ⟨tree,.Released⟩ := releaseFacts.1
  have frameEq : tree = {(GeneralBorrowFreshSharedSequence.child secondData s.tracker.global.protectedTags true).tree with locations:=tree.locations} := treeFrame
  obtain ⟨derivedMetadata⟩ := metadata tree releasedEq frameEq
  obtain ⟨ready,frameEq,machineEq,configEq,limitsEq⟩ :=
    GenericSharedRejectedForm.form_data s frame machine tree boundary derivedMetadata
  refine ⟨ready,configEq,limitsEq,?_⟩
  rw [frameEq,machineEq]
  exact trace

/-- Compatibility wrapper: the original append allocator forms second and all
post-len metadata internally, then uses the common actual runtime proof. -/
theorem prepare (s : GenericSharedRejectedInput.Input) :
    ∃ ready : GenericRootRejectedPhysical.Input,
      PreparedContracts.actualConfig ready.options () (ready.remaining+1) ready.span =
        PreparedContracts.actualConfig s.options () (s.remaining+1) s.span ∧ ready.limits=s.limits ∧
      SuccessfulTrace.Trace (PreparedContracts.actualConfig s.options () (s.remaining+1) s.span) s.limits
        (Storage.withCurrent #[] s.frame s.machine) (Storage.withCurrent #[] ready.before ready.machine) := by
  apply prepare_data s (second s) (by rfl)
    (by
      have aligned : s.entry.allocation.extra.tagMapping.mapping.size=s.entry.allocation.extra.nodes.data.size := by
        cases s.first.slot with
        | append empty aligned fits => exact aligned
        | reuse index available bounded vacant slack => rw [s.noFree] at available;cases available
      rw [←aligned]
      exact s.room)
  intro tree releaseEq frame
  obtain ⟨initialMetadata⟩ := staged s
  obtain ⟨metadata⟩ := GeneralBorrowFreshSharedReleasedMetadata.of_frame s.entry.allocation.extra (child s) tree
    s.target s.first.parentNode s.first.parentTag initialMetadata frame
  exact ⟨⟨metadata.certificates,metadata.roots,metadata.nodeFits,metadata.node,metadata.tagPresent⟩⟩
end
end DuplicatePrefix.GenericSharedRejectedRuntime
