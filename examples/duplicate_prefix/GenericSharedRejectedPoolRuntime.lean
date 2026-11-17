import duplicate_prefix.GenericSharedRejectedPoolInput
import duplicate_prefix.GenericSharedRejectedRuntime
import duplicate_prefix.GenericSharedLenAcceptedStrong
import duplicate_prefix.GeneralBorrowFreshSharedPoolReleasedMetadata
namespace DuplicatePrefix.GenericSharedRejectedPoolRuntime
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open GenericSharedRejectedStages
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
attribute [local irreducible] GeneralBorrowFreshSharedSequence.child

def second (s : GenericSharedRejectedPoolInput.Input) :=
  (GeneralBorrowFreshSharedNextPool.next s.entry.allocation.extra s.tracker.global.protectedTags s.target
    s.tracker.global.nextPointerTag (one_base s).global.nextPointerTag s.offset s.len s.first s.pool s.accounting
    (by have room:=s.nodeRoom;omega) s.tagFresh s.protectorFresh s.different s.cleanVacant s.owned).val

def child (s : GenericSharedRejectedPoolInput.Input) :=
  (GeneralBorrowFreshSharedSequence.child (second s) s.tracker.global.protectedTags true).tree

private theorem metadata_data (s : GenericSharedRejectedInput.Base) (tree : BorrowTree)
    (childIndex : UniIndex)
    (metadata : GeneralBorrowFreshSharedPoolReleasedMetadata.Output s.entry.allocation.extra tree
      s.tracker.global.nextPointerTag (one_base s).global.nextPointerTag
      (GeneralBorrowFreshSharedSequence.index s.first) childIndex) :
    Nonempty (GenericSharedRejectedForm.Metadata s tree) := by
  have differentFirst := GeneralBorrowFreshSharedStageLookup.fresh_not_present s.entry.allocation.extra
    s.tracker.global.nextPointerTag s.first.parentTag s.target s.first.tagFresh s.first.parentTagPresent
  have differentSecond := GeneralBorrowFreshSharedStageLookup.fresh_not_present s.entry.allocation.extra
    (one_base s).global.nextPointerTag s.first.parentTag s.target s.tagFresh s.first.parentTagPresent
  exact ⟨⟨metadata.certificates,metadata.roots,metadata.nodeFits,
    metadata.oldNode s.target s.first.parentNode s.first.parentPresent,
    (metadata.oldLookup s.first.parentTag differentFirst differentSecond).trans s.first.parentTagPresent⟩⟩

/-- Execute both real shared stages and actual len/helper return, then rejected
cleanup/physical-return input formation, from initial arbitrary-pool data. -/
theorem prepare (s : GenericSharedRejectedPoolInput.Input) :
    ∃ ready : GenericRootRejectedPhysical.Input,
      PreparedContracts.actualConfig ready.options () (ready.remaining+1) ready.span =
        PreparedContracts.actualConfig s.options () (s.remaining+1) s.span ∧ ready.limits=s.limits ∧
      SuccessfulTrace.Trace (PreparedContracts.actualConfig s.options () (s.remaining+1) s.span) s.limits
        (Storage.withCurrent #[] s.frame s.machine) (Storage.withCurrent #[] ready.before ready.machine) := by
  apply GenericSharedRejectedRuntime.prepare_data s (second s) (by rfl)
    (by have room:=s.nodeRoom;change s.entry.allocation.extra.nodes.data.size+3≤4294967295 at room;omega)
  intro tree releaseEq frame
  have derived := GeneralBorrowFreshSharedPoolReleasedMetadata.build s.entry.allocation.extra
    s.tracker.global.protectedTags s.target s.tracker.global.nextPointerTag (one_base s).global.nextPointerTag
    s.offset s.len s.first s.pool s.accounting (by have room:=s.nodeRoom;omega)
    s.tagFresh s.protectorFresh s.different s.cleanVacant s.owned
  change _ ∧ Nonempty (GeneralBorrowFreshSharedPoolReleasedMetadata.Output s.entry.allocation.extra
    ((GeneralBorrowFreshSharedSequence.child (second s) s.tracker.global.protectedTags true).tree.releaseProtector
      (one_base s).global.nextPointerTag
      (GeneralBorrowFreshSharedSequence.registered s.tracker.global.protectedTags (one_base s).global.nextPointerTag true)).tree
    s.tracker.global.nextPointerTag (one_base s).global.nextPointerTag
    (GeneralBorrowFreshSharedSequence.index s.first) (GeneralBorrowFreshSharedSequence.index (second s))) at derived
  rw [releaseEq] at derived
  obtain ⟨releasedMetadata⟩ := derived.2
  exact metadata_data s tree (GeneralBorrowFreshSharedSequence.index (second s)) releasedMetadata
end
end DuplicatePrefix.GenericSharedRejectedPoolRuntime
