import duplicate_prefix.S04ZeroChildCallbacks
import duplicate_prefix.GeneralBorrowStructuralHistoryMixedConcrete
import duplicate_prefix.GeneralBorrowProtectedConstructorPossible
import duplicate_prefix.GeneralBorrowZeroProtectedDefaultExposureCache

namespace DuplicatePrefix.S04ZeroConcreteRuntime
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralRangeMapState
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
attribute [local irreducible] UniValMap.insert

/-- The literal empty protected concrete constructor preserves the complete
runtime invariant for append and vacant-slot reuse. The zero inside map has no
segments, so the offset needs no allocation bound. Constructor completion and
the resulting runtime facts are conclusions from current input metadata. -/
theorem construct (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (tag : BorTag) (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (room : tree.nodes.size+1 ≤ 4294967295)
    (tagBound : tag.value.toNat < global.nextPointerTag.value.toNat)
    (_held : global.protectedTags.contains tag = true) (offset : UInt64) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) tag
      (DedupRangeMap.new (Size.ofBytes 0) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    actual.outcome = .ok () ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global ∧
      actual.tree.locations.size = tree.locations.size ∧ actual.tree.nodes.size ≤ tree.nodes.size+1 := by
  have accounting := runtime.formed.allocator.accounting
  have fits : tree.tagMapping.mapping.size ≤ 4294967295 := by
    unfold GeneralBorrowFreshStagePool.Accounting at accounting
    omega
  let input := ConcreteEmptyPoolEntry.factory tree parentTag tag parent parentNode
    (Classical.choice runtime.formed.depth) tagged present fresh runtime.formed.allocator.pool
    accounting fits (DuplicatePrefixBorrowContract.vacant_clean runtime)
  have bounded : GeneralBorrowStructuralHistoryMixedConcrete.Bounded
      (DedupRangeMap.new (Size.ofBytes 0) GeneralBorrowFreshChild.inside)
      (Size.ofBytes offset) tree.locations.size := by
    intro segment member
    simp [DedupRangeMap.iterAll,DedupRangeMap.new,Size.ofBytes] at member
  have structural := GeneralBorrowStructuralHistoryMixedConcrete.preserves tree runtime.formed.toState
    parentTag parent parentNode tagged present tag fresh room (.ReservedFrz false) .None true
    rfl rfl rfl (Size.ofBytes offset)
    (DedupRangeMap.new (Size.ofBytes 0) GeneralBorrowFreshChild.inside) bounded
  rw [input.child offset] at structural
  have stageProfile : Every
      (fun location => GeneralBorrowLocationSifaConsistency.Profile input.stage location global.protectedTags)
      input.stage.locations := by
    intro position valid
    exact S04ZeroChildCallbacks.stage_profile tree parentTag tag input _ global.protectedTags
      (runtime.formed.profile position valid)
  have profile := GeneralBorrowSifaProfileTransport.sifa input.stage global.protectedTags input.parent .None stageProfile
  have stagePossible : Every (GeneralBorrowSnapshotReadRuntime.GlobalPossible input.stage) input.stage.locations := by
    intro position valid
    exact GeneralBorrowProtectedConstructorPossible.attach tree _ global.protectedTags input.index input.parent
      input.parentNode tag input.vacant input.present (runtime.formed.profile position valid) (runtime.possible position valid)
  have possible := GeneralBorrowProtectedConstructorPossible.sifa input.stage input.parent .None stagePossible
  have stageSize : tree.nodes.size ≤ input.stage.nodes.size := by
    rw [ConcreteEmptyPoolEntryNext.stage_size input]
    omega
  have stageCoherent : Every
      (fun location => GeneralBorrowExposureCardinality.LocationCoherent input.stage location global.protectedTags)
      input.stage.locations := by
    intro position valid
    exact GeneralBorrowExposureChildAttach.attach tree input.depth input.index input.parent input.parentNode
      (GeneralBorrowFreshChild.child tag input.parent) input.vacant input.present rfl stageSize _ global.protectedTags
      (runtime.coherent position valid)
  have coherent := GeneralBorrowExposureSifaTransport.sifa input.stage global.protectedTags
    (S04ZeroChildCallbacks.stage_depth tree parentTag tag input) input.parent .None stageCoherent
  have full : DuplicatePrefixBorrowContract.RuntimeFacts input.after global := by
    refine ⟨⟨structural.1,profile⟩,coherent,possible,⟨?_,runtime.below.protectors⟩⟩
    intro row member
    rw [input.mapping_after] at member
    change row ∈ tree.tagMapping.mapping.push (tag,input.index) at member
    rcases Array.mem_push.mp member with old | added
    · exact runtime.below.mapping row old
    · subst row
      exact tagBound
  dsimp only
  rw [input.child offset]
  exact ⟨rfl,full,structural.2.1,structural.2.2⟩

end DuplicatePrefix.S04ZeroConcreteRuntime
