import duplicate_prefix.GeneralBorrowWildcardConstructorRuntime

namespace DuplicatePrefix.S04ZeroWildcardRuntime
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
attribute [local irreducible] UniValMap.insert

/-- The literal empty protected wildcard constructor preserves the complete
runtime invariant at any offset, including offsets beyond the allocation.
There is no access to an empty range and no assumed constructor success. -/
theorem construct (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+1 ≤ 4294967295)
    (tagBound : tag.value.toNat < global.nextPointerTag.value.toNat)
    (held : global.protectedTags.contains tag = true) (offset : UInt64) :
    let actual := tree.newChild (Size.ofBytes offset) .wildcard tag
      (DedupRangeMap.new Size.ZERO ChildBorrow.fnEntryLocation) (.ReservedFrz false) true
    actual.outcome = .ok () ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global ∧
      actual.tree.locations = tree.locations ∧ actual.tree.nodes.size ≤ tree.nodes.size+1 := by
  obtain ⟨mapping,index,inserted,rows,vacant,graph,monotone,growth⟩ :=
    GeneralBorrowWildcardConstructorSlot.select tree global runtime tag fresh room (.ReservedFrz false) .None
  have actual := WildcardHitZeroConstructor.exact tree tag index mapping inserted
    (.ReservedFrz false) .None true rfl rfl rfl ChildBorrow.fnEntryLocation offset
  let node := WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None
  let result := WildcardHitZeroConstructor.installed tree mapping index tag (.ReservedFrz false) .None
  have consistent : GeneralBorrowSifaPermissionConsistency.Consistent node.defaultLocationState
      (global.protectedTags.contains tag) := by
    change GeneralBorrowSifaPermissionConsistency.Consistent ⟨.ReservedFrz false,false,.None⟩ _
    rw [held]
    exact GeneralBorrowSifaPermissionConsistency.protected_reservation false
  have profile : GeneralRangeMapState.Every
      (fun location => GeneralBorrowLocationSifaConsistency.Profile result location global.protectedTags) result.locations := by
    intro position valid
    have p := GeneralBorrowWildcardConstructorState.insert_profile tree _ global.protectedTags index node vacant
      (runtime.formed.profile position valid) consistent
    exact ⟨p.present,p.vacant⟩
  have possible : GeneralRangeMapState.Every
      (GeneralBorrowSnapshotReadRuntime.GlobalPossible result) result.locations := by
    intro position valid
    exact GeneralBorrowWildcardConstructorState.insert_possible tree _ global.protectedTags index node vacant
      (runtime.formed.profile position valid) (runtime.possible position valid) rfl
  obtain ⟨depth⟩ := runtime.formed.depth
  have coherent : GeneralRangeMapState.Every
      (fun location => GeneralBorrowExposureCardinality.LocationCoherent result location global.protectedTags) result.locations := by
    intro position valid
    exact GeneralBorrowWildcardRootCache.insert tree depth index node vacant rfl monotone _ global.protectedTags
      (runtime.coherent position valid)
  have full : DuplicatePrefixBorrowContract.RuntimeFacts result global := by
    refine ⟨⟨⟨graph,runtime.formed.well⟩,profile⟩,coherent,possible,⟨?_,runtime.below.protectors⟩⟩
    intro row member
    change row ∈ mapping.mapping at member
    rw [rows] at member
    rcases Array.mem_push.mp member with old | added
    · exact runtime.below.mapping row old
    · subst row
      exact tagBound
  dsimp only
  rw [actual]
  exact ⟨rfl,full,rfl,growth⟩

end DuplicatePrefix.S04ZeroWildcardRuntime
