import duplicate_prefix.GeneralBorrowPhysicalReadableReadProfile
import duplicate_prefix.GeneralBorrowProtectedGeneratedFramesHistory
namespace DuplicatePrefix.GeneralBorrowGeneratedFnEntryRead
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestGeneratedTagHistoryData GeneralRangeMapState GeneralBorrowForestGeneratedHiddenCache
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

def registration (id : AllocId) (state : Snapshot) (room : state.global.nextPointerTag.value < 18446744073709551615) (held : Bool) : Snapshot :=
  register id state {state.global with nextPointerTag:=TypedRetagEmpty.successorTag state.global.nextPointerTag room} state.global.nextPointerTag held

def read (id : AllocId) (state : Snapshot) (room : state.global.nextPointerTag.value < 18446744073709551615)
    (held : Bool) (parent : BorTag) (offset len : Size) (mode : ChildrenVisitMode) :=
  state.tree.performNormalAccessRange parent offset len .Read (registration id state room held).global.protectedTags mode

/-- The shadow retains the ORIGINAL counter and frame stack only for applying
an existing constructor proof. Its tree is the actual leading Read under the
already registered protector; the final macro performs allocation/registration
before this Read, not afterwards. -/
def shadow (id : AllocId) (state : Snapshot) (room : state.global.nextPointerTag.value < 18446744073709551615)
    (held : Bool) (parent : BorTag) (offset len : Size) (mode : ChildrenVisitMode) : Snapshot :=
  {state with tree:=(read id state room held parent offset len mode).tree}

theorem prepare (id : AllocId) (root : UniIndex) (state : Snapshot)
    (formed : GeneralBorrowProtectedGeneratedFramesStep.Formed id root state)
    (readable : GeneralBorrowForestGeneratedReadableHistory.Formed state)
    (room : state.global.nextPointerTag.value < 18446744073709551615) (held : Bool)
    (parent : BorTag) (anchor : UniIndex) (node : TreeNode)
    (tagged : state.tree.indexOfTag parent = some anchor) (present : state.tree.nodeAt anchor = some node)
    (offset len : Size) (mode : ChildrenVisitMode)
    (bounds : offset.bytes.toNat+len.bytes.toNat≤state.tree.locations.size.bytes.toNat) :
    (read id state room held parent offset len mode).status = .Completed ∧
    GeneralBorrowProtectedGeneratedFramesStep.Formed id root (shadow id state room held parent offset len mode) ∧
    GeneralBorrowForestGeneratedReadableHistory.Formed (shadow id state room held parent offset len mode) ∧
    (shadow id state room held parent offset len mode).tree.locations.size = state.tree.locations.size ∧
    (shadow id state room held parent offset len mode).tree = {state.tree with locations:=(read id state room held parent offset len mode).tree.locations} := by
  let registered := registration id state room held
  let actual := read id state room held parent offset len mode
  let after := shadow id state room held parent offset len mode
  have fresh := GeneralBorrowForestGeneratedTagHistoryData.fresh state formed.cache.sifa.generated
  have tags := formed.cache.sifa.generated.structural.allocator.nodeTags
  have oldReadable : Every (fun location=>GeneralBorrowPhysicalReadable.Profile state.tree location registered.global.protectedTags) state.tree.locations := by
    cases held with
    | false => exact readable.readable
    | true =>
      exact GeneralBorrowPhysicalReadableProtections.register state.tree
        {state.global with nextPointerTag:=TypedRetagEmpty.successorTag state.global.nextPointerTag room}
        {} id state.global.nextPointerTag .StrongProtector fresh tags readable.readable
  have oldSifa : Every (fun location=>GeneralBorrowLocationSifaConsistency.Profile state.tree location registered.global.protectedTags) state.tree.locations := by
    cases held with
    | false => exact formed.cache.sifa.profile
    | true =>
      exact GeneralBorrowSifaProtectionProfile.register state.tree
        {state.global with nextPointerTag:=TypedRetagEmpty.successorTag state.global.nextPointerTag room}
        {} id state.global.nextPointerTag .StrongProtector fresh tags formed.cache.sifa.profile
  obtain ⟨depth⟩ := formed.cache.sifa.generated.structural.depth
  have done := GeneralBorrowPhysicalReadableReadProfile.ranged state.tree registered.global.protectedTags parent anchor root offset len mode
    formed.cache.sifa.generated.structural.fits depth formed.cache.sifa.generated.structural.children node present formed.roots
    formed.cache.sifa.generated.structural.covered tagged formed.cache.sifa.generated.structural.well
    (fun location=>Classical.choice (formed.cache.sifa.generated.structural.forest location registered.global.protectedTags)) formed.cache.empty.hidden
    (fun position valid=>⟨oldReadable position valid,oldSifa position valid,formed.cache.empty.zero position valid⟩) bounds
  have frame : actual.tree = {state.tree with locations:=actual.tree.locations} := GeneralBorrowFreshReadFrame.frame state.tree (.concrete parent) offset len .Read registered.global.protectedTags mode
  have structural :=  GeneralBorrowStructuralHistoryFrames.access state.tree formed.cache.sifa.generated.structural (.concrete parent) offset len .Read registered.global.protectedTags mode bounds
  have highwater : GeneralBorrowForestTagHighWater.Below actual.tree state.global.protectedTags state.global.nextPointerTag := by
    rw [frame]
    exact GeneralBorrowForestTagHighWaterHistory.locations _ _ _ _ formed.cache.sifa.generated.below
  have generated : Invariant after := ⟨structural.1,highwater⟩
  have absent : state.tree.indexOfTag state.global.nextPointerTag = none := by
    simp only [BorrowTree.indexOfTag,UniKeyMap.get,GeneralBorrowTagMap.fresh_find _ _ fresh,Option.map_none]
  have nodesEq : actual.tree.nodes=state.tree.nodes := done.2.2.2.2.1
  have sameHeld : ∀ query current,actual.tree.nodeAt query=some current →
      registered.global.protectedTags.contains current.tag=state.global.protectedTags.contains current.tag := by
    intro query current found
    have old : state.tree.nodeAt query=some current := by
      change actual.tree.nodes.get query=some current at found
      rw [nodesEq] at found
      exact found
    have different : current.tag≠state.global.nextPointerTag := by
      intro same
      have lookup : state.tree.indexOfTag current.tag = some query := tags query current old
      rw [same,absent] at lookup
      cases lookup
    cases held with
    | false => rfl
    | true => exact congrArg Option.isSome (GeneralBorrowProtectorCacheMap.insert_other _ _ _ .StrongProtector different)
  have sifa : GeneralBorrowForestGeneratedSifaHistory.Formed after := by
    refine ⟨generated,?_⟩
    intro position valid
    have good := (done.2.1 position valid).2.1
    refine ⟨?_,good.vacant⟩
    intro query current found
    have consistent:=good.present query current found
    rw [sameHeld query current found] at consistent
    exact consistent
  have nextReadable : GeneralBorrowForestGeneratedReadableHistory.Formed after := by
    refine ⟨sifa,?_⟩
    intro position valid
    have good := (done.2.1 position valid).1
    refine ⟨?_,good.vacant⟩
    intro query current found
    have value:=good.present query current found
    rw [sameHeld query current found] at value
    exact value
  have hidden : Hidden actual.tree := by rw [frame];exact formed.cache.empty.hidden
  have frames : GeneralBorrowPhysicalReadableLifo.Frames id actual.tree state.global state.frames := by
    rw [frame]
    exact ⟨formed.frames.singleton,formed.frames.distinct,formed.frames.held,formed.frames.nodes⟩
  have roots : actual.tree.roots=#[root] := by rw [frame];exact formed.roots
  exact ⟨done.1,⟨⟨sifa,hidden,fun position valid=>(done.2.1 position valid).2.2⟩,frames,roots⟩,nextReadable,done.2.2.2.1,frame⟩
end DuplicatePrefix.GeneralBorrowGeneratedFnEntryRead
