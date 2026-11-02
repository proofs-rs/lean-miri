import duplicate_prefix.GeneralBorrowForestFnEntry
import duplicate_prefix.GeneralBorrowForestMutableSlice
import duplicate_prefix.GeneralBorrowProtectorCacheMap
namespace DuplicatePrefix.GeneralBorrowProtectedRetainedNestedWrite
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestMutableAccess (Data)
open GeneralBorrowForestAccessData (Context)
open GeneralBorrowFreshReborrowStages (Slot)
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- A retained Strong-protected parent remains protected during a nested real
FnEntry reservation and the new protected child's Write. Initial permissions
and graph metadata are raw source invariants, never operation-success fields.
This is a BorrowTree protocol component, not a whole-MIR invocation. -/
theorem construct_write (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (parentTag : BorTag) (parent primary : UniIndex) (extras : List UniIndex) (offset len : UInt64)
    (mode : ChildrenVisitMode) (context : Context tree parent primary extras)
    (covered : GeneralBorrowGraph.RootsCover tree) (parentTagPresent : tree.indexOfTag parentTag = some parent)
    (parentHeld : global.protectedTags.get parentTag = some .StrongProtector)
    (tagRoom : global.nextPointerTag.value < 18446744073709551615)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping global.nextPointerTag)
    (unheld : global.protectedTags.get global.nextPointerTag = none)
    (nodeTags : ∀ index node, tree.nodeAt index = some node → tree.indexOfTag node.tag = some index)
    (slot : Slot tree context.depth parent) (fits : tree.nodes.data.size ≤ 4294967296)
    (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (before : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (Data tree location global.protectedTags parent primary extras))
      offset (offset+len) tree.locations) :
    ∃ output, GeneralBorrowForestFnEntry.operation tree global frame allocation parentTag offset len mode = .ok output ∧
      output.access.status = .Completed ∧ output.child.outcome = .ok () ∧
      output.global.protectedTags.get parentTag = some .StrongProtector ∧
      output.global.protectedTags.get output.tag = some .StrongProtector ∧
      output.frame.protectedTags = frame.protectedTags.push (allocation,output.tag) ∧
      let written := output.child.tree.performBorrowAccessRange (.concrete output.tag)
        (Size.ofBytes offset) (Size.ofBytes len) .Write output.global.protectedTags mode
      written.status = .Completed ∧ written.tree.locations.WellFormed ∧
      written.tree.locations.size = tree.locations.size ∧
      GeneralRangeMapOrigins.OwnedOn
        (fun location => Nonempty (Data written.tree location output.global.protectedTags
          (GeneralBorrowFreshMetadataChildMutableSlot.index slot) primary extras))
        offset (offset+len) written.tree.locations := by
  obtain ⟨output,actual,tag,next,held,frameEq,readDone,childDone,⟨childContext⟩,owned,lookup,childWell,capacity,childFits,childCovered⟩ :=
    GeneralBorrowForestFnEntry.invoke tree global frame allocation parentTag parent primary extras offset len mode context covered
      parentTagPresent tagRoom fresh unheld nodeTags slot fits nonzero well bounds before
  have different : parentTag ≠ global.nextPointerTag := by
    intro equal
    rw [equal,unheld] at parentHeld
    cases parentHeld
  have table : output.global.protectedTags = global.protectedTags.insert global.nextPointerTag .StrongProtector := by
    have computed := actual
    simp only [GeneralBorrowForestFnEntry.operation,TypedRetagEmpty.allocate_tag global tagRoom,Except.bind,Except.pure,pure] at computed
    have same := Except.ok.inj computed
    rw [←same]
    rfl
  have retained : output.global.protectedTags.get parentTag = some .StrongProtector := by
    rw [table,GeneralBorrowProtectorCacheMap.insert_other _ _ _ _ different]
    exact parentHeld
  have childBounds : (Size.ofBytes offset).bytes.toNat+(Size.ofBytes len).bytes.toNat ≤ output.child.tree.locations.size.bytes.toNat := by
    rw [capacity]
    exact bounds
  have write := GeneralBorrowForestMutableSlice.access output.child.tree output.global.protectedTags output.tag
    (GeneralBorrowFreshMetadataChildMutableSlot.index slot) primary extras (Size.ofBytes offset) (Size.ofBytes len) .Write mode
    childContext lookup childWell childFits offset (offset+len) owned childBounds (Nat.le_refl _) (Nat.le_refl _)
  exact ⟨output,actual,readDone,childDone,retained,held,frameEq,write.1,write.2.2.1,write.2.2.2.trans capacity,write.2.1⟩
end DuplicatePrefix.GeneralBorrowProtectedRetainedNestedWrite
