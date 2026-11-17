import duplicate_prefix.GeneralBorrowForestProtected
import duplicate_prefix.GeneralBorrowForestMutableRegister
import duplicate_prefix.TypedRetagEmpty

namespace DuplicatePrefix.GeneralBorrowForestFnEntry
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestMutableAccess (Data)
open GeneralBorrowForestAccessData (Context)
open GeneralBorrowFreshReborrowStages (Slot)
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Actual global/frame/BorrowTree outputs of the protected FnEntry borrowing
stage. Typed-reference memory validation and MIR execution are separate. -/
structure Output where
  global : GlobalState
  frame : FrameState
  tag : BorTag
  access : BorrowTree.BorrowTreeAccessResult
  child : BorrowTree.ChildInsertResult

/-- Exact actual allocation→Strong registration→Read→protected Default child
operations. Failure outcomes remain in the real returned records. -/
def operation (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (parentTag : BorTag) (offset len : UInt64) (mode : ChildrenVisitMode) : Except GlobalStateError Output := do
  let (advanced,tag) ← global.newPointerTag
  let (registered,callFrame) := advanced.addProtector frame allocation tag .StrongProtector
  let accessed := GeneralBorrowForestProtected.read tree registered.protectedTags parentTag offset len mode
  let child := accessed.tree.newChild (Size.ofBytes offset) (.concrete parentTag) tag
    (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
  pure ⟨registered,callFrame,tag,accessed,child⟩

/-- A true fresh global next tag, actual registration and actual protected
Default SIFA.None reservation form the new child's full multiple-root mutable
input. Initial GLOBAL unheld is explicit and independent of allocation-map
freshness. Counter headroom, actual node/tag coherence and slice/allocator
conditions are all raw initial records; no operation success is a premise.
This theorem is the global/BorrowTree FnEntry component, not whole MIR safety. -/
theorem invoke (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (parentTag : BorTag) (parent primary : UniIndex) (extras : List UniIndex) (offset len : UInt64) (mode : ChildrenVisitMode)
    (context : Context tree parent primary extras) (covered : GeneralBorrowGraph.RootsCover tree)
    (parentTagPresent : tree.indexOfTag parentTag = some parent)
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
    ∃ output, operation tree global frame allocation parentTag offset len mode = .ok output ∧
      output.tag = global.nextPointerTag ∧ output.global.nextPointerTag = TypedRetagEmpty.successorTag global.nextPointerTag tagRoom ∧
      output.global.protectedTags.get output.tag = some .StrongProtector ∧
      output.frame.protectedTags = frame.protectedTags.push (allocation,output.tag) ∧
      output.access.status = .Completed ∧ output.child.outcome = .ok () ∧
      Nonempty (Context output.child.tree (GeneralBorrowFreshMetadataChildMutableSlot.index slot) primary extras) ∧
      GeneralRangeMapOrigins.OwnedOn
        (fun location => Nonempty (Data output.child.tree location output.global.protectedTags
          (GeneralBorrowFreshMetadataChildMutableSlot.index slot) primary extras))
        offset (offset+len) output.child.tree.locations ∧
      output.child.tree.indexOfTag output.tag = some (GeneralBorrowFreshMetadataChildMutableSlot.index slot) ∧
      output.child.tree.locations.WellFormed ∧ output.child.tree.locations.size = tree.locations.size ∧
      output.child.tree.nodes.data.size ≤ 4294967296 ∧ GeneralBorrowGraph.RootsCover output.child.tree := by
  let advanced := {global with nextPointerTag := TypedRetagEmpty.successorTag global.nextPointerTag tagRoom}
  let registration := advanced.addProtector frame allocation global.nextPointerTag .StrongProtector
  have registered := GeneralBorrowForestMutableRegister.registered tree advanced frame allocation global.nextPointerTag .StrongProtector
    parent primary extras fresh nodeTags unheld offset (offset+len) before
  have stage := GeneralBorrowForestProtected.run tree registration.1.protectedTags parentTag global.nextPointerTag parent primary extras offset len mode
    context covered parentTagPresent fresh slot fits nonzero well bounds registered.2.2.2
  let output : Output := ⟨registration.1,registration.2,global.nextPointerTag,
    GeneralBorrowForestProtected.read tree registration.1.protectedTags parentTag offset len mode,
    GeneralBorrowForestProtected.child tree registration.1.protectedTags parentTag global.nextPointerTag offset len mode⟩
  refine ⟨output,?_,rfl,rfl,registered.1,registered.2.1,stage.1,stage.2.1,stage.2.2.1,stage.2.2.2.1,
    stage.2.2.2.2.1,stage.2.2.2.2.2.1,stage.2.2.2.2.2.2.1,stage.2.2.2.2.2.2.2.1,stage.2.2.2.2.2.2.2.2⟩
  simp only [operation,TypedRetagEmpty.allocate_tag global tagRoom,Except.bind,Except.pure,pure]
  rfl

end DuplicatePrefix.GeneralBorrowForestFnEntry
