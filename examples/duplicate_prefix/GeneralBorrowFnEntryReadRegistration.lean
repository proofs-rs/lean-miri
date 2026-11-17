import duplicate_prefix.GeneralBorrowFnEntryRegistrationRuntime
import duplicate_prefix.GeneralBorrowFreshReadRegistration

namespace DuplicatePrefix.GeneralBorrowFnEntryReadRegistration
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFnEntryRegistration (advanced registered)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Actual newPointerTag and Strong registry/frame updates retain a raw Read
owner window and all runtime facts. No source Write permission, slot choice,
future capability or successful-operation premise is required. -/
theorem prepare (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (room : global.nextPointerTag.value < 18446744073709551615)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (anchor selected : UniIndex) (maximum : Option BorTag) (offset len : UInt64)
    (positive : GeneralBorrowReadRowRange.Positive tree global.protectedTags anchor selected maximum offset len) :
    global.newPointerTag = .ok (advanced global room,global.nextPointerTag) ∧
    (registered global frame allocation room).1.protectedTags.get global.nextPointerTag = some .StrongProtector ∧
    (registered global frame allocation room).2.protectedTags = frame.protectedTags.push (allocation,global.nextPointerTag) ∧
    DuplicatePrefixBorrowContract.RuntimeFacts tree (registered global frame allocation room).1 ∧
    Nonempty (GeneralBorrowReadRowRange.Positive tree (registered global frame allocation room).1.protectedTags
      anchor selected maximum offset len) ∧
    GeneralBorrowTagMap.Fresh tree.tagMapping global.nextPointerTag := by
  obtain ⟨allocated,held,pushed,current,nodeFresh,fresh⟩ :=
    GeneralBorrowFnEntryRegistrationRuntime.prepare tree global frame allocation room runtime
  exact ⟨allocated,held,pushed,current,
    GeneralBorrowFreshReadRegistration.positive tree global.protectedTags global.nextPointerTag .StrongProtector
      nodeFresh anchor selected maximum offset len positive,fresh⟩

end DuplicatePrefix.GeneralBorrowFnEntryReadRegistration
