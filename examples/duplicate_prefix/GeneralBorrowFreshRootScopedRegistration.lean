import duplicate_prefix.GeneralBorrowFreshRootScopedReadRow
import duplicate_prefix.GeneralBorrowFnEntryReadRegistration
namespace DuplicatePrefix.GeneralBorrowFreshRootScopedRegistration
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFnEntryRegistration (advanced registered)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
theorem row (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (tag : BorTag) (kind : ProtectorKind) (fresh : GeneralBorrowProtector.Fresh tree tag)
    (source selected : UniIndex) (maximum : BorTag)
    (old : GeneralBorrowFreshRootScopedRow.Row tree location protections source selected maximum) :
    Nonempty (GeneralBorrowFreshRootScopedRow.Row tree location (protections.insert tag kind) source selected maximum) := by
  obtain ⟨base⟩ := GeneralBorrowFreshRegistration.row tree location protections tag kind fresh (some source) (some selected) (some maximum) old.base
  have same : ∀ index node,tree.nodeAt index = some node →
      (protections.insert tag kind).contains node.tag = protections.contains node.tag := by
    intro index node present
    exact ProtectorInsertion.contains_other protections tag node.tag kind (fresh (index,node)
      (Array.mem_toList_iff.mp ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes index node).mpr present)))
  refine ⟨⟨base,old.exposed,?_⟩⟩
  intro position valid different
  obtain ⟨support,bounded,read,write⟩ := old.callbacks position valid different
  exact ⟨support,bounded,GeneralBorrowFreshRegistration.authorization tree location protections _ same _ _ _ _ _ read,
    GeneralBorrowFreshRegistration.authorization tree location protections _ same _ _ _ _ _ write⟩

theorem positive (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag) (kind : ProtectorKind)
    (fresh : GeneralBorrowProtector.Fresh tree tag) (source selected : UniIndex) (maximum : BorTag) (offset len : UInt64)
    (old : GeneralBorrowFreshRootScopedRow.Positive tree protections source selected maximum offset len) :
    Nonempty (GeneralBorrowFreshRootScopedRow.Positive tree (protections.insert tag kind) source selected maximum offset len) := by
  obtain ⟨base⟩ := GeneralBorrowFreshRegistration.positive tree protections tag kind fresh (some source) (some selected) (some maximum) offset len old.base
  refine ⟨⟨base,?_⟩⟩
  intro position valid nonzero start stop
  obtain ⟨row⟩ := old.rows position valid nonzero start stop
  exact GeneralBorrowFreshRootScopedRegistration.row tree _ protections tag kind fresh source selected maximum row

theorem prepare (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (room : global.nextPointerTag.value < 18446744073709551615)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (source selected : UniIndex) (maximum : BorTag) (offset len : UInt64)
    (positive : GeneralBorrowFreshRootScopedRow.Positive tree global.protectedTags source selected maximum offset len) :
    global.newPointerTag = .ok (advanced global room,global.nextPointerTag) ∧
    (registered global frame allocation room).1.protectedTags.get global.nextPointerTag = some .StrongProtector ∧
    (registered global frame allocation room).2.protectedTags = frame.protectedTags.push (allocation,global.nextPointerTag) ∧
    DuplicatePrefixBorrowContract.RuntimeFacts tree (registered global frame allocation room).1 ∧
    Nonempty (GeneralBorrowFreshRootScopedRow.Positive tree (registered global frame allocation room).1.protectedTags source selected maximum offset len) ∧
    GeneralBorrowTagMap.Fresh tree.tagMapping global.nextPointerTag := by
  obtain ⟨allocated,held,pushed,current,nodeFresh,fresh⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare tree global frame allocation room runtime
  exact ⟨allocated,held,pushed,current,
    GeneralBorrowFreshRootScopedRegistration.positive tree global.protectedTags global.nextPointerTag .StrongProtector nodeFresh source selected maximum offset len positive,fresh⟩

theorem read_row (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (tag : BorTag) (kind : ProtectorKind) (fresh : GeneralBorrowProtector.Fresh tree tag)
    (source selected : UniIndex) (maximum : BorTag)
    (old : GeneralBorrowFreshRootScopedReadRow.Row tree location protections source selected maximum) :
    Nonempty (GeneralBorrowFreshRootScopedReadRow.Row tree location (protections.insert tag kind) source selected maximum) := by
  obtain ⟨base⟩ := GeneralBorrowFreshReadRegistration.row tree location protections tag kind fresh (some source) (some selected) (some maximum) old.base
  have same : ∀ index node,tree.nodeAt index = some node →
      (protections.insert tag kind).contains node.tag = protections.contains node.tag := by
    intro index node present
    exact ProtectorInsertion.contains_other protections tag node.tag kind (fresh (index,node)
      (Array.mem_toList_iff.mp ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes index node).mpr present)))
  refine ⟨⟨base,old.exposed,?_⟩⟩
  intro position valid different
  obtain ⟨support,bounded,read,write⟩ := old.callbacks position valid different
  exact ⟨support,bounded,GeneralBorrowFreshRegistration.authorization tree location protections _ same _ _ _ _ _ read,
    GeneralBorrowFreshRegistration.authorization tree location protections _ same _ _ _ _ _ write⟩

theorem read_positive (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag) (kind : ProtectorKind)
    (fresh : GeneralBorrowProtector.Fresh tree tag) (source selected : UniIndex) (maximum : BorTag) (offset len : UInt64)
    (old : GeneralBorrowFreshRootScopedReadRow.Positive tree protections source selected maximum offset len) :
    Nonempty (GeneralBorrowFreshRootScopedReadRow.Positive tree (protections.insert tag kind) source selected maximum offset len) := by
  obtain ⟨base⟩ := GeneralBorrowFreshReadRegistration.positive tree protections tag kind fresh source selected (some maximum) offset len old.base
  refine ⟨⟨base,?_⟩⟩
  intro position valid nonzero start stop
  obtain ⟨row⟩ := old.rows position valid nonzero start stop
  exact read_row tree _ protections tag kind fresh source selected maximum row

theorem read_prepare (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (room : global.nextPointerTag.value < 18446744073709551615)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (source selected : UniIndex) (maximum : BorTag) (offset len : UInt64)
    (positive : GeneralBorrowFreshRootScopedReadRow.Positive tree global.protectedTags source selected maximum offset len) :
    global.newPointerTag = .ok (advanced global room,global.nextPointerTag) ∧
    (registered global frame allocation room).1.protectedTags.get global.nextPointerTag = some .StrongProtector ∧
    (registered global frame allocation room).2.protectedTags = frame.protectedTags.push (allocation,global.nextPointerTag) ∧
    DuplicatePrefixBorrowContract.RuntimeFacts tree (registered global frame allocation room).1 ∧
    Nonempty (GeneralBorrowFreshRootScopedReadRow.Positive tree (registered global frame allocation room).1.protectedTags source selected maximum offset len) ∧
    GeneralBorrowTagMap.Fresh tree.tagMapping global.nextPointerTag := by
  obtain ⟨allocated,held,pushed,current,nodeFresh,fresh⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare tree global frame allocation room runtime
  exact ⟨allocated,held,pushed,current,
    read_positive tree global.protectedTags global.nextPointerTag .StrongProtector nodeFresh source selected maximum offset len positive,fresh⟩

end DuplicatePrefix.GeneralBorrowFreshRootScopedRegistration
