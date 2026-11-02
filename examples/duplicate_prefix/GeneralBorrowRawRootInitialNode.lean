import duplicate_prefix.GeneralBorrowRawRootPrefixResources
import duplicate_prefix.GeneralBorrowRawFnEntryHidden
namespace DuplicatePrefix.GeneralBorrowRawRootInitialNode
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
private theorem fn3 {A B C D : Type} (f : A → B → C → D)
    (a1 a2 : A) (b1 b2 : B) (c1 c2 : C)
    (first : a1 = a2) (second : b1 = b2) (third : c1 = c2) : f a1 b1 c1 = f a2 b2 c2 := by
  cases first
  cases second
  cases third
  rfl

abbrev Initial := GeneralBorrowRawRootZeroEntry.Initial

/-- The literal initializer's ORIGINAL fresh mutable child has exact ordinary
node metadata, independently of append/reuse choice. -/
theorem exists_node (s : Initial) :
    ∃ anchor node, (GeneralBorrowRawRootPrefixResources.bufferTree s).indexOfTag s.tracker.global.nextPointerTag = some anchor ∧
      (GeneralBorrowRawRootPrefixResources.bufferTree s).nodeAt anchor = some node ∧
      node.tag = s.tracker.global.nextPointerTag ∧ node.isExposed = false := by
  let original := GeneralBorrowRawFnEntryArgument.finalTree s.entry.allocation.extra s.tracker s.raw.parentTag s.raw.offset s.raw.len
  have trees : original = GeneralBorrowRawRootPrefixResources.bufferTree s :=
    @fn3 BorTag UInt64 UInt64 BorrowTree (GeneralBorrowRawFnEntryArgument.finalTree s.entry.allocation.extra s.tracker)
      s.raw.parentTag s.parentTag s.raw.offset s.offset s.raw.len s.len s.rawTag s.rawOffset s.rawLen
  obtain ⟨anchor,node,lookup,present,tag,hidden⟩ :=
    GeneralBorrowRawFnEntryHidden.hidden s.entry.allocation.extra s.tracker {} s.id s.runtime s.raw
  refine ⟨anchor,node,?_,?_,tag,hidden⟩
  · exact (congrArg (fun tree => tree.indexOfTag s.tracker.global.nextPointerTag) trees.symm).trans lookup
  · exact (congrArg (fun tree => tree.nodeAt anchor) trees.symm).trans present
end
end DuplicatePrefix.GeneralBorrowRawRootInitialNode
