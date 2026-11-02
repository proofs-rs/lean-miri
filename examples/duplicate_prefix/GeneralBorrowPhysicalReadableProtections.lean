import duplicate_prefix.GeneralBorrowPhysicalReadable
import duplicate_prefix.GeneralBorrowSifaProtectionProfile
import duplicate_prefix.GeneralBorrowRelease
namespace DuplicatePrefix.GeneralBorrowPhysicalReadableProtections
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowPhysicalReadable DuplicatePrefix.GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
/-- Physical profiles depend on node metadata and stored permissions, while
other tree and location fields are framed explicitly. -/
theorem nodes (before after : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (same : after.nodes = before.nodes) (initial : Profile before location protections) : Profile after location protections := by
  refine ⟨?_,?_⟩
  · intro index node present
    change after.nodes.get index = some node at present
    rw [same] at present
    exact initial.present index node present
  · intro index vacant
    rw [same] at vacant
    exact initial.vacant index vacant

theorem perms (tree : BorrowTree) (before after : LocationTree) (protections : ProtectedTags)
    (same : after.perms = before.perms) (initial : Profile tree before protections) : Profile tree after protections := by
  refine ⟨?_,?_⟩
  · intro index node present
    rw [same]
    exact initial.present index node present
  · intro index vacant
    rw [same]
    exact initial.vacant index vacant

/-- Fresh actual global/frame protector registration preserves physical SIFA
profiles on the existing graph. Real map freshness and node/tag accounting
exclude an already-present node with this tag; global absence is not inferred. -/
theorem register (tree : BorrowTree) (global : GlobalState) (frame : FrameState)
    (allocation : AllocId) (tag : BorTag) (kind : ProtectorKind)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (nodeTags : ∀ index node,tree.nodeAt index = some node → tree.indexOfTag node.tag = some index)
    (initial : Every (fun location => Profile tree location global.protectedTags) tree.locations) :
    Every (fun location => Profile tree location (global.addProtector frame allocation tag kind).1.protectedTags) tree.locations := by
  have absent : tree.indexOfTag tag = none := by
    simp only [BorrowTree.indexOfTag,UniKeyMap.get,GeneralBorrowTagMap.fresh_find tree.tagMapping tag fresh,Option.map_none]
  intro position valid
  refine ⟨?_,(initial position valid).vacant⟩
  intro query node present
  have different : node.tag ≠ tag := by
    intro same
    have lookup := nodeTags query node present
    rw [same,absent] at lookup;cases lookup
  have heldSame : (global.addProtector frame allocation tag kind).1.protectedTags.contains node.tag = global.protectedTags.contains node.tag := by
    simp only [GlobalState.addProtector,ProtectedTags.contains,
      GeneralBorrowProtectorCacheMap.insert_other global.protectedTags tag node.tag kind different]
  rw [heldSame]
  exact (initial position valid).present query node present


/-- Removing protectors weakens Readable's held-only restrictions. -/
theorem weaken (tree : BorrowTree) (location : LocationTree) (before after : ProtectedTags)
    (weaken : ∀tag,after.contains tag=true→before.contains tag=true)
    (initial : Profile tree location before) : Profile tree location after := by
  refine ⟨?_,initial.vacant⟩
  intro index node present
  obtain ⟨possible,enabled,held⟩ := initial.present index node present
  exact ⟨possible,enabled,fun current=>held (weaken node.tag current)⟩

theorem end_call (tree : BorrowTree) (global : GlobalState) (frame : FrameState)
    (initial : Every (fun location=>Profile tree location global.protectedTags) tree.locations) :
    Every (fun location=>Profile tree location (global.endCall frame).protectedTags) tree.locations := by
  intro position valid
  exact weaken tree _ _ _ (GeneralBorrowRelease.end_call_weakens global frame) (initial position valid)
end DuplicatePrefix.GeneralBorrowPhysicalReadableProtections
