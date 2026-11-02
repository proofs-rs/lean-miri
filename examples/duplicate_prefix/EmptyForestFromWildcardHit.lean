import duplicate_prefix.EmptyForestSharedAppend
import duplicate_prefix.WildcardHitRootDepth
import duplicate_prefix.ActualWildcardHitReference

namespace DuplicatePrefix.EmptyForestFromWildcardHit
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshNode
set_option maxRecDepth 65536
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- Build the first shared continuation's pure data from initial forest/resource
invariants and the exact HIT-created root. No intermediate tree, parent node or
successful child operation is supplied. -/
def shared (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (rootTag sharedTag : BorTag)
    (rootFresh : GeneralBorrowTagMap.Fresh tree.tagMapping rootTag)
    (sharedFresh : GeneralBorrowTagMap.Fresh tree.tagMapping sharedTag)
    (different : rootTag ≠ sharedTag)
    (noFree : tree.tagMapping.deassigned.back? = none)
    (aligned : tree.tagMapping.mapping.size = tree.nodes.data.size)
    (room : tree.tagMapping.mapping.size+1 ≤ 4294967295)
    (clean : ∀ position (valid : position < tree.locations.entries.size),
      tree.locations.entries[position].data.perms.get ⟨UInt32.ofNat (tree.tagMapping.mapping.size+1)⟩ = none) :
    EmptyForestSharedAppend.Input (ActualWildcardHitReference.finalTree tree rootTag) rootTag sharedTag := by
  let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
  have atEnd : index.toNat = tree.nodes.data.size := by
    simp only [index,UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega : tree.tagMapping.mapping.size < 2^32)]
    exact aligned
  refine {
    parent := index
    parentNode := WildcardHitZeroConstructor.rootNode rootTag (.ReservedFrz false) .None
    depth := WildcardHitRootDepth.installed tree depth ⟨tree.tagMapping.mapping.push (rootTag,index),tree.tagMapping.deassigned⟩ index rootTag (.ReservedFrz false) .None atEnd
    tagged := GeneralBorrowTagMap.pushed_get_new tree.tagMapping rootTag rootFresh index tree.tagMapping.deassigned
    present := append_get_same tree.nodes index _ atEnd
    fresh := ?_
    noFree := noFree
    aligned := ?_
    fits := by simpa only [ActualWildcardHitReference.finalTree,WildcardHitZeroConstructor.installed,Array.size_push] using room
    clean := ?_ }
  · intro row member
    rcases Array.mem_push.mp member with old | last
    · exact sharedFresh row old
    · cases last;exact different
  · have size := append_size tree.nodes index (WildcardHitZeroConstructor.rootNode rootTag (.ReservedFrz false) .None) atEnd
    simpa only [ActualWildcardHitReference.finalTree,WildcardHitZeroConstructor.installed,Array.size_push,UniValMap.size,index,aligned] using size.symm
  · intro position valid
    simpa only [ActualWildcardHitReference.finalTree,WildcardHitZeroConstructor.installed,Array.size_push] using clean position valid

end DuplicatePrefix.EmptyForestFromWildcardHit
