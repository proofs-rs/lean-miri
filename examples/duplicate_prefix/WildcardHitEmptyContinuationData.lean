import duplicate_prefix.EmptyForestFromWildcardHit
import duplicate_prefix.EmptyForestSharedReleaseData

namespace DuplicatePrefix.WildcardHitEmptyContinuationData
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

structure Input (tree : BorrowTree) (rootTag sharedTag lenTag : BorTag) where
  depth : GeneralBorrowExposure.ParentDepth tree.nodes
  rootFresh : GeneralBorrowTagMap.Fresh tree.tagMapping rootTag
  sharedFresh : GeneralBorrowTagMap.Fresh tree.tagMapping sharedTag
  lenFresh : GeneralBorrowTagMap.Fresh tree.tagMapping lenTag
  rootShared : rootTag ≠ sharedTag
  rootLen : rootTag ≠ lenTag
  sharedLen : sharedTag ≠ lenTag
  noFree : tree.tagMapping.deassigned.back? = none
  aligned : tree.tagMapping.mapping.size = tree.nodes.data.size
  room : tree.tagMapping.mapping.size+2 ≤ 4294967295
  cleanRoot : ∀ position (valid : position < tree.locations.entries.size),
    tree.locations.entries[position].data.perms.get ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩ = none
  cleanShared : ∀ position (valid : position < tree.locations.entries.size),
    tree.locations.entries[position].data.perms.get ⟨UInt32.ofNat (tree.tagMapping.mapping.size+1)⟩ = none
  cleanLen : ∀ position (valid : position < tree.locations.entries.size),
    tree.locations.entries[position].data.perms.get ⟨UInt32.ofNat (tree.tagMapping.mapping.size+2)⟩ = none

namespace Input
variable {tree : BorrowTree} {rootTag sharedTag lenTag : BorTag}
def first (input : Input tree rootTag sharedTag lenTag) :
    EmptyForestSharedAppend.Input (ActualWildcardHitReference.finalTree tree rootTag) rootTag sharedTag :=
  EmptyForestFromWildcardHit.shared tree input.depth rootTag sharedTag input.rootFresh input.sharedFresh
    input.rootShared input.noFree input.aligned (by have := input.room;omega) input.cleanShared

noncomputable def second (input : Input tree rootTag sharedTag lenTag) :
    EmptyForestSharedAppend.Input input.first.after sharedTag lenTag := by
  apply EmptyForestSharedAppendNext.next input.first lenTag
  · intro row member
    rcases Array.mem_push.mp member with old | last
    · exact input.lenFresh row old
    · cases last;exact input.rootLen
  · exact input.sharedLen
  · simpa only [ActualWildcardHitReference.finalTree,WildcardHitZeroConstructor.installed,Array.size_push] using input.room
  · intro position valid
    simpa only [ActualWildcardHitReference.finalTree,WildcardHitZeroConstructor.installed,Array.size_push,Nat.add_assoc] using input.cleanLen position valid

noncomputable def root (input : Input tree rootTag sharedTag lenTag) :
    EmptyForestSharedReleaseData.Data input.first.after rootTag :=
  EmptyForestSharedReleaseData.after input.first
    (EmptyForestSharedReleaseData.wildcard tree rootTag input.rootFresh input.aligned (by have := input.room;omega) input.cleanRoot)

end Input
end DuplicatePrefix.WildcardHitEmptyContinuationData
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.WildcardHitEmptyContinuationData." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved live HIT continuation data {dependency}"
