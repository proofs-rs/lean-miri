import duplicate_prefix.GeneralBorrowSharedConstructorRuntime
import duplicate_prefix.GeneralBorrowSharedChildGraph
import duplicate_prefix.GeneralBorrowFreshActiveWithin
namespace DuplicatePrefix.S05SharedChildActivity
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowFreshAnchor
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- Activity of the actual shared child follows solely from clean vacant slots
and actual range materialization, including either allocator choice and SIFA. -/
theorem construct (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (tagBound : newTag.value.toNat < global.nextPointerTag.value.toNat)
    (held : Bool) (aligned : global.protectedTags.contains newTag = held)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) sharedState) .Frozen held
    actual.outcome = .ok () ∧ ∃ child, actual.tree.indexOfTag newTag = some child ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin actual.tree child .Read offset (offset+len) := by
  have completed := GeneralBorrowSharedConstructorRuntime.construct tree global runtime parentTag newTag parent parentNode
    tagged present fresh room tagBound held aligned offset len nonzero bounds
  refine ⟨completed.1,?_⟩
  let rank := GeneralBorrowStructuralHistoryShared.depth tree runtime.formed.toState
  have slot := GeneralBorrowStructuralHistoryShared.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree accounting fits =>
    let input : GeneralBorrowFreshMetadataChildShared.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        noFree,accounting,fits,held,offset,len,nonzero,runtime.formed.well,bounds⟩
    let child := GeneralBorrowFreshMetadataChildShared.index input
    have vacant : tree.nodes.get child = none := by
      have atEnd : child.toNat = tree.nodes.data.size := GeneralBorrowFreshMetadataChildShared.at_end input
      simp only [UniValMap.get,atEnd,Array.getElem?_eq_none (Nat.le_refl _)]
    have active := GeneralBorrowFreshActiveWithin.modified tree child (Size.ofBytes offset) (Size.ofBytes len)
      runtime.formed.well bounds (fun position valid => (runtime.formed.profile position valid).vacant child vacant)
    have stageActive : GeneralBorrowFreshActiveWithin.ActiveWithin (GeneralBorrowFreshMetadataChildShared.stage input)
        child .Read offset (offset+len) := active
    exact ⟨child,(GeneralBorrowFreshMetadataChildShared.append input).freshLookup,
      GeneralBorrowFreshActiveWithin.shape_preserves _ _ (GeneralBorrowFreshMetadataChildShared.shape input)
        child .Read offset (offset+len) stageActive⟩
  | reuse child available valid vacant slack =>
    let input : GeneralBorrowFreshMetadataChildSharedReuse.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        child,available,valid,vacant,slack,held,offset,len,nonzero,runtime.formed.well,bounds⟩
    have active := GeneralBorrowFreshActiveWithin.modified tree child (Size.ofBytes offset) (Size.ofBytes len)
      runtime.formed.well bounds (fun position valid => (runtime.formed.profile position valid).vacant child vacant)
    have stageActive : GeneralBorrowFreshActiveWithin.ActiveWithin (GeneralBorrowFreshMetadataChildSharedReuse.stage input)
        child .Read offset (offset+len) := active
    exact ⟨child,(GeneralBorrowFreshMetadataChildSharedReuse.reuse input).freshLookup,
      GeneralBorrowFreshActiveWithin.shape_preserves _ _ (GeneralBorrowFreshMetadataChildSharedReuse.shape input)
        child .Read offset (offset+len) stageActive⟩
end DuplicatePrefix.S05SharedChildActivity
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05SharedChildActivity." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved shared child activity dependency {dependency}"
