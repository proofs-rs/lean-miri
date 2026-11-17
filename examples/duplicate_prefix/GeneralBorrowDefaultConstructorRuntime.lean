import duplicate_prefix.GeneralBorrowDefaultConstructorPossible
import duplicate_prefix.GeneralBorrowDefaultConstructorExposureCache
import duplicate_prefix.DuplicatePrefixBorrowContract
namespace DuplicatePrefix.GeneralBorrowDefaultConstructorRuntime
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshDefaultChild (inside)
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- The real concrete Default mutable constructor preserves complete call-time runtime
facts with arbitrary consistent allocator pools and arbitrary exposure forests.
The fresh tag's strict bound is an explicit external counter resource. -/
theorem construct (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (tagBound : newTag.value.toNat < global.nextPointerTag.value.toNat)
    (aligned : global.protectedTags.contains newTag = false)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) inside) (.ReservedFrz false) false
    actual.outcome = .ok () ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global ∧
    actual.tree.locations.size = tree.locations.size ∧ actual.tree.nodes.size ≤ tree.nodes.size+1 := by
  have formed := GeneralBorrowDefaultConstructorFormed.construct tree global.protectedTags runtime.formed parentTag newTag parent parentNode
    tagged present fresh room aligned offset len nonzero bounds
  let rank := GeneralBorrowStructuralHistoryDefault.depth tree runtime.formed.toState
  let slot := GeneralBorrowStructuralHistoryDefault.slot tree runtime.formed.toState parent parentNode present room
  have closure :
      GeneralRangeMapState.Every (fun location => GeneralBorrowExposureCardinality.LocationCoherent
        (GeneralBorrowFreshMetadataChildDefaultSlot.result tree parentTag newTag offset len) location global.protectedTags)
        (GeneralBorrowFreshMetadataChildDefaultSlot.result tree parentTag newTag offset len).locations ∧
      GeneralRangeMapState.Every (GeneralBorrowSnapshotReadRuntime.GlobalPossible
        (GeneralBorrowFreshMetadataChildDefaultSlot.result tree parentTag newTag offset len))
        (GeneralBorrowFreshMetadataChildDefaultSlot.result tree parentTag newTag offset len).locations ∧
      GeneralBorrowForestTagHighWater.Below (GeneralBorrowFreshMetadataChildDefaultSlot.result tree parentTag newTag offset len)
        global.protectedTags global.nextPointerTag := by
    cases slot with
    | append noFree accounting fits =>
      let input : GeneralBorrowFreshMetadataChildDefault.Input :=
        ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
          noFree,accounting,fits,offset,len,nonzero,runtime.formed.well,bounds⟩
      have coherence := (GeneralBorrowDefaultConstructorExposureCache.append input global.protectedTags runtime.coherent).2
      have vacant : tree.nodes.get (GeneralBorrowFreshMetadataChildDefault.index input) = none := by
        have atEnd : (GeneralBorrowFreshMetadataChildDefault.index input).toNat = tree.nodes.data.size := GeneralBorrowFreshMetadataChildDefault.at_end input
        simp only [UniValMap.get,atEnd,Array.getElem?_eq_none (Nat.le_refl _),Option.getD_none]
      have possible := GeneralBorrowDefaultConstructorPossible.default_stage tree global.protectedTags
        (GeneralBorrowFreshMetadataChildDefault.index input) parent parentNode newTag (GeneralBorrowFreshMetadataChildDefault.mapping input)
        vacant present offset len runtime.formed.well bounds runtime.formed.profile runtime.possible
      change GeneralRangeMapState.Every (GeneralBorrowSnapshotReadRuntime.GlobalPossible
        (sourceUpdateSifa (GeneralBorrowFreshMetadataChildDefault.stage input) input.parent .Read).1)
        (sourceUpdateSifa (GeneralBorrowFreshMetadataChildDefault.stage input) input.parent .Read).1.locations at possible
      rw [←GeneralBorrowFreshMetadataChildDefault.tree_eq input] at possible
      refine ⟨coherence,possible,⟨?_,runtime.below.protectors⟩⟩
      intro row member
      change row ∈ (GeneralBorrowFreshMetadataChildDefault.result input).tagMapping.mapping at member
      rw [(GeneralBorrowFreshMetadataChildDefault.append input).mapping] at member
      change row ∈ tree.tagMapping.mapping.push (newTag,GeneralBorrowFreshMetadataChildDefault.index input) at member
      rcases Array.mem_push.mp member with previous | latest
      · exact runtime.below.mapping row previous
      · subst row;exact tagBound
    | reuse index available valid vacant slack =>
      let input : GeneralBorrowFreshMetadataChildDefaultReuse.Input :=
        ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
          index,available,valid,vacant,slack,offset,len,nonzero,runtime.formed.well,bounds⟩
      have coherence := (GeneralBorrowDefaultConstructorExposureCache.reuse input global.protectedTags runtime.coherent).2
      have possible := GeneralBorrowDefaultConstructorPossible.default_stage tree global.protectedTags index parent parentNode newTag
        (GeneralBorrowFreshMetadataChildDefaultReuse.mapping input) vacant present offset len runtime.formed.well bounds runtime.formed.profile runtime.possible
      change GeneralRangeMapState.Every (GeneralBorrowSnapshotReadRuntime.GlobalPossible
        (sourceUpdateSifa (GeneralBorrowFreshMetadataChildDefaultReuse.stage input) input.parent .Read).1)
        (sourceUpdateSifa (GeneralBorrowFreshMetadataChildDefaultReuse.stage input) input.parent .Read).1.locations at possible
      rw [←GeneralBorrowFreshMetadataChildDefaultReuse.tree_eq input] at possible
      refine ⟨coherence,possible,⟨?_,runtime.below.protectors⟩⟩
      intro row member
      change row ∈ (GeneralBorrowFreshMetadataChildDefaultReuse.result input).tagMapping.mapping at member
      rw [(GeneralBorrowFreshMetadataChildDefaultReuse.reuse input).mapping] at member
      change row ∈ tree.tagMapping.mapping.push (newTag,index) at member
      rcases Array.mem_push.mp member with previous | latest
      · exact runtime.below.mapping row previous
      · subst row;exact tagBound
  exact ⟨formed.1,⟨formed.2.1,closure.1,closure.2.1,closure.2.2⟩,formed.2.2.1,formed.2.2.2⟩

end DuplicatePrefix.GeneralBorrowDefaultConstructorRuntime
