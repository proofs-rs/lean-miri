import duplicate_prefix.GeneralBorrowGeneratedGcComplete
import duplicate_prefix.GeneralBorrowStarEntryData

namespace DuplicatePrefix.GeneralBorrowGeneratedGcEntryData
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshMetadataChildShared DuplicatePrefix.GeneralBorrowFullSharedStep
open DuplicatePrefix.GeneralBorrowGeneratedStarShape DuplicatePrefix.GeneralBorrowGeneratedGcProfile
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Actual successful GC yields full retag-entry Data with the allocator's real
append/reuse choice. No post-GC graph, permissions or target success is assumed. -/
theorem collected {n : Nat} (input : Input) (location : LocationTree) (reserve : Fin n → BorTag)
    (initial : GeneralBorrowFullSharedResources.Resources input location reserve)
    (star : Star input.tree input.parent input.parentNode) (extraLive : Array BorTag) :
    (gc input extraLive).outcome = .ok () ∧
    Nonempty (GenericAsMutPtrEntryValidity.Data (gc input extraLive).tree {}
      input.parentNode.tag input.newTag 0 input.len) := by
  have done := GeneralBorrowGeneratedGcComplete.complete input location initial.state star extraLive
  obtain ⟨postLocation,locations⟩ := done.2
  obtain ⟨postNode,postStar⟩ := GeneralBorrowGcStarShape.preserves input.tree input.parent input.parentNode
    (#[input.parentNode.tag] ++ extraLive) star initial.state.roots
  have facts := GeneralBorrowGeneratedGcProfile.collected input location initial.state initial.allocator extraLive
  obtain ⟨heldNode,present,tagged⟩ := facts.2.1
  have sameNode : heldNode = postNode := Option.some.inj (present.symm.trans postStar.present)
  have sameTag : postNode.tag = input.parentNode.tag := sameNode ▸ tagged
  have profile : GeneralBorrowSharedGeneratorProfile.Profile (gc input extraLive).tree postLocation input.parent := by
    have valid : 0 < (gc input extraLive).tree.locations.entries.size := by rw [locations];change 0<1;omega
    simpa only [locations,RangeMapNonempty.homogeneous,Array.getElem_singleton] using facts.2.2 0 valid
  have resources := GeneralBorrowGeneratedGcProfile.resources input location reserve initial extraLive
  have fresh := GeneralBorrowGcResourceFrame.preserves (fun _ : Fin 1 => input.newTag) input.tree
    (#[input.parentNode.tag] ++ extraLive) (fun _ => input.fresh)
  let data := GeneralBorrowStarEntryData.data (gc input extraLive).tree input.parent postNode postStar
    (resources.1.roots.trans initial.state.roots) input.len input.nonzero postLocation locations profile facts.1
    input.newTag (fresh.fresh 0) resources.2.2.1
  have typed : GenericAsMutPtrEntryValidity.Data (gc input extraLive).tree {}
      input.parentNode.tag input.newTag 0 input.len := by
    rw [←sameTag]
    exact data
  exact ⟨done.1,⟨typed⟩⟩

/-- Allocation, arbitrary finite actual full-slice shared history and one actual
full GC construct successful GC and invocation entry Data internally. Only tag
supply, reserved resources and numeric headroom are external borrow premises. -/
theorem generate {n : Nat} (capacity : UInt64) (nonzero : capacity ≠ 0)
    (rootTag childTag : BorTag) (different : rootTag ≠ childTag)
    (tags : List BorTag) (unique : tags.Nodup) (rootUnused : rootTag ∉ tags)
    (childUnused : childTag ∉ tags) (reserve : Fin n → BorTag)
    (reserved : ∀ step, reserve step ∉ rootTag :: childTag :: tags)
    (room : 1+tags.length+4 ≤ 4294967295) (extraLive : Array BorTag) :
    let seed := GeneralBorrowFullSharedSeed.input capacity nonzero rootTag childTag different
    ∃ final finalLocation, GeneralBorrowFullSharedRepeat.Run seed tags final ∧
      GeneralBorrowFullSharedResources.Resources final finalLocation reserve ∧
      final.len = capacity ∧ (gc final extraLive).outcome = .ok () ∧
      Nonempty (GenericAsMutPtrEntryValidity.Data (gc final extraLive).tree {}
        final.parentNode.tag final.newTag 0 final.len) := by
  obtain ⟨final,location,history,resources,length,star,_⟩ := GeneralBorrowGeneratedGcComplete.generate
    capacity nonzero rootTag childTag different tags unique rootUnused childUnused reserve reserved room extraLive
  exact ⟨final,location,history,resources,length,collected final location reserve resources star extraLive⟩

end DuplicatePrefix.GeneralBorrowGeneratedGcEntryData
