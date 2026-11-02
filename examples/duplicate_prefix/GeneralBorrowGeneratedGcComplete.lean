import duplicate_prefix.GeneralBorrowGeneratedGcProfile
import duplicate_prefix.GeneralBorrowGeneratedStarShape
import duplicate_prefix.GeneralBorrowGcStarShape
import duplicate_prefix.GeneralBorrowGcStarComplete

namespace DuplicatePrefix.GeneralBorrowGeneratedGcComplete
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshMetadataChildShared DuplicatePrefix.GeneralBorrowFullSharedStep
open DuplicatePrefix.GeneralBorrowGeneratedStarShape DuplicatePrefix.GeneralBorrowGeneratedGcProfile
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- The structural star and homogeneous map suffice for actual full GC to
succeed. All graph and range conditions concern the initial state. -/
theorem complete (input : Input) (location : LocationTree) (good : State input location)
    (star : Star input.tree input.parent input.parentNode) (extraLive : Array BorTag) :
    (gc input extraLive).outcome = .ok () ∧
    ∃ next, (gc input extraLive).tree.locations = RangeMapNonempty.homogeneous input.len next := by
  have notChild : input.parent ∉ input.parentNode.children.toList := by
    intro member
    exact ((star.children input.parent).mp member).1 rfl
  have leaves : ∀ index ∈ input.parentNode.children.toList, ∃ child,
      input.tree.nodes.get index = some child ∧ child.children = #[] := by
    intro index member
    obtain ⟨different,child,present⟩ := (star.children index).mp member
    exact ⟨child,present,(star.leaves index child present different).2⟩
  exact GeneralBorrowGcStarComplete.complete input.tree input.parent input.parentNode _ input.len location
    good.locations good.roots input.parentPresent star.distinct notChild leaves (children_bound input.tree input.parent input.parentNode star)

/-- Actual allocation and every finite full-slice shared-generation history
followed by full production GC complete. No initial graph, profile, allocator,
GC success, intermediate Input/Plan or trace is an input premise. -/
theorem generate {n : Nat} (capacity : UInt64) (nonzero : capacity ≠ 0)
    (rootTag childTag : BorTag) (different : rootTag ≠ childTag)
    (tags : List BorTag) (unique : tags.Nodup) (rootUnused : rootTag ∉ tags)
    (childUnused : childTag ∉ tags) (reserve : Fin n → BorTag)
    (reserved : ∀ step, reserve step ∉ rootTag :: childTag :: tags)
    (room : 1+tags.length+4 ≤ 4294967295) (extraLive : Array BorTag) :
    let seed := GeneralBorrowFullSharedSeed.input capacity nonzero rootTag childTag different
    ∃ final finalLocation, GeneralBorrowFullSharedRepeat.Run seed tags final ∧
      GeneralBorrowFullSharedResources.Resources final finalLocation reserve ∧
      final.len = capacity ∧ Star final.tree final.parent final.parentNode ∧
      (gc final extraLive).outcome = .ok () ∧
      (∃ rootNode, Star (gc final extraLive).tree final.parent rootNode) ∧
      ∃ next, (gc final extraLive).tree.locations = RangeMapNonempty.homogeneous capacity next := by
  obtain ⟨final,location,history,resources,_⟩ := GeneralBorrowFullSharedResources.generate capacity nonzero
    rootTag childTag different tags unique rootUnused childUnused reserve reserved room
  obtain ⟨_,_,star⟩ := run_star history GeneralBorrowFullSharedSeed.location
    (GeneralBorrowFullSharedSeed.state capacity nonzero rootTag childTag different)
    (seed_star capacity nonzero rootTag childTag different)
  have facts := complete final location resources.state star extraLive
  have postStar := GeneralBorrowGcStarShape.preserves final.tree final.parent final.parentNode (#[final.parentNode.tag] ++ extraLive) star resources.state.roots
  refine ⟨final,location,history,resources,history.length,star,facts.1,postStar,?_⟩
  have length : final.len = capacity := history.length
  simpa only [length] using facts.2

end DuplicatePrefix.GeneralBorrowGeneratedGcComplete
