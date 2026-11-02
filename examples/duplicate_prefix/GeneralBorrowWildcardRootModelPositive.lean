import duplicate_prefix.GeneralBorrowWildcardRootRowPositive
import duplicate_prefix.GeneralBorrowWildcardRootRangeTransport
import duplicate_prefix.GeneralBorrowPositiveWildcardConstructor
namespace DuplicatePrefix.GeneralBorrowWildcardRootModelPositive
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralRangeMapOrigins
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
/-- The exact positive wildcard constructor model forms full concrete Both
Positive on its new selected root. Every old callback is transported through
actual range splits and writes; no post-construction row is supplied. -/
theorem positive (tree : BorrowTree) (mapping : UniKeyMap BorTag) (index : UniIndex) (tag : BorTag)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (vacant : tree.nodes.get index = none)
    (size : tree.nodes.size ≤ (tree.nodes.insert index (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None)).size)
    (bound : GeneralBorrowFreshRootCutoff.Bound tree tag)
    (protections : ProtectedTags) (offset len : UInt64) (well : tree.locations.WellFormed)
    (old : DuplicatePrefixBorrowAuthorization.Positive tree protections none none none offset len) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Positive
      (GeneralBorrowPositiveWildcardConstructor.result tree mapping index tag (.ReservedFrz false) .None
        GeneralBorrowFreshChild.inside offset len)
      protections (some index) (some index) (some tag) offset len) := by
  let model := GeneralBorrowPositiveWildcardConstructor.result tree mapping index tag (.ReservedFrz false) .None
    GeneralBorrowFreshChild.inside offset len
  have present : model.nodeAt index = some (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None) :=
    GeneralBorrowFreshLocation.get_same tree.nodes index _
  have geometry := GeneralBorrowFreshRangeFrame.modifyRange_frame tree.locations (Size.ofBytes offset) (Size.ofBytes len)
    (fun _ location => {location with perms := location.perms.insert index GeneralBorrowFreshChild.inside}) well old.bounds
  refine ⟨{positive := old.positive,bounds := ?_,sourcePresent := ?_,wildcardRoot := ?_,rows := ?_}⟩
  · change offset.toNat+len.toNat ≤ model.locations.size.bytes.toNat
    dsimp only [model,GeneralBorrowPositiveWildcardConstructor.result]
    rw [geometry.2]
    exact old.bounds
  · intro anchor same
    have equal : anchor = index := Option.some.inj same.symm
    subst anchor
    exact ⟨_,present⟩
  · intro impossible;cases impossible
  · change OwnedOn (fun location => Nonempty (DuplicatePrefixBorrowAuthorization.Row model location protections
        (some index) (some index) (some tag))) offset (offset+len)
        (tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len)
          (fun _ location => {location with perms := location.perms.insert index GeneralBorrowFreshChild.inside})).state
    apply GeneralBorrowWildcardRootRangeTransport.transport tree.locations index GeneralBorrowFreshChild.inside
      (Size.ofBytes offset) (Size.ofBytes len) well old.bounds
      (fun location => Nonempty (DuplicatePrefixBorrowAuthorization.Row tree location protections none none none))
      (fun location => Nonempty (DuplicatePrefixBorrowAuthorization.Row model location protections
        (some index) (some index) (some tag))) old.rows
    intro location initial
    obtain ⟨row⟩ := initial
    have slots : ∀ query node,tree.nodes.get query = some node →
        (location.perms.insert index GeneralBorrowFreshChild.inside).get query = location.perms.get query := by
      intro query node found
      have different : query ≠ index := by intro same;rw [same,vacant] at found;contradiction
      exact GeneralBorrowFreshLocation.get_other _ index query _ different
    obtain ⟨formed⟩ := GeneralBorrowWildcardRootRowPositive.row tree mapping index tag depth vacant size bound
      location {location with perms := location.perms.insert index GeneralBorrowFreshChild.inside} protections slots
      (GeneralBorrowFreshLocation.get_same _ index _) row
    exact GeneralBorrowWildcardRootRowPositive.row_locations _ model.locations _ protections
      (some index) (some index) (some tag) formed
end DuplicatePrefix.GeneralBorrowWildcardRootModelPositive
