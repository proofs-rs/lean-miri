import duplicate_prefix.GeneralBorrowFreshActiveWithinInsert
import duplicate_prefix.GeneralBorrowSharedConstructorRuntime
import duplicate_prefix.GeneralBorrowDefaultConstructorRuntime
import duplicate_prefix.GeneralBorrowProtectedConstructorRuntime
namespace DuplicatePrefix.GeneralBorrowConstructorChildActivity
open Miri Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshActiveWithin
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- Actual fresh-slot installation confines bytewise activity to the selected
window. Topology, tag mapping and node payload impose no permission profile. -/
theorem stage (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (mapping : UniKeyMap BorTag) (inserted : LocationState) (ownerKind : AccessKind)
    (allowed : ∀ kind, inserted.permission.associatedAccess = some kind → ownerKind = .Read → kind = .Read)
    (offset len : UInt64) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (clean : ∀ position (valid : position < tree.locations.entries.size), tree.locations.entries[position].data.perms.get index = none) :
    ActiveWithin (GeneralBorrowFreshMetadataChildAttach.staged tree index parent parentNode newNode mapping
      (tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len)
        (fun _ location => GeneralBorrowFreshMaterialization.materialized location index inserted)).state)
      index ownerKind offset (offset+len) := by
  exact GeneralBorrowFreshActiveWithinInsert.modified tree index (Size.ofBytes offset) (Size.ofBytes len)
    inserted ownerKind allowed well bounds clean

namespace Shared
/-- Exact actual Shared append result, including ancestor SIFA. -/
theorem append (input : GeneralBorrowFreshMetadataChildShared.Input)
    (clean : ∀ position (valid : position < input.tree.locations.entries.size),
      input.tree.locations.entries[position].data.perms.get (GeneralBorrowFreshMetadataChildShared.index input) = none) :
    ActiveWithin (GeneralBorrowFreshMetadataChildShared.result input) (GeneralBorrowFreshMetadataChildShared.index input) .Read input.offset (input.offset+input.len) := by
  have installed := stage input.tree (GeneralBorrowFreshMetadataChildShared.index input) input.parent input.parentNode (GeneralBorrowFreshAnchor.sharedNode input.newTag input.parent)
    (GeneralBorrowFreshMetadataChildShared.mapping input) GeneralBorrowFreshAnchor.sharedState .Read (by intro kind associated _; simpa only [GeneralBorrowFreshAnchor.sharedState,Permission.associatedAccess,Option.some.injEq] using associated.symm) input.offset input.len input.well input.bounds clean
  exact GeneralBorrowFreshActiveWithin.shape_preserves (GeneralBorrowFreshMetadataChildShared.stage input) (GeneralBorrowFreshMetadataChildShared.result input)
    (GeneralBorrowFreshMetadataChildShared.shape input) (GeneralBorrowFreshMetadataChildShared.index input) .Read input.offset (input.offset+input.len) installed
/-- Exact actual Shared Reuse result, including ancestor SIFA. -/
theorem reuse (input : GeneralBorrowFreshMetadataChildSharedReuse.Input)
    (clean : ∀ position (valid : position < input.tree.locations.entries.size),
      input.tree.locations.entries[position].data.perms.get (input.index) = none) :
    ActiveWithin (GeneralBorrowFreshMetadataChildSharedReuse.result input) (input.index) .Read input.offset (input.offset+input.len) := by
  have installed := stage input.tree (input.index) input.parent input.parentNode (GeneralBorrowFreshAnchor.sharedNode input.newTag input.parent)
    (GeneralBorrowFreshMetadataChildSharedReuse.mapping input) GeneralBorrowFreshAnchor.sharedState .Read (by intro kind associated _; simpa only [GeneralBorrowFreshAnchor.sharedState,Permission.associatedAccess,Option.some.injEq] using associated.symm) input.offset input.len input.well input.bounds clean
  exact GeneralBorrowFreshActiveWithin.shape_preserves (GeneralBorrowFreshMetadataChildSharedReuse.stage input) (GeneralBorrowFreshMetadataChildSharedReuse.result input)
    (GeneralBorrowFreshMetadataChildSharedReuse.shape input) (input.index) .Read input.offset (input.offset+input.len) installed
/-- Raw runtime Clean forms the new child's bytewise activity window in
either actual allocator branch. Initial source activity outside is unrestricted. -/
theorem construct (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (held : Bool) (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen held
    ∃ child, actual.tree.indexOfTag newTag = some child ∧ ActiveWithin actual.tree child .Read offset (offset+len) := by
  let rank := GeneralBorrowStructuralHistoryShared.depth tree runtime.formed.toState
  have slot := GeneralBorrowStructuralHistoryShared.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree accounting fits =>
    let input : GeneralBorrowFreshMetadataChildShared.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        noFree,accounting,fits,held,offset,len,nonzero,runtime.formed.well,bounds⟩
    have vacant : tree.nodes.get (GeneralBorrowFreshMetadataChildShared.index input) = none := by
      have atEnd : (GeneralBorrowFreshMetadataChildShared.index input).toNat = tree.nodes.data.size := GeneralBorrowFreshMetadataChildShared.at_end input
      simp only [UniValMap.get,atEnd,Array.getElem?_eq_none (Nat.le_refl _),Option.getD_none]
    have clean : ∀ position (valid : position < tree.locations.entries.size),
        tree.locations.entries[position].data.perms.get (GeneralBorrowFreshMetadataChildShared.index input) = none := by
      intro position valid
      exact (runtime.formed.profile position valid).vacant _ vacant
    exact ⟨GeneralBorrowFreshMetadataChildShared.index input,
      (GeneralBorrowFreshMetadataChildShared.append input).freshLookup,append input clean⟩
  | reuse index available valid vacant slack =>
    let input : GeneralBorrowFreshMetadataChildSharedReuse.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        index,available,valid,vacant,slack,held,offset,len,nonzero,runtime.formed.well,bounds⟩
    have clean : ∀ position (valid : position < tree.locations.entries.size),tree.locations.entries[position].data.perms.get index = none := by
      intro position valid
      exact (runtime.formed.profile position valid).vacant index vacant
    exact ⟨index,(GeneralBorrowFreshMetadataChildSharedReuse.reuse input).freshLookup,reuse input clean⟩
end Shared

namespace Default
/-- Exact actual Default append result, including ancestor SIFA. -/
theorem append (input : GeneralBorrowFreshMetadataChildDefault.Input)
    (clean : ∀ position (valid : position < input.tree.locations.entries.size),
      input.tree.locations.entries[position].data.perms.get (GeneralBorrowFreshMetadataChildDefault.index input) = none) :
    ActiveWithin (GeneralBorrowFreshMetadataChildDefault.result input) (GeneralBorrowFreshMetadataChildDefault.index input) .Write input.offset (input.offset+input.len) := by
  have installed := stage input.tree (GeneralBorrowFreshMetadataChildDefault.index input) input.parent input.parentNode (GeneralBorrowFreshDefaultChild.child input.newTag input.parent)
    (GeneralBorrowFreshMetadataChildDefault.mapping input) GeneralBorrowFreshDefaultChild.inside .Write (by intro kind associated impossible;cases impossible) input.offset input.len input.well input.bounds clean
  exact GeneralBorrowFreshActiveWithin.shape_preserves (GeneralBorrowFreshMetadataChildDefault.stage input) (GeneralBorrowFreshMetadataChildDefault.result input)
    (GeneralBorrowFreshMetadataChildDefault.shape input) (GeneralBorrowFreshMetadataChildDefault.index input) .Write input.offset (input.offset+input.len) installed
/-- Exact actual Default Reuse result, including ancestor SIFA. -/
theorem reuse (input : GeneralBorrowFreshMetadataChildDefaultReuse.Input)
    (clean : ∀ position (valid : position < input.tree.locations.entries.size),
      input.tree.locations.entries[position].data.perms.get (input.index) = none) :
    ActiveWithin (GeneralBorrowFreshMetadataChildDefaultReuse.result input) (input.index) .Write input.offset (input.offset+input.len) := by
  have installed := stage input.tree (input.index) input.parent input.parentNode (GeneralBorrowFreshDefaultChild.child input.newTag input.parent)
    (GeneralBorrowFreshMetadataChildDefaultReuse.mapping input) GeneralBorrowFreshDefaultChild.inside .Write (by intro kind associated impossible;cases impossible) input.offset input.len input.well input.bounds clean
  exact GeneralBorrowFreshActiveWithin.shape_preserves (GeneralBorrowFreshMetadataChildDefaultReuse.stage input) (GeneralBorrowFreshMetadataChildDefaultReuse.result input)
    (GeneralBorrowFreshMetadataChildDefaultReuse.shape input) (input.index) .Write input.offset (input.offset+input.len) installed
/-- Raw runtime Clean forms the new child's bytewise activity window in
either actual allocator branch. Initial source activity outside is unrestricted. -/
theorem construct (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false
    ∃ child, actual.tree.indexOfTag newTag = some child ∧ ActiveWithin actual.tree child .Write offset (offset+len) := by
  let rank := GeneralBorrowStructuralHistoryDefault.depth tree runtime.formed.toState
  have slot := GeneralBorrowStructuralHistoryDefault.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree accounting fits =>
    let input : GeneralBorrowFreshMetadataChildDefault.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        noFree,accounting,fits,offset,len,nonzero,runtime.formed.well,bounds⟩
    have vacant : tree.nodes.get (GeneralBorrowFreshMetadataChildDefault.index input) = none := by
      have atEnd : (GeneralBorrowFreshMetadataChildDefault.index input).toNat = tree.nodes.data.size := GeneralBorrowFreshMetadataChildDefault.at_end input
      simp only [UniValMap.get,atEnd,Array.getElem?_eq_none (Nat.le_refl _),Option.getD_none]
    have clean : ∀ position (valid : position < tree.locations.entries.size),
        tree.locations.entries[position].data.perms.get (GeneralBorrowFreshMetadataChildDefault.index input) = none := by
      intro position valid
      exact (runtime.formed.profile position valid).vacant _ vacant
    exact ⟨GeneralBorrowFreshMetadataChildDefault.index input,
      (GeneralBorrowFreshMetadataChildDefault.append input).freshLookup,append input clean⟩
  | reuse index available valid vacant slack =>
    let input : GeneralBorrowFreshMetadataChildDefaultReuse.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        index,available,valid,vacant,slack,offset,len,nonzero,runtime.formed.well,bounds⟩
    have clean : ∀ position (valid : position < tree.locations.entries.size),tree.locations.entries[position].data.perms.get index = none := by
      intro position valid
      exact (runtime.formed.profile position valid).vacant index vacant
    exact ⟨index,(GeneralBorrowFreshMetadataChildDefaultReuse.reuse input).freshLookup,reuse input clean⟩
end Default

namespace Protected
/-- Exact actual Protected append result, including ancestor SIFA. -/
theorem append (input : GeneralBorrowFreshMetadataChildMutable.Input)
    (clean : ∀ position (valid : position < input.tree.locations.entries.size),
      input.tree.locations.entries[position].data.perms.get (GeneralBorrowFreshMetadataChildMutable.index input) = none) :
    ActiveWithin (GeneralBorrowFreshMetadataChildMutable.result input) (GeneralBorrowFreshMetadataChildMutable.index input) .Write input.offset (input.offset+input.len) := by
  have installed := stage input.tree (GeneralBorrowFreshMetadataChildMutable.index input) input.parent input.parentNode (GeneralBorrowFreshChild.child input.newTag input.parent)
    (GeneralBorrowFreshMetadataChildMutable.mapping input) GeneralBorrowFreshChild.inside .Write (by intro kind associated impossible;cases impossible) input.offset input.len input.well input.bounds clean
  exact GeneralBorrowFreshActiveWithin.shape_preserves (GeneralBorrowFreshMetadataChildMutable.stage input) (GeneralBorrowFreshMetadataChildMutable.result input)
    (GeneralBorrowFreshMetadataChildMutable.shape input) (GeneralBorrowFreshMetadataChildMutable.index input) .Write input.offset (input.offset+input.len) installed
/-- Exact actual Protected Reuse result, including ancestor SIFA. -/
theorem reuse (input : GeneralBorrowFreshMetadataChildMutableReuse.Input)
    (clean : ∀ position (valid : position < input.tree.locations.entries.size),
      input.tree.locations.entries[position].data.perms.get (input.index) = none) :
    ActiveWithin (GeneralBorrowFreshMetadataChildMutableReuse.result input) (input.index) .Write input.offset (input.offset+input.len) := by
  have installed := stage input.tree (input.index) input.parent input.parentNode (GeneralBorrowFreshChild.child input.newTag input.parent)
    (GeneralBorrowFreshMetadataChildMutableReuse.mapping input) GeneralBorrowFreshChild.inside .Write (by intro kind associated impossible;cases impossible) input.offset input.len input.well input.bounds clean
  exact GeneralBorrowFreshActiveWithin.shape_preserves (GeneralBorrowFreshMetadataChildMutableReuse.stage input) (GeneralBorrowFreshMetadataChildMutableReuse.result input)
    (GeneralBorrowFreshMetadataChildMutableReuse.shape input) (input.index) .Write input.offset (input.offset+input.len) installed
/-- Raw runtime Clean forms the new child's bytewise activity window in
either actual allocator branch. Initial source activity outside is unrestricted. -/
theorem construct (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    ∃ child, actual.tree.indexOfTag newTag = some child ∧ ActiveWithin actual.tree child .Write offset (offset+len) := by
  let rank := GeneralBorrowStructuralHistoryMutable.depth tree runtime.formed.toState
  have slot := GeneralBorrowStructuralHistoryMutable.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree accounting fits =>
    let input : GeneralBorrowFreshMetadataChildMutable.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        noFree,accounting,fits,offset,len,nonzero,runtime.formed.well,bounds⟩
    have vacant : tree.nodes.get (GeneralBorrowFreshMetadataChildMutable.index input) = none := by
      have atEnd : (GeneralBorrowFreshMetadataChildMutable.index input).toNat = tree.nodes.data.size := GeneralBorrowFreshMetadataChildMutable.at_end input
      simp only [UniValMap.get,atEnd,Array.getElem?_eq_none (Nat.le_refl _),Option.getD_none]
    have clean : ∀ position (valid : position < tree.locations.entries.size),
        tree.locations.entries[position].data.perms.get (GeneralBorrowFreshMetadataChildMutable.index input) = none := by
      intro position valid
      exact (runtime.formed.profile position valid).vacant _ vacant
    exact ⟨GeneralBorrowFreshMetadataChildMutable.index input,
      (GeneralBorrowFreshMetadataChildMutable.append input).freshLookup,append input clean⟩
  | reuse index available valid vacant slack =>
    let input : GeneralBorrowFreshMetadataChildMutableReuse.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        index,available,valid,vacant,slack,offset,len,nonzero,runtime.formed.well,bounds⟩
    have clean : ∀ position (valid : position < tree.locations.entries.size),tree.locations.entries[position].data.perms.get index = none := by
      intro position valid
      exact (runtime.formed.profile position valid).vacant index vacant
    exact ⟨index,(GeneralBorrowFreshMetadataChildMutableReuse.reuse input).freshLookup,reuse input clean⟩
end Protected
end DuplicatePrefix.GeneralBorrowConstructorChildActivity
