import duplicate_prefix.GeneralBorrowSharedReadMetadata
import duplicate_prefix.GeneralBorrowCallbackSourceSharedConstructor
import duplicate_prefix.GeneralBorrowRowRootMetadata
namespace DuplicatePrefix.GeneralBorrowSharedReadPositive
open Miri Miri.Memory Miri.ABI Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralRangeMapOrigins GeneralBorrowReadRowNormal GeneralBorrowRowRootMetadata
open GeneralBorrowSharedCallbacksData
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Read-only positive storage supplies the same permission-independent geometry. -/
theorem geometry (tree : BorrowTree) (protections : ProtectedTags) (source selected : UniIndex)
    (maximum : Option BorTag) (offset len : UInt64) (well : tree.locations.WellFormed)
    (positive : GeneralBorrowReadRowRange.Positive tree protections source selected maximum offset len) :
    Geometry tree source selected maximum := by
  have inside : offset.toNat < tree.locations.size.bytes.toNat := by have p:=positive.positive;have b:=positive.bounds;omega
  obtain ⟨position,valid,start,stop⟩ := GeneralRangeMapGeometry.covered tree.locations well offset inside
  have fits : offset.toNat+len.toNat < 2^64 := Nat.lt_of_le_of_lt positive.bounds tree.locations.size.bytes.toNat_lt
  have nonzero : offset.toNat < (offset+len).toNat := by
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt fits]
    have p:=positive.positive
    omega
  obtain ⟨row⟩ := positive.rows position valid nonzero (by omega) stop
  refine ⟨?_,?_⟩
  · intro location tags
    have same : (source_normal_projection tree location tags).topology =
        (source_normal_projection tree tree.locations.entries[position].data protections).topology := by
      unfold_general_projection
      rfl
    rw [same]
    exact row.rootPath source rfl
  · obtain ⟨node,present⟩ := row.rootPresent selected rfl
    exact ⟨node,present,by simpa only [Option.bind_some,present,Option.map_some] using row.cutoff⟩

/-- Rebuild an internal ReadRow from independent geometry, selected Read table,
and complete other-root callback data. -/
theorem row (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (source selected : UniIndex) (maximum : Option BorTag) (geometry : Geometry tree source selected maximum)
    (normal : DuplicatePrefixNormalKind.Capability tree location protections source .Read)
    (callbacks : Callbacks tree protections selected maximum location) :
    Nonempty (ReadRow tree location protections (some source) (some selected) maximum) := by
  refine ⟨{
    wildcard := ?_,rootPath := ?_,rootPresent := ?_,cutoff := ?_,normal := ?_,callbacks := callbacks}⟩
  · intro impossible;cases impossible
  · intro anchor same
    have same : anchor = source := Option.some.inj same.symm
    subst anchor
    exact geometry.path location protections
  · intro root same
    have same : root = selected := Option.some.inj same.symm
    subst root
    obtain ⟨node,present,_⟩ := geometry.root
    exact ⟨node,present⟩
  · obtain ⟨node,present,cutoff⟩ := geometry.root
    simpa only [Option.bind_some,present,Option.map_some] using cutoff
  · intro anchor same
    have same : anchor = source := Option.some.inj same.symm
    subst anchor
    exact ⟨normal⟩

/-- Actual shared construction from a Read-only parent yields SAME-window
parent and child ReadRowPositive, for either fresh protector state and either
allocator case. Source Write permission is never required or asserted. -/
theorem construct (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (tagBound : newTag.value.toNat < global.nextPointerTag.value.toNat)
    (held : Bool) (aligned : global.protectedTags.contains newTag = held)
    (selected : UniIndex) (maximum : Option BorTag) (offset len : UInt64)
    (positive : GeneralBorrowReadRowRange.Positive tree global.protectedTags parent selected maximum offset len) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen held
    actual.outcome = .ok () ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global ∧
    actual.tree.locations.size = tree.locations.size ∧ actual.tree.nodes.size ≤ tree.nodes.size+1 ∧
    ∃ child,actual.tree.indexOfTag newTag = some child ∧ actual.tree.roots = tree.roots ∧
      Nonempty (GeneralBorrowReadRowRange.Positive actual.tree global.protectedTags parent selected maximum offset len) ∧
      Nonempty (GeneralBorrowReadRowRange.Positive actual.tree global.protectedTags child selected maximum offset len) := by
  have nonzero : len ≠ 0 := by intro zero;have p:=positive.positive;rw [zero] at p;contradiction
  have normals : OwnedOn (fun location => Nonempty (DuplicatePrefixNormalKind.Capability tree location global.protectedTags parent .Read))
      offset (offset+len) tree.locations := by
    intro position valid nonempty beforeUpper afterLower
    obtain ⟨row⟩ := positive.rows position valid nonempty beforeUpper afterLower
    exact row.normal parent rfl
  have sources : OwnedOn (fun location => Nonempty (GeneralBorrowCallbackSource.Source tree location global.protectedTags parent selected maximum))
      offset (offset+len) tree.locations := by
    intro position valid nonempty beforeUpper afterLower
    obtain ⟨row⟩ := positive.rows position valid nonempty beforeUpper afterLower
    exact ⟨GeneralBorrowCallbackSource.of_read_row tree _ global.protectedTags parent selected maximum row⟩
  have capabilities := GeneralBorrowSharedReadConstructor.construct tree global runtime parentTag newTag parent parentNode
    tagged present fresh room tagBound held aligned offset len nonzero positive.bounds normals
  obtain ⟨child,lookup,both⟩ := capabilities.2.2.2.2
  have callbacks := GeneralBorrowCallbackSourceSharedConstructor.construct tree global runtime parentTag newTag parent parentNode
    tagged present fresh room tagBound held aligned selected maximum offset len nonzero positive.bounds sources
  obtain ⟨callbackChild,callbackLookup,roots,allCallbacks⟩ := callbacks.2.2.2.2
  have same : callbackChild = child := Option.some.inj (callbackLookup.symm.trans lookup)
  subst callbackChild
  obtain ⟨metadataChild,metadataLookup,data⟩ := GeneralBorrowSharedReadMetadata.construct tree global runtime
    parentTag newTag parent parentNode tagged present fresh room held offset len nonzero positive.bounds
  have same : metadataChild = child := Option.some.inj (metadataLookup.symm.trans lookup)
  subst metadataChild
  have oldGeometry := geometry tree global.protectedTags parent selected maximum offset len runtime.formed.well positive
  have childGeometry := after_attach tree _ parent child selected maximum oldGeometry data.paths data.nodes
  have parentGeometry := after_attach_parent tree _ parent child selected maximum oldGeometry data.paths data.nodes
  obtain ⟨newParent,parentFound,_,_⟩ := data.nodes parent parentNode present
  refine ⟨capabilities.1,capabilities.2.1,capabilities.2.2.1,capabilities.2.2.2.1,child,lookup,roots,?_,?_⟩
  · refine ⟨{
      positive := positive.positive,bounds := ?_,sourcePresent := ⟨newParent,parentFound⟩,rows := ?_}⟩
    · rw [capabilities.2.2.1]
      exact positive.bounds
    · intro position valid nonempty beforeUpper afterLower
      obtain ⟨⟨normal⟩,_⟩ := both position valid nonempty beforeUpper afterLower
      exact row _ _ global.protectedTags parent selected maximum parentGeometry normal
        (allCallbacks position valid nonempty beforeUpper afterLower)
  · refine ⟨{
      positive := positive.positive,bounds := ?_,sourcePresent := data.childPresent,rows := ?_}⟩
    · rw [capabilities.2.2.1]
      exact positive.bounds
    · intro position valid nonempty beforeUpper afterLower
      obtain ⟨_,⟨normal⟩⟩ := both position valid nonempty beforeUpper afterLower
      exact row _ _ global.protectedTags child selected maximum childGeometry normal
        (allCallbacks position valid nonempty beforeUpper afterLower)
end DuplicatePrefix.GeneralBorrowSharedReadPositive
