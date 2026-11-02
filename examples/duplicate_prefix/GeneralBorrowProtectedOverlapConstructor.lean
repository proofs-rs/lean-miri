import duplicate_prefix.GeneralBorrowProtectedReadRange
import duplicate_prefix.GeneralBorrowFreshReadFrame
namespace DuplicatePrefix.GeneralBorrowProtectedOverlapConstructor
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralRangeMapOrigins
open DuplicatePrefix.GeneralBorrowConstructorPriorPermission
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Actual leading Read followed by protected Default append, allowing an
already accessed, held earlier reservation. The conflict is established by the
actual ranged source visitor and retained through constructor SIFA.None. -/
theorem append (input : GeneralBorrowFreshMetadataChildMutable.Input)
    (protections : ProtectedTags) (earlier : UniIndex) (earlierNode : TreeNode)
    (roots : input.tree.roots = #[input.parent]) (parentless : input.parentNode.parent = none)
    (earlierPresent : input.tree.nodeAt earlier = some earlierNode)
    (listed : earlier ∈ input.parentNode.children) (held : protections.contains earlierNode.tag = true)
    (different : earlier ≠ GeneralBorrowFreshMetadataChildMutable.index input)
    (initial : GeneralRangeMapState.Every (GeneralBorrowProtectedReadRange.Before input.tree protections input.parent earlier) input.tree.locations) :
    let read := input.tree.performNormalAccessRange input.parentTag (Size.ofBytes input.offset)
      (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed
    let child := read.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    read.status = .Completed ∧ child.outcome = .ok () ∧
      OwnedOn (At earlier (some (.ReservedFrz true))) input.offset (input.offset+input.len) child.tree.locations := by
  let read := input.tree.performNormalAccessRange input.parentTag (Size.ofBytes input.offset)
    (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed
  have fits : input.tree.nodes.data.size ≤ 4294967296 := by
    have aligned := input.aligned
    have bound := input.fits
    omega
  have conflict := GeneralBorrowProtectedReadRange.root_conflict input.tree protections input.parentTag input.parent earlier
    input.parentNode earlierNode input.offset input.len fits input.depth input.children input.covered roots
    input.parentTagPresent input.parentPresent parentless earlierPresent listed held input.well input.bounds initial
  have all : GeneralRangeMapState.Every (GeneralBorrowProtectedReadRange.LocationCompatible input.tree protections input.parent) input.tree.locations := by
    intro position valid
    exact (initial position valid).1
  have good := GeneralBorrowProtectedReadRange.geometry input.tree protections input.parentTag input.parent input.parent
    (Size.ofBytes input.offset) (Size.ofBytes input.len) .VisitChildrenOfAccessed input.depth input.children input.parentNode
    input.parentPresent roots input.covered input.parentTagPresent input.well all input.bounds
  have frame : read.tree = {input.tree with locations := read.tree.locations} :=
    GeneralBorrowFreshReadFrame.frame input.tree (.concrete input.parentTag) (Size.ofBytes input.offset)
      (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed
  have nodes : read.tree.nodes = input.tree.nodes := by simpa only using congrArg BorrowTree.nodes frame
  have mapping : read.tree.tagMapping = input.tree.tagMapping := by simpa only using congrArg BorrowTree.tagMapping frame
  let next : GeneralBorrowFreshMetadataChildMutable.Input := {
    input with
    tree := read.tree
    depth := GeneralBorrowFreshReadFrame.depth_on input.tree read.tree nodes input.depth
    children := by rw [frame];exact input.children
    covered := by rw [frame];exact input.covered
    parentTagPresent := by rw [frame];exact input.parentTagPresent
    parentPresent := by rw [frame];exact input.parentPresent
    fresh := by rw [frame];exact input.fresh
    noFree := by rw [frame];exact input.noFree
    aligned := by rw [frame];exact input.aligned
    fits := by rw [frame];exact input.fits
    well := good.1
    bounds := by rw [good.2];exact input.bounds }
  have separated : earlier ≠ GeneralBorrowFreshMetadataChildMutable.index next := by
    change earlier ≠ ⟨UInt32.ofNat read.tree.tagMapping.mapping.size⟩
    rw [mapping]
    exact different
  have preserved := GeneralBorrowConstructorPriorPermissionRange.protected_append next earlier
    (some (.ReservedFrz true)) input.offset (input.offset+input.len) separated conflict.2
  exact ⟨conflict.1,preserved.1,preserved.2⟩

/-- The same chronology for the real vacant-slot reuse branch. -/
theorem reuse (input : GeneralBorrowFreshMetadataChildMutableReuse.Input)
    (fits : input.tree.nodes.data.size ≤ 4294967296)
    (protections : ProtectedTags) (earlier : UniIndex) (earlierNode : TreeNode)
    (roots : input.tree.roots = #[input.parent]) (parentless : input.parentNode.parent = none)
    (earlierPresent : input.tree.nodeAt earlier = some earlierNode)
    (listed : earlier ∈ input.parentNode.children) (held : protections.contains earlierNode.tag = true)
    (different : earlier ≠ GeneralBorrowFreshMetadataChildMutableReuse.index input)
    (initial : GeneralRangeMapState.Every (GeneralBorrowProtectedReadRange.Before input.tree protections input.parent earlier) input.tree.locations) :
    let read := input.tree.performNormalAccessRange input.parentTag (Size.ofBytes input.offset)
      (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed
    let child := read.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    read.status = .Completed ∧ child.outcome = .ok () ∧
      OwnedOn (At earlier (some (.ReservedFrz true))) input.offset (input.offset+input.len) child.tree.locations := by
  let read := input.tree.performNormalAccessRange input.parentTag (Size.ofBytes input.offset)
    (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed
  have conflict := GeneralBorrowProtectedReadRange.root_conflict input.tree protections input.parentTag input.parent earlier
    input.parentNode earlierNode input.offset input.len fits input.depth input.children input.covered roots
    input.parentTagPresent input.parentPresent parentless earlierPresent listed held input.well input.bounds initial
  have all : GeneralRangeMapState.Every (GeneralBorrowProtectedReadRange.LocationCompatible input.tree protections input.parent) input.tree.locations := by
    intro position valid
    exact (initial position valid).1
  have good := GeneralBorrowProtectedReadRange.geometry input.tree protections input.parentTag input.parent input.parent
    (Size.ofBytes input.offset) (Size.ofBytes input.len) .VisitChildrenOfAccessed input.depth input.children input.parentNode
    input.parentPresent roots input.covered input.parentTagPresent input.well all input.bounds
  have frame : read.tree = {input.tree with locations := read.tree.locations} :=
    GeneralBorrowFreshReadFrame.frame input.tree (.concrete input.parentTag) (Size.ofBytes input.offset)
      (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed
  have nodes : read.tree.nodes = input.tree.nodes := by simpa only using congrArg BorrowTree.nodes frame
  have mapping : read.tree.tagMapping = input.tree.tagMapping := by simpa only using congrArg BorrowTree.tagMapping frame
  let next : GeneralBorrowFreshMetadataChildMutableReuse.Input := {
    input with
    tree := read.tree
    depth := GeneralBorrowFreshReadFrame.depth_on input.tree read.tree nodes input.depth
    children := by rw [frame];exact input.children
    covered := by rw [frame];exact input.covered
    parentTagPresent := by rw [frame];exact input.parentTagPresent
    parentPresent := by rw [frame];exact input.parentPresent
    fresh := by rw [frame];exact input.fresh
    available := by rw [frame];exact input.available
    valid := by rw [nodes];exact input.valid
    vacant := by rw [nodes];exact input.vacant
    parentSlack := by change input.depth.depth input.parent < read.tree.nodes.size;rw [nodes];exact input.parentSlack
    well := good.1
    bounds := by rw [good.2];exact input.bounds }
  have separated : earlier ≠ GeneralBorrowFreshMetadataChildMutableReuse.index next := by
    exact different
  have preserved := GeneralBorrowConstructorPriorPermissionRange.protected_reuse next earlier
    (some (.ReservedFrz true)) input.offset (input.offset+input.len) separated conflict.2
  exact ⟨conflict.1,preserved.1,preserved.2⟩

end DuplicatePrefix.GeneralBorrowProtectedOverlapConstructor
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowProtectedOverlapConstructor.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved protected chronology dependency {dependency}"
