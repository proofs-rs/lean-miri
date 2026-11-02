import duplicate_prefix.GeneralBorrowFreshDefaultStages
import duplicate_prefix.GeneralBorrowFreshDefaultTargetWithin
namespace DuplicatePrefix.GeneralBorrowFreshDefaultActivity
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralBorrowFreshReborrowStages DuplicatePrefix.GeneralBorrowFreshReadFrame
set_option maxRecDepth 65536
set_option maxHeartbeats 400000
set_option autoImplicit false in
/-- Preserve an older mutable anchor's strong activity through the real
unprotected Default-mode Read/constructor stage, from initial data only. -/
theorem preserves_target (tree : BorrowTree) (protections : ProtectedTags)
    (parentTag newTag : BorTag) (parent root : UniIndex) (parentNode : TreeNode)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (parentPresent : tree.nodeAt parent = some parentNode) (roots : tree.roots = #[root])
    (covered : GeneralBorrowGraph.RootsCover tree) (parentTagPresent : tree.indexOfTag parentTag = some parent)
    (tagFresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag)
    (nodeFits : tree.nodes.data.size ≤ 4294967296) (slot : Slot tree depth parent)
    (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned tree protections parent .Write) offset (offset+len) tree.locations)
    (target : UniIndex) (lower upper : UInt64)
    (requestLower : lower.toNat ≤ offset.toNat) (requestUpper : (offset+len).toNat ≤ upper.toNat)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree target .Write lower upper) :

    let read := tree.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len)
      .Read protections .VisitChildrenOfAccessed
    let child := read.tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false
    GeneralBorrowFreshActiveWithin.ActiveWithin child.tree target .Write lower upper := by

  let read := tree.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read protections .VisitChildrenOfAccessed
  have registeredOwners := owned
  have good := GeneralBorrowRangeLocal.access tree protections parentTag parent root (Size.ofBytes offset) (Size.ofBytes len)
    .Read .Write .VisitChildrenOfAccessed (fun _ => rfl) nodeFits depth children parentNode parentPresent roots covered parentTagPresent well
    offset (offset+len) registeredOwners bounds (Nat.le_refl _) (Nat.le_refl _)
  change read.status = .Completed ∧ OwnedOn (GeneralBorrowRange.LocationOwned read.tree protections parent .Write) offset (offset+len) read.tree.locations ∧
    read.tree.locations.WellFormed ∧ read.tree.locations.size = tree.locations.size at good
  have readActive : GeneralBorrowFreshActiveWithin.ActiveWithin read.tree target .Write lower upper :=
    GeneralBorrowFreshActiveWithinAccess.normal tree parentTag (Size.ofBytes offset) (Size.ofBytes len) .Read
      protections .VisitChildrenOfAccessed target lower upper well bounds requestLower requestUpper active
  have framed := GeneralBorrowFreshReadFrame.frame tree (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read protections .VisitChildrenOfAccessed
  have nodeEq := congrArg BorrowTree.nodes framed
  have nodes : read.tree.nodes = tree.nodes := nodeEq
  have tagEq := congrArg BorrowTree.tagMapping framed
  have tags : read.tree.tagMapping = tree.tagMapping := tagEq
  have parentAfter : read.tree.nodeAt parent = some parentNode := by
    change read.tree.nodes.get parent = some parentNode
    rw [nodes]
    exact parentPresent
  have parentTagAfter : read.tree.tagMapping.get parentTag = some parent := by rw [tags];exact parentTagPresent
  have freshAfter : GeneralBorrowTagMap.Fresh read.tree.tagMapping newTag := by rw [tags];exact tagFresh
  have boundsAfter : offset.toNat+len.toNat ≤ read.tree.locations.size.bytes.toNat := by rw [good.2.2.2];exact bounds
  dsimp only
  cases slot with
  | append noFree aligned fits =>
    have noFreeAfter : read.tree.tagMapping.deassigned.back? = none := by rw [tags];exact noFree
    have alignedAfter : read.tree.tagMapping.mapping.size = read.tree.nodes.data.size := by rw [tags,nodes];exact aligned
    have fitsIndex : read.tree.tagMapping.mapping.size ≤ 4294967295 := by rw [tags];exact fits
    exact GeneralBorrowFreshDefaultTargetWithin.append read.tree parentTag newTag parent parentNode parentTagAfter parentAfter
      freshAfter noFreeAfter alignedAfter fitsIndex offset len nonzero good.2.2.1 boundsAfter
      target lower upper requestLower requestUpper readActive
  | reuse candidate available bounded vacant slack =>
    have availableAfter : read.tree.tagMapping.deassigned.back? = some candidate := by rw [tags];exact available
    have boundedAfter : candidate.toNat < read.tree.nodes.data.size := by rw [nodes];exact bounded
    have vacantAfter : read.tree.nodes.get candidate = none := by rw [nodes];exact vacant
    exact GeneralBorrowFreshDefaultTargetWithin.reuse read.tree parentTag newTag parent parentNode parentTagAfter parentAfter
      freshAfter candidate availableAfter boundedAfter vacantAfter offset len nonzero good.2.2.1 boundsAfter
      target lower upper requestLower requestUpper readActive
set_option autoImplicit false in
/-- The complete Default-mode expression stage derives actual parent Read and
unprotected ReservedFrz constructor success together with the new child's
Write/strong profile and retention of an older target's strong profile. -/
theorem borrow (tree : BorrowTree) (protections : ProtectedTags)
    (parentTag newTag : BorTag) (parent root : UniIndex) (parentNode : TreeNode)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (parentPresent : tree.nodeAt parent = some parentNode) (roots : tree.roots = #[root])
    (covered : GeneralBorrowGraph.RootsCover tree) (parentTagPresent : tree.indexOfTag parentTag = some parent)
    (tagFresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag)
    (nodeFits : tree.nodes.data.size ≤ 4294967296) (slot : Slot tree depth parent)
    (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned tree protections parent .Write) offset (offset+len) tree.locations)
    (clean : Every (fun location : LocationTree => location.perms.get (GeneralBorrowFreshDefaultStages.slot_index slot) = none) tree.locations)
    (target : UniIndex) (lower upper : UInt64)
    (requestLower : lower.toNat ≤ offset.toNat) (requestUpper : (offset+len).toNat ≤ upper.toNat)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree target .Write lower upper) :

    let read := tree.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len)
      .Read protections .VisitChildrenOfAccessed
    let child := read.tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false
    read.status = .Completed ∧ child.outcome = .ok () ∧
      OwnedOn (GeneralBorrowRange.LocationOwned child.tree protections (GeneralBorrowFreshDefaultStages.slot_index slot) .Write)
        offset (offset+len) child.tree.locations ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin child.tree (GeneralBorrowFreshDefaultStages.slot_index slot) .Write offset (offset+len) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin child.tree target .Write lower upper := by
  have produced := GeneralBorrowFreshDefaultStages.borrow tree protections parentTag newTag parent root parentNode
    depth children parentPresent roots covered parentTagPresent tagFresh nodeFits slot offset len nonzero well bounds owned clean
  have preserved := preserves_target tree protections parentTag newTag parent root parentNode depth children
    parentPresent roots covered parentTagPresent tagFresh nodeFits slot offset len nonzero well bounds owned
    target lower upper requestLower requestUpper active
  exact ⟨produced.1,produced.2.1,produced.2.2.1,produced.2.2.2,preserved⟩
end DuplicatePrefix.GeneralBorrowFreshDefaultActivity
