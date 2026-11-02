import duplicate_prefix.GeneralBorrowFreshReadFrame

namespace DuplicatePrefix.GenericCopyBorrow
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapOrigins
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

set_option autoImplicit false in
/-- Slice-local ownership and graph data for a real adjacent copy. No fixed
node count, canonical tree constructor or successful access is supplied. -/
structure Input (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag)
    (offset sliceLen count : UInt64) where
  anchor : UniIndex
  root : UniIndex
  fits : tree.nodes.data.size ≤ 4294967296
  depth : GeneralBorrowExposure.ParentDepth tree.nodes
  children : GeneralBorrowGraph.ChildNodes tree
  node : TreeNode
  nodePresent : tree.nodeAt anchor = some node
  roots : tree.roots = #[root]
  covered : GeneralBorrowGraph.RootsCover tree
  tagPresent : tree.indexOfTag tag = some anchor
  well : tree.locations.WellFormed
  bounds : offset.toNat+sliceLen.toNat ≤ tree.locations.size.bytes.toNat
  twice : count.toNat+count.toNat ≤ sliceLen.toNat
  owned : OwnedOn (GeneralBorrowRange.LocationOwned tree protections anchor .Write)
    offset (offset+sliceLen) tree.locations

private theorem arithmetic (offset len count capacity : UInt64)
    (bounds : offset.toNat+len.toNat ≤ capacity.toNat)
    (twice : count.toNat+count.toNat ≤ len.toNat) :
    offset.toNat+count.toNat ≤ capacity.toNat ∧
    (offset+count).toNat+count.toNat ≤ capacity.toNat ∧
    offset.toNat ≤ (offset+count).toNat ∧
    (offset+count).toNat ≤ (offset+len).toNat ∧
    ((offset+count)+count).toNat ≤ (offset+len).toNat := by
  have capacityFits : capacity.toNat < 2^64 := UInt64.toNat_lt_size capacity
  have fullFits : offset.toNat+len.toNat < 2^64 := by omega
  have firstFits : offset.toNat+count.toNat < 2^64 := by omega
  have secondFits : offset.toNat+count.toNat+count.toNat < 2^64 := by omega
  simp only [UInt64.toNat_add,Nat.mod_eq_of_lt fullFits,Nat.mod_eq_of_lt firstFits,Nat.mod_eq_of_lt secondFits]
  omega

/-- Source Read followed by destination Write both execute the real ranged
visitor and retain Write ownership over the original slice. -/
theorem accesses (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag)
    (offset sliceLen count : UInt64) (input : Input tree protections tag offset sliceLen count) :
    let read := tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes offset) (Size.ofBytes count)
      .Read protections .VisitChildrenOfAccessed
    let write := read.tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes (offset+count)) (Size.ofBytes count)
      .Write protections .VisitChildrenOfAccessed
    read.status = .Completed ∧ write.status = .Completed ∧
      OwnedOn (GeneralBorrowRange.LocationOwned write.tree protections input.anchor .Write)
        offset (offset+sliceLen) write.tree.locations ∧
      write.tree.locations.WellFormed ∧ write.tree.locations.size = tree.locations.size := by
  let read := tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes offset) (Size.ofBytes count)
    .Read protections .VisitChildrenOfAccessed
  let write := read.tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes (offset+count)) (Size.ofBytes count)
    .Write protections .VisitChildrenOfAccessed
  have ranges := arithmetic offset sliceLen count tree.locations.size.bytes input.bounds input.twice
  have first := GeneralBorrowRangeLocal.access tree protections tag input.anchor input.root
    (Size.ofBytes offset) (Size.ofBytes count) .Read .Write .VisitChildrenOfAccessed
    (by intro impossible;cases impossible) input.fits input.depth input.children input.node input.nodePresent
    input.roots input.covered input.tagPresent input.well offset (offset+sliceLen) input.owned ranges.1
    (Nat.le_refl _) ranges.2.2.2.1
  have same := GeneralBorrowFreshReadFrame.frame tree (.concrete tag) (Size.ofBytes offset) (Size.ofBytes count)
    .Read protections .VisitChildrenOfAccessed
  change read.tree = {tree with locations := read.tree.locations} at same
  have nodes : read.tree.nodes = tree.nodes := congrArg (fun tree => tree.nodes) same
  have nextDepth := GeneralBorrowFreshReadFrame.depth_on tree read.tree nodes input.depth
  have children : GeneralBorrowGraph.ChildNodes read.tree := by rw [same];exact input.children
  have covered : GeneralBorrowGraph.RootsCover read.tree := by rw [same];exact input.covered
  have nodePresent : read.tree.nodeAt input.anchor = some input.node := by rw [same];exact input.nodePresent
  have roots : read.tree.roots = #[input.root] := by rw [same];exact input.roots
  have tagPresent : read.tree.indexOfTag tag = some input.anchor := by rw [same];exact input.tagPresent
  have fits : read.tree.nodes.data.size ≤ 4294967296 := by rw [nodes];exact input.fits
  have readSize : read.tree.locations.size = tree.locations.size := first.2.2.2
  have second := GeneralBorrowRangeLocal.access read.tree protections tag input.anchor input.root
    (Size.ofBytes (offset+count)) (Size.ofBytes count) .Write .Write .VisitChildrenOfAccessed
    (by intro impossible;cases impossible) fits nextDepth children input.node nodePresent roots covered tagPresent
    first.2.2.1 offset (offset+sliceLen) first.2.1
    (by rw [readSize];exact ranges.2.1) ranges.2.2.1 ranges.2.2.2.2
  exact ⟨first.1,second.1,second.2.1,second.2.2.1,second.2.2.2.trans first.2.2.2⟩

end DuplicatePrefix.GenericCopyBorrow
open Lean Elab Command in
run_cmd do
  for dependency in (←collectAxioms ``DuplicatePrefix.GenericCopyBorrow.accesses) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved generic copy borrow dependency {dependency}"
