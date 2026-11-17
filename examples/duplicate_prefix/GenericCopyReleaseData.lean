import duplicate_prefix.GenericCopyBorrow
import duplicate_prefix.GeneralBorrowFreshActiveWithinAccess
import duplicate_prefix.GeneralBorrowFreshLifetimeRestore
import duplicate_prefix.GeneralBorrowFreshAnchor

namespace DuplicatePrefix.GenericCopyReleaseData
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralBorrowFreshActiveWithin
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

set_option autoImplicit false in
/-- Metadata and bytewise activity of the older mutable protector released by
root return. Copy ownership itself remains at its actual pointer anchor. -/
structure Input (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag)
    (offset len count : UInt64) where
  copy : GenericCopyBorrow.Input tree protections tag offset len count
  target : UniIndex
  active : ActiveWithin tree target .Write offset (offset+len)
  restore : GeneralBorrowFreshLifetimeRestore.RestoreTo tree protections protections copy.anchor target (fun _ => true)

private theorem arithmetic (offset len count capacity : UInt64)
    (bounds : offset.toNat+len.toNat ≤ capacity.toNat) (twice : count.toNat+count.toNat ≤ len.toNat) :
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

private theorem combined (tree : BorrowTree) (protections : ProtectedTags) (anchor : UniIndex) (location : LocationTree)
    (owned : GeneralBorrowRange.LocationOwned tree protections anchor .Write location) :
    GeneralBorrowFreshReleaseMixed.Combined tree protections anchor (fun _ => true) location := by
  obtain ⟨forest,owner⟩ := owned
  refine ⟨⟨forest,GeneralBorrowFreshAnchor.anchor_readable _ _ owner⟩,?_⟩
  intro position valid
  exact owner.permissions position (by rw [←owner.locationsAligned];exact valid)

/-- Preserve bytewise activity through both actual copy accesses and restore
Write ownership of an arbitrary older mutable anchor from the all-Write contract. -/
theorem after_copy (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag)
    (offset len count : UInt64) (input : Input tree protections tag offset len count) :
    let read := tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes offset) (Size.ofBytes count) .Read protections .VisitChildrenOfAccessed
    let write := read.tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes (offset+count)) (Size.ofBytes count) .Write protections .VisitChildrenOfAccessed
    write.tree = {tree with locations := write.tree.locations} ∧
    OwnedOn (GeneralBorrowRange.LocationOwned write.tree protections input.target .Write) offset (offset+len) write.tree.locations ∧
    ActiveWithin write.tree input.target .Write offset (offset+len) ∧
    GeneralBorrowFreshReleaseLoop.ActiveOn write.tree input.target .Write offset (offset+len) := by
  let read := tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes offset) (Size.ofBytes count) .Read protections .VisitChildrenOfAccessed
  let write := read.tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes (offset+count)) (Size.ofBytes count) .Write protections .VisitChildrenOfAccessed
  have ranges := arithmetic offset len count tree.locations.size.bytes input.copy.bounds input.copy.twice
  have first := GeneralBorrowRangeLocal.access tree protections tag input.copy.anchor input.copy.root
    (Size.ofBytes offset) (Size.ofBytes count) .Read .Write .VisitChildrenOfAccessed
    (by intro impossible;cases impossible) input.copy.fits input.copy.depth input.copy.children input.copy.node input.copy.nodePresent
    input.copy.roots input.copy.covered input.copy.tagPresent input.copy.well offset (offset+len) input.copy.owned ranges.1
    (Nat.le_refl _) ranges.2.2.2.1
  have readSize : read.tree.locations.size = tree.locations.size := first.2.2.2
  have readActive := GeneralBorrowFreshActiveWithinAccess.normal tree tag (Size.ofBytes offset) (Size.ofBytes count) .Read
    protections .VisitChildrenOfAccessed input.target offset (offset+len) input.copy.well ranges.1
    (Nat.le_refl _) ranges.2.2.2.1 input.active
  have writeActive := GeneralBorrowFreshActiveWithinAccess.normal read.tree tag (Size.ofBytes (offset+count)) (Size.ofBytes count) .Write
    protections .VisitChildrenOfAccessed input.target offset (offset+len) first.2.2.1
    (by rw [readSize];exact ranges.2.1) ranges.2.2.1 ranges.2.2.2.2 readActive
  have readSame := GeneralBorrowFreshReadFrame.frame tree (.concrete tag) (Size.ofBytes offset) (Size.ofBytes count) .Read protections .VisitChildrenOfAccessed
  have writeSame := GeneralBorrowFreshReadFrame.frame read.tree (.concrete tag) (Size.ofBytes (offset+count)) (Size.ofBytes count) .Write protections .VisitChildrenOfAccessed
  have same : write.tree = {tree with locations := write.tree.locations} := by
    calc
      write.tree = {read.tree with locations := write.tree.locations} := writeSame
      _ = {tree with locations := write.tree.locations} := by rw [readSame]
  have restore : GeneralBorrowFreshLifetimeRestore.RestoreTo write.tree protections protections input.copy.anchor input.target (fun _ => true) := by
    rw [same]
    exact GeneralBorrowFreshLifetimeRestore.restore_map tree _ protections protections input.copy.anchor input.target _ input.restore
  have copied := GenericCopyBorrow.accesses tree protections tag offset len count input.copy
  have mixed : OwnedOn (GeneralBorrowFreshReleaseMixed.Combined write.tree protections input.copy.anchor (fun _ => true))
      offset (offset+len) write.tree.locations := by
    intro position valid positive start stop
    exact combined write.tree protections input.copy.anchor _ (copied.2.2.1 position valid positive start stop)
  exact ⟨same,GeneralBorrowFreshLifetimeRestore.restore_owned_on write.tree protections protections (fun _ held => held)
    input.copy.anchor input.target _ restore offset (offset+len) mixed,writeActive,
    active_on write.tree input.target .Write offset (offset+len) copied.2.2.2.1 writeActive⟩

end DuplicatePrefix.GenericCopyReleaseData
open Lean Elab Command in
run_cmd do
  for dependency in (←collectAxioms ``DuplicatePrefix.GenericCopyReleaseData.after_copy) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved generic copy-to-release data dependency {dependency}"
