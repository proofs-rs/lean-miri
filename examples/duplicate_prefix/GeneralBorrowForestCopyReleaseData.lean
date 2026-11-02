import duplicate_prefix.GeneralBorrowForestCopyInput
import duplicate_prefix.GeneralBorrowFreshActiveWithinAccess
import duplicate_prefix.GeneralBorrowFreshLifetimeRestore
import duplicate_prefix.GeneralBorrowFreshAnchor
import duplicate_prefix.GeneralBorrowForestMixedRestore

namespace DuplicatePrefix.GeneralBorrowForestCopyReleaseData
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralBorrowFreshActiveWithin DuplicatePrefix.GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

set_option autoImplicit false in
/-- Metadata and bytewise activity of the older mutable protector released by
root return. Copy ownership itself remains at its actual pointer anchor. -/
structure Input (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag)
    (offset len count : UInt64) where
  copy : GeneralBorrowForestCopyInput.Input tree protections tag offset len count
  target : UniIndex
  active : ActiveWithin tree target .Write offset (offset+len)
  targetContext : GeneralBorrowForestAccessData.Context tree target copy.primary copy.extras
  targetRootPath : ∀ location, ((source_normal_projection tree location protections).topology.ancestorPath target.toNat).getLast! = copy.primary.toNat
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
    OwnedOn (fun location => Nonempty (GeneralBorrowForestMutableAccess.Data write.tree location protections input.target input.copy.primary input.copy.extras)) offset (offset+len) write.tree.locations ∧
    ActiveWithin write.tree input.target .Write offset (offset+len) ∧
    GeneralBorrowFreshReleaseLoop.ActiveOn write.tree input.target .Write offset (offset+len) := by
  let read := tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes offset) (Size.ofBytes count) .Read protections .VisitChildrenOfAccessed
  let write := read.tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes (offset+count)) (Size.ofBytes count) .Write protections .VisitChildrenOfAccessed
  have ranges := arithmetic offset len count tree.locations.size.bytes input.copy.bounds input.copy.twice
  have first := GeneralBorrowForestMutableSlice.access tree protections tag input.copy.anchor input.copy.primary input.copy.extras
    (Size.ofBytes offset) (Size.ofBytes count) .Read .VisitChildrenOfAccessed
    input.copy.context input.copy.tagPresent input.copy.well input.copy.fits offset (offset+len) input.copy.owned ranges.1
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
  have copied := GeneralBorrowForestCopyBorrow.accesses tree protections tag input.copy.anchor input.copy.primary input.copy.extras
    offset len count input.copy.context input.copy.tagPresent input.copy.well input.copy.fits input.copy.bounds input.copy.twice input.copy.owned
    .VisitChildrenOfAccessed .VisitChildrenOfAccessed
  have restored : OwnedOn
      (fun location => Nonempty (GeneralBorrowForestMutableAccess.Data write.tree location protections input.target input.copy.primary input.copy.extras))
      offset (offset+len) write.tree.locations := by
    intro position valid positive start stop
    obtain ⟨data⟩ := copied.2.2.1 position valid positive start stop
    let mixed : GeneralBorrowForestMixedAccess.Data write.tree _ protections input.copy.anchor input.copy.primary input.copy.extras (fun _ => true) := {
      base := {
        forest := data.base.forest
        owned := GeneralBorrowFreshAnchor.anchor_readable _ _ data.base.owned
        rootPath := data.base.rootPath
        region := GeneralBorrowForestMutableAccess.region _ _ _ _ _ _ data .Read
        supported := data.base.supported
        foreignGraph := data.base.foreignGraph }
      mixed := by intro index bounded;exact data.base.owned.permissions index (by rw [←data.base.owned.locationsAligned];exact bounded)
      writeZero := data.base.region.zero }
    have path (location : LocationTree) : ((source_normal_projection write.tree location protections).topology.ancestorPath input.target.toNat).getLast! = input.copy.primary.toNat := by
      rw [same]
      exact input.targetRootPath _
    exact ⟨GeneralBorrowForestMixedRestore.restore write.tree _ protections protections (fun _ held => held)
      input.copy.anchor input.target input.copy.primary input.copy.extras (fun _ => true) restore (path _) mixed⟩
  exact ⟨same,restored,writeActive,
    active_on write.tree input.target .Write offset (offset+len) copied.2.2.2.1 writeActive⟩

end DuplicatePrefix.GeneralBorrowForestCopyReleaseData
open Lean Elab Command in
run_cmd do
  for dependency in (←collectAxioms ``DuplicatePrefix.GeneralBorrowForestCopyReleaseData.after_copy) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved generic copy-to-release data dependency {dependency}"
