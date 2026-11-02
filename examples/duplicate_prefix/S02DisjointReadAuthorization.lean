import duplicate_prefix.S02DisjointReadFrame

namespace DuplicatePrefix.S02DisjointReadAuthorization
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapOrigins
open GeneralBorrowSnapshotWildcardRangeBoth (authorization_locations)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

private theorem row_locations (tree : BorrowTree) (locations : DedupRangeMap LocationTree)
    (location : LocationTree) (protections : ProtectedTags)
    (source selected : Option UniIndex) (maximum : Option BorTag)
    (row : Nonempty (DuplicatePrefixBorrowAuthorization.Row tree location protections source selected maximum)) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Row {tree with locations := locations}
      location protections source selected maximum) := by
  obtain ⟨row⟩ := row
  refine ⟨{
    wildcard := row.wildcard,rootPath := row.rootPath,rootPresent := row.rootPresent,
    cutoff := row.cutoff,normal := ?_,callbacks := ?_}⟩
  · intro anchor equal
    obtain ⟨normal⟩ := row.normal anchor equal
    exact ⟨{component := normal.component,permissions := normal.permissions}⟩
  · intro position valid different
    obtain ⟨support,read,write⟩ := row.callbacks position valid different
    exact ⟨support,authorization_locations tree locations location protections _ _ _ _ support read,
      authorization_locations tree locations location protections _ _ _ _ support write⟩

/-- Row authorization at a disjoint destination byte survives a concrete
source Read. The structural tree equality is the standard range-access frame
result, derivable from the existing concrete access contract. -/
theorem row (tree : BorrowTree) (tag : BorTag) (anchor : UniIndex)
    (tagPresent : tree.indexOfTag tag = some anchor)
    (offset len : Size) (protections : ProtectedTags) (mode : ChildrenVisitMode)
    (source selected : Option UniIndex) (maximum : Option BorTag)
    (lower upper : UInt64)
    (well : tree.locations.WellFormed)
    (bounds : offset.bytes.toNat + len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (outside : offset.bytes.toNat + len.bytes.toNat ≤ lower.toNat ∨
      upper.toNat ≤ offset.bytes.toNat)
    (owned : OwnedOn (fun location => Nonempty
      (DuplicatePrefixBorrowAuthorization.Row tree location protections source selected maximum))
      lower upper tree.locations)
    (treeEq : (tree.performBorrowAccessRange (.concrete tag) offset len .Read protections mode).tree =
      {tree with locations := (tree.performBorrowAccessRange (.concrete tag) offset len .Read protections mode).tree.locations}) :
    OwnedOn (fun location => Nonempty
      (DuplicatePrefixBorrowAuthorization.Row
        (tree.performBorrowAccessRange (.concrete tag) offset len .Read protections mode).tree
        location protections source selected maximum))
      lower upper
      (tree.performBorrowAccessRange (.concrete tag) offset len .Read protections mode).tree.locations := by
  have kept := S02DisjointReadFrame.concrete tree tag anchor tagPresent offset len .Read protections mode
    (fun location => Nonempty
      (DuplicatePrefixBorrowAuthorization.Row tree location protections source selected maximum))
    lower upper well bounds outside owned
  rw [treeEq]
  intro position valid positive beforeUpper afterLower
  exact row_locations tree _ _ protections source selected maximum
    (kept position valid positive beforeUpper afterLower)

end DuplicatePrefix.S02DisjointReadAuthorization

open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms ``DuplicatePrefix.S02DisjointReadAuthorization.row) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
