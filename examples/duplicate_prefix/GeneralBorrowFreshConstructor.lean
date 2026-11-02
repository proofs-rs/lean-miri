import duplicate_prefix.GeneralBorrowFreshInstallation
import duplicate_prefix.GeneralBorrowFreshResult
namespace DuplicatePrefix.GeneralBorrowFreshConstructor
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshChild DuplicatePrefix.GeneralBorrowNodeUpdate
open DuplicatePrefix.GeneralRangeMapOrigins
set_option maxRecDepth 65536
set_option maxHeartbeats 300000

/-- The actual protected mutable constructor completes and makes the fresh
child own precisely the requested slice. This is the concrete-parent,
append-index case; arbitrary ownership outside the slice is allowed. The
parent forest/ownership history is supplied by the explicit input contract. -/
theorem mutable_owned (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (parentTagPresent : tree.tagMapping.get parentTag = some parent)
    (parentPresent : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag)
    (noFree : tree.tagMapping.deassigned.back? = none)
    (aligned : tree.tagMapping.mapping.size = tree.nodes.data.size)
    (fits : tree.tagMapping.mapping.size ≤ 4294967295)
    (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (protections : ProtectedTags) (kind : AccessKind)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned tree protections parent kind)
      offset (offset+len) tree.locations) :
    let result := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) inside) (.ReservedFrz false) true
    result.outcome = .ok () ∧
      OwnedOn (GeneralBorrowRange.LocationOwned result.tree protections
        ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩ kind) offset (offset+len) result.tree.locations := by
  dsimp only
  refine ⟨mutable_success tree depth parentTag newTag parent parentNode parentTagPresent parentPresent
    fresh noFree aligned fits offset len nonzero well bounds,?_⟩
  rw [GeneralBorrowFreshResult.mutable_tree tree parentTag newTag parent parentNode parentTagPresent parentPresent
    fresh noFree aligned fits offset len nonzero well bounds]
  let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
  have atEnd : index.toNat = tree.nodes.data.size := by
    dsimp only [index,UniIndex.toNat]
    rw [UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega)]
    exact aligned
  apply GeneralBorrowFreshOwnedOn.sifa_preserves
  have installed := GeneralBorrowFreshInstallation.ranged_owned tree index parent parentNode newTag
    atEnd parentPresent (Size.ofBytes offset) (Size.ofBytes len) well bounds protections kind owned
  intro position valid positive start stop
  rw [GeneralBorrowFreshInstallation.location_context_eq]
  rw [←GeneralBorrowFreshInstallation.location_map]
  exact installed position valid positive start stop
end DuplicatePrefix.GeneralBorrowFreshConstructor
#print axioms DuplicatePrefix.GeneralBorrowFreshConstructor.mutable_owned
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshConstructor." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved mutable constructor dependency {dependency}"
