import duplicate_prefix.GeneralBorrowFreshReuseInstallation
import duplicate_prefix.GeneralBorrowFreshReuseChild
import duplicate_prefix.GeneralBorrowFreshOwnedOn
namespace DuplicatePrefix.GeneralBorrowFreshReuseConstructor
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshChild DuplicatePrefix.GeneralBorrowNodeUpdate
open DuplicatePrefix.GeneralRangeMapOrigins
set_option maxRecDepth 65536
set_option maxHeartbeats 300000

/-- The actual protected mutable constructor completes and makes the fresh
child own precisely the requested slice. This is the concrete-parent,
reusable-index case; arbitrary ownership outside the slice is allowed. The
parent forest/ownership history is supplied by the explicit input contract. -/
theorem mutable_owned (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (parentTagPresent : tree.tagMapping.get parentTag = some parent)
    (parentPresent : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag)
    (index : UniIndex) (available : tree.tagMapping.deassigned.back? = some index)
    (indexBound : index.toNat < tree.nodes.data.size) (vacant : tree.nodes.get index = none)
    (parentSlack : depth.depth parent < tree.nodes.size) (nodesFit : tree.nodes.data.size ≤ 4294967296)
    (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (protections : ProtectedTags) (kind : AccessKind)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned tree protections parent kind)
      offset (offset+len) tree.locations) :
    let result := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) inside) (.ReservedFrz false) true
    result.outcome = .ok () ∧
      OwnedOn (GeneralBorrowRange.LocationOwned result.tree protections
        index kind) offset (offset+len) result.tree.locations := by
  dsimp only
  refine ⟨GeneralBorrowFreshReuseChild.mutable_success tree depth parentTag newTag parent parentNode parentTagPresent parentPresent
    fresh index available indexBound vacant parentSlack offset len nonzero well bounds,?_⟩
  have returned : (tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) inside) (.ReservedFrz false) true).tree =
      (sourceUpdateSifa
        {(GeneralBorrowFreshGraph.attached tree index parent parentNode (child newTag parent)) with
          tagMapping := {mapping := tree.tagMapping.mapping.push (newTag,index),deassigned := tree.tagMapping.deassigned.pop}
          locations := (tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len)
            (fun _ location => GeneralBorrowFreshMaterialization.materialized location index inside)).state}
        parent .None).1 := by
    simpa only [GeneralBorrowFreshGraph.attached,GeneralBorrowFreshMaterialization.materialized] using
      GeneralBorrowFreshReuseChild.mutable_tree tree parentTag newTag parent parentNode parentTagPresent parentPresent
        fresh index available indexBound vacant offset len nonzero well bounds
  rw [returned]
  apply GeneralBorrowFreshOwnedOn.sifa_preserves
  have installed := GeneralBorrowFreshReuseInstallation.ranged_owned tree index parent parentNode newTag
    indexBound vacant nodesFit parentPresent (Size.ofBytes offset) (Size.ofBytes len) well bounds protections kind owned
  intro position valid positive start stop
  rw [GeneralBorrowFreshInstallation.location_context_eq]
  rw [←GeneralBorrowFreshInstallation.location_map]
  exact installed position valid positive start stop
end DuplicatePrefix.GeneralBorrowFreshReuseConstructor
#print axioms DuplicatePrefix.GeneralBorrowFreshReuseConstructor.mutable_owned

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshReuseConstructor." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved reusable ownership dependency {dependency}"
