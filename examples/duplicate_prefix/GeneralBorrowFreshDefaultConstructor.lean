import duplicate_prefix.GeneralBorrowFreshDefaultInstallation
import duplicate_prefix.GeneralBorrowFreshDefaultChild
import duplicate_prefix.GeneralBorrowFreshOwnedOn
namespace DuplicatePrefix.GeneralBorrowFreshDefaultConstructor
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshDefaultChild DuplicatePrefix.GeneralBorrowNodeUpdate
open DuplicatePrefix.GeneralRangeMapOrigins
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
/-- The actual unprotected mutable-expression constructor completes and makes the fresh
child own precisely the requested slice. This is the concrete-parent,
append-index case; arbitrary ownership outside the slice is allowed. The
parent forest/ownership history is supplied by the explicit input contract. -/
theorem append_owned (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (parentTagPresent : tree.tagMapping.get parentTag = some parent)
    (parentPresent : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag)
    (noFree : tree.tagMapping.deassigned.back? = none)
    (aligned : tree.tagMapping.mapping.size = tree.nodes.data.size)
    (fits : tree.tagMapping.mapping.size ≤ 4294967295)
    (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (protections : ProtectedTags)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned tree protections parent .Write)
      offset (offset+len) tree.locations) :
    let result := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) inside) (.ReservedFrz false) false
    result.outcome = .ok () ∧
      OwnedOn (GeneralBorrowRange.LocationOwned result.tree protections
        ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩ .Write) offset (offset+len) result.tree.locations := by
  dsimp only
  refine ⟨GeneralBorrowFreshDefaultChild.append_success tree depth parentTag newTag parent parentNode parentTagPresent parentPresent
    fresh noFree aligned fits offset len nonzero well bounds,?_⟩
  rw [GeneralBorrowFreshDefaultChild.append_tree tree parentTag newTag parent parentNode parentTagPresent parentPresent
    fresh noFree aligned fits offset len nonzero well bounds]
  let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
  have atEnd : index.toNat = tree.nodes.data.size := by
    dsimp only [index,UniIndex.toNat]
    rw [UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega)]
    exact aligned
  apply GeneralBorrowFreshOwnedOn.sifa_preserves
  have installed := GeneralBorrowFreshDefaultInstallation.append_ranged_owned tree index parent parentNode newTag
    atEnd parentPresent (Size.ofBytes offset) (Size.ofBytes len) well bounds protections owned
  intro position valid positive start stop
  rw [GeneralBorrowFreshInstallation.location_context_eq]
  rw [←GeneralBorrowFreshInstallation.location_map]
  exact installed position valid positive start stop

/-- The actual unprotected mutable-expression constructor completes and makes the fresh
child own precisely the requested slice. This is the concrete-parent,
reusable-index case; arbitrary ownership outside the slice is allowed. The
parent forest/ownership history is supplied by the explicit input contract. -/
theorem reuse_owned (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (parentTagPresent : tree.tagMapping.get parentTag = some parent)
    (parentPresent : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag)
    (index : UniIndex) (available : tree.tagMapping.deassigned.back? = some index)
    (indexBound : index.toNat < tree.nodes.data.size) (vacant : tree.nodes.get index = none)
    (parentSlack : depth.depth parent < tree.nodes.size) (nodesFit : tree.nodes.data.size ≤ 4294967296)
    (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (protections : ProtectedTags)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned tree protections parent .Write)
      offset (offset+len) tree.locations) :
    let result := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) inside) (.ReservedFrz false) false
    result.outcome = .ok () ∧
      OwnedOn (GeneralBorrowRange.LocationOwned result.tree protections
        index .Write) offset (offset+len) result.tree.locations := by
  dsimp only
  refine ⟨GeneralBorrowFreshDefaultChild.reuse_success tree depth parentTag newTag parent parentNode parentTagPresent parentPresent
    fresh index available indexBound vacant parentSlack offset len nonzero well bounds,?_⟩
  have returned : (tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) inside) (.ReservedFrz false) false).tree =
      (sourceUpdateSifa
        {(GeneralBorrowFreshGraph.attached tree index parent parentNode (child newTag parent)) with
          tagMapping := {mapping := tree.tagMapping.mapping.push (newTag,index),deassigned := tree.tagMapping.deassigned.pop}
          locations := (tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len)
            (fun _ location => GeneralBorrowFreshMaterialization.materialized location index inside)).state}
        parent .Read).1 := by
    simpa only [GeneralBorrowFreshGraph.attached,GeneralBorrowFreshMaterialization.materialized] using
      GeneralBorrowFreshDefaultChild.reuse_tree tree parentTag newTag parent parentNode parentTagPresent parentPresent
        fresh index available indexBound vacant offset len nonzero well bounds
  rw [returned]
  apply GeneralBorrowFreshOwnedOn.sifa_preserves
  have installed := GeneralBorrowFreshDefaultInstallation.reuse_ranged_owned tree index parent parentNode newTag
    indexBound vacant nodesFit parentPresent (Size.ofBytes offset) (Size.ofBytes len) well bounds protections owned
  intro position valid positive start stop
  rw [GeneralBorrowFreshInstallation.location_context_eq]
  rw [←GeneralBorrowFreshInstallation.location_map]
  exact installed position valid positive start stop
end DuplicatePrefix.GeneralBorrowFreshDefaultConstructor
#print axioms DuplicatePrefix.GeneralBorrowFreshDefaultConstructor.append_owned
#print axioms DuplicatePrefix.GeneralBorrowFreshDefaultConstructor.reuse_owned
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshDefaultConstructor." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved frozen shared ownership dependency {dependency}"
