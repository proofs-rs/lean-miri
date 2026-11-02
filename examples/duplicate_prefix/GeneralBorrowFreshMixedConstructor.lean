import duplicate_prefix.GeneralBorrowFreshMixedInstallation
import duplicate_prefix.GeneralBorrowFreshSharedChild
namespace DuplicatePrefix.GeneralBorrowFreshMixedConstructor
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshAnchor DuplicatePrefix.GeneralBorrowNodeUpdate
open DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralBorrowFreshReleaseMixed
open DuplicatePrefix.GeneralBorrowFreshMixedChild
set_option maxRecDepth 65536
set_option maxHeartbeats 300000
/-- The actual Frozen shared constructor completes and makes the fresh
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
    (isProtected : Bool) (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (protections : ProtectedTags) (writable : Nat → Bool)
    (owned : OwnedOn (Combined tree protections parent writable)
      offset (offset+len) tree.locations) :
    let result := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) sharedState) (.Frozen) isProtected
    result.outcome = .ok () ∧
      OwnedOn (Combined result.tree protections
        ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
        (extend writable (⟨UInt32.ofNat tree.tagMapping.mapping.size⟩ : UniIndex).toNat)) offset (offset+len) result.tree.locations := by
  dsimp only
  refine ⟨GeneralBorrowFreshSharedChild.append_success tree depth parentTag newTag parent parentNode parentTagPresent parentPresent
    fresh noFree aligned fits isProtected offset len nonzero well bounds,?_⟩
  rw [GeneralBorrowFreshSharedChild.append_tree tree parentTag newTag parent parentNode parentTagPresent parentPresent
    fresh noFree aligned fits isProtected offset len nonzero well bounds]
  let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
  have atEnd : index.toNat = tree.nodes.data.size := by
    dsimp only [index,UniIndex.toNat]
    rw [UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega)]
    exact aligned
  apply GeneralBorrowFreshMixedShape.sifa_preserves
  have installed := GeneralBorrowFreshMixedInstallation.append_ranged_owned tree index parent parentNode newTag
    atEnd parentPresent (Size.ofBytes offset) (Size.ofBytes len) well bounds protections writable owned
  intro position valid positive start stop
  rw [GeneralBorrowFreshMixedShape.context_eq]
  rw [←GeneralBorrowFreshMixedShape.map_eq]
  exact installed position valid positive start stop

/-- The actual Frozen shared constructor completes and makes the fresh
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
    (isProtected : Bool) (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (protections : ProtectedTags) (writable : Nat → Bool)
    (owned : OwnedOn (Combined tree protections parent writable)
      offset (offset+len) tree.locations) :
    let result := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) sharedState) (.Frozen) isProtected
    result.outcome = .ok () ∧
      OwnedOn (Combined result.tree protections index (extend writable index.toNat)) offset (offset+len) result.tree.locations := by
  dsimp only
  refine ⟨GeneralBorrowFreshSharedChild.reuse_success tree depth parentTag newTag parent parentNode parentTagPresent parentPresent
    fresh index available indexBound vacant parentSlack isProtected offset len nonzero well bounds,?_⟩
  have returned : (tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) sharedState) (.Frozen) isProtected).tree =
      (sourceUpdateSifa
        {(GeneralBorrowFreshGraph.attached tree index parent parentNode (sharedNode newTag parent)) with
          tagMapping := {mapping := tree.tagMapping.mapping.push (newTag,index),deassigned := tree.tagMapping.deassigned.pop}
          locations := (tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len)
            (fun _ location => GeneralBorrowFreshMaterialization.materialized location index sharedState)).state}
        parent .Read).1 := by
    simpa only [GeneralBorrowFreshGraph.attached,GeneralBorrowFreshMaterialization.materialized] using
      GeneralBorrowFreshSharedChild.reuse_tree tree parentTag newTag parent parentNode parentTagPresent parentPresent
        fresh index available indexBound vacant isProtected offset len nonzero well bounds
  rw [returned]
  apply GeneralBorrowFreshMixedShape.sifa_preserves
  have installed := GeneralBorrowFreshMixedInstallation.reuse_ranged_owned tree index parent parentNode newTag
    indexBound vacant nodesFit parentPresent (Size.ofBytes offset) (Size.ofBytes len) well bounds protections writable owned
  intro position valid positive start stop
  rw [GeneralBorrowFreshMixedShape.context_eq]
  rw [←GeneralBorrowFreshMixedShape.map_eq]
  exact installed position valid positive start stop
end DuplicatePrefix.GeneralBorrowFreshMixedConstructor
#print axioms DuplicatePrefix.GeneralBorrowFreshMixedConstructor.append_owned
#print axioms DuplicatePrefix.GeneralBorrowFreshMixedConstructor.reuse_owned

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshMixedConstructor." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved mixed shared construction dependency {dependency}"
