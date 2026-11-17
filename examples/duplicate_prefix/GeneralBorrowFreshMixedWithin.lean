import duplicate_prefix.GeneralBorrowFreshMixedConstructor
import duplicate_prefix.GeneralBorrowFreshActiveWithin
namespace DuplicatePrefix.GeneralBorrowFreshMixedWithin
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshAnchor DuplicatePrefix.GeneralBorrowNodeUpdate
open DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralBorrowFreshReleaseMixed
open DuplicatePrefix.GeneralBorrowFreshMixedChild DuplicatePrefix.GeneralBorrowFreshMaterialization
set_option maxRecDepth 65536
set_option maxHeartbeats 300000

private theorem modified_sifa (tree : BorrowTree) (index parent : UniIndex) (offset len : Size)
    (well : tree.locations.WellFormed) (bounds : offset.bytes.toNat+len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (clean : ∀ position (valid : position < tree.locations.entries.size), tree.locations.entries[position].data.perms.get index = none) :
    GeneralBorrowFreshActiveWithin.ActiveWithin
      (sourceUpdateSifa {tree with locations := (tree.locations.modifyRange offset len (fun _ location => materialized location index sharedState)).state}
        parent .Read).1 index .Read offset.bytes (offset.bytes+len.bytes) := by
  have active := GeneralBorrowFreshActiveWithin.modified tree index offset len well bounds clean
  exact GeneralBorrowFreshActiveWithin.sifa_preserves
    {tree with locations := (tree.locations.modifyRange offset len (fun _ location => materialized location index sharedState)).state}
    parent .Read index .Read offset.bytes (offset.bytes+len.bytes) active

theorem append (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (parentTagPresent : tree.tagMapping.get parentTag = some parent) (parentPresent : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag)
    (noFree : tree.tagMapping.deassigned.back? = none) (aligned : tree.tagMapping.mapping.size = tree.nodes.data.size)
    (fits : tree.tagMapping.mapping.size ≤ 4294967295) (isProtected : Bool)
    (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (protections : ProtectedTags) (writable : Nat → Bool)
    (owned : OwnedOn (Combined tree protections parent writable) offset (offset+len) tree.locations)
    (clean : ∀ position (valid : position < tree.locations.entries.size),
      tree.locations.entries[position].data.perms.get ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩ = none) :
    let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
    let result := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) sharedState) .Frozen isProtected
    result.outcome = .ok () ∧
      OwnedOn (Combined result.tree protections index (extend writable index.toNat)) offset (offset+len) result.tree.locations ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin result.tree index .Read offset (offset+len) := by
  dsimp only
  have constructed := GeneralBorrowFreshMixedConstructor.append_owned tree depth parentTag newTag parent parentNode
    parentTagPresent parentPresent fresh noFree aligned fits isProtected offset len nonzero well bounds protections writable owned
  refine ⟨constructed.1,constructed.2,?_⟩
  rw [GeneralBorrowFreshSharedChild.append_tree tree parentTag newTag parent parentNode parentTagPresent parentPresent
    fresh noFree aligned fits isProtected offset len nonzero well bounds]
  let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
  let base : BorrowTree := {(GeneralBorrowFreshGraph.attached tree index parent parentNode (sharedNode newTag parent)) with
    tagMapping := ⟨tree.tagMapping.mapping.push (newTag,index),tree.tagMapping.deassigned⟩}
  have wellBase : base.locations.WellFormed := by
    dsimp only [base,GeneralBorrowFreshGraph.attached]
    exact well
  have boundsBase : offset.toNat+len.toNat ≤ base.locations.size.bytes.toNat := by
    dsimp only [base,GeneralBorrowFreshGraph.attached]
    exact bounds
  have cleanBase : ∀ position (valid : position < base.locations.entries.size), base.locations.entries[position].data.perms.get index = none := by
    dsimp only [base,GeneralBorrowFreshGraph.attached]
    exact clean
  have active := modified_sifa base index parent (Size.ofBytes offset) (Size.ofBytes len) wellBase boundsBase cleanBase
  simpa only [base,index,materialized,GeneralBorrowFreshGraph.attached,Size.ofBytes] using active

theorem reuse (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (parentTagPresent : tree.tagMapping.get parentTag = some parent) (parentPresent : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag)
    (index : UniIndex) (available : tree.tagMapping.deassigned.back? = some index)
    (indexBound : index.toNat < tree.nodes.data.size) (vacant : tree.nodes.get index = none)
    (parentSlack : depth.depth parent < tree.nodes.size) (nodesFit : tree.nodes.data.size ≤ 4294967296)
    (isProtected : Bool) (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (protections : ProtectedTags) (writable : Nat → Bool)
    (owned : OwnedOn (Combined tree protections parent writable) offset (offset+len) tree.locations)
    (clean : ∀ position (valid : position < tree.locations.entries.size), tree.locations.entries[position].data.perms.get index = none) :
    let result := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) sharedState) .Frozen isProtected
    result.outcome = .ok () ∧
      OwnedOn (Combined result.tree protections index (extend writable index.toNat)) offset (offset+len) result.tree.locations ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin result.tree index .Read offset (offset+len) := by
  dsimp only
  have constructed := GeneralBorrowFreshMixedConstructor.reuse_owned tree depth parentTag newTag parent parentNode
    parentTagPresent parentPresent fresh index available indexBound vacant parentSlack nodesFit isProtected offset len nonzero well bounds protections writable owned
  refine ⟨constructed.1,constructed.2,?_⟩
  have returned : (tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) sharedState) .Frozen isProtected).tree =
      (sourceUpdateSifa
        {(GeneralBorrowFreshGraph.attached tree index parent parentNode (sharedNode newTag parent)) with
          tagMapping := ⟨tree.tagMapping.mapping.push (newTag,index),tree.tagMapping.deassigned.pop⟩
          locations := (tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len)
            (fun _ location => materialized location index sharedState)).state} parent .Read).1 := by
    simpa only [GeneralBorrowFreshGraph.attached,materialized] using GeneralBorrowFreshSharedChild.reuse_tree tree
      parentTag newTag parent parentNode parentTagPresent parentPresent fresh index available indexBound vacant isProtected offset len nonzero well bounds
  rw [returned]
  let base : BorrowTree := {(GeneralBorrowFreshGraph.attached tree index parent parentNode (sharedNode newTag parent)) with
    tagMapping := ⟨tree.tagMapping.mapping.push (newTag,index),tree.tagMapping.deassigned.pop⟩}
  have wellBase : base.locations.WellFormed := by
    dsimp only [base,GeneralBorrowFreshGraph.attached]
    exact well
  have boundsBase : offset.toNat+len.toNat ≤ base.locations.size.bytes.toNat := by
    dsimp only [base,GeneralBorrowFreshGraph.attached]
    exact bounds
  have cleanBase : ∀ position (valid : position < base.locations.entries.size), base.locations.entries[position].data.perms.get index = none := by
    dsimp only [base,GeneralBorrowFreshGraph.attached]
    exact clean
  have active := modified_sifa base index parent (Size.ofBytes offset) (Size.ofBytes len) wellBase boundsBase cleanBase
  simpa only [base,materialized,GeneralBorrowFreshGraph.attached,Size.ofBytes] using active
end DuplicatePrefix.GeneralBorrowFreshMixedWithin
#print axioms DuplicatePrefix.GeneralBorrowFreshMixedWithin.append
#print axioms DuplicatePrefix.GeneralBorrowFreshMixedWithin.reuse

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshMixedWithin." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved shared lifetime preparation dependency {dependency}"
