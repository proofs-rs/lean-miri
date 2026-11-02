import duplicate_prefix.GeneralBorrowFreshMetadataChildSlot
namespace DuplicatePrefix.GeneralBorrowFreshMetadataChildAllocator
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

theorem fresh_push (mapping : UniKeyMap BorTag) (tag next : BorTag) (index : UniIndex) (pool : Array UniIndex)
    (fresh : GeneralBorrowTagMap.Fresh mapping next) (different : tag ≠ next) :
    GeneralBorrowTagMap.Fresh ⟨mapping.mapping.push (tag,index),pool⟩ next := by
  intro entry member
  simp only [Array.mem_push] at member
  rcases member with old | equal
  · exact fresh entry old
  · subst entry; exact different

theorem append_fresh (input : GeneralBorrowFreshMetadataChildShared.Input) (next : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh input.tree.tagMapping next) (different : input.newTag ≠ next) :
    GeneralBorrowTagMap.Fresh (GeneralBorrowFreshMetadataChildShared.result input).tagMapping next := by
  rw [(GeneralBorrowFreshMetadataChildShared.append input).mapping]
  exact fresh_push input.tree.tagMapping input.newTag next _ _ fresh different

theorem reuse_fresh (input : GeneralBorrowFreshMetadataChildSharedReuse.Input) (next : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh input.tree.tagMapping next) (different : input.newTag ≠ next) :
    GeneralBorrowTagMap.Fresh (GeneralBorrowFreshMetadataChildSharedReuse.result input).tagMapping next := by
  rw [(GeneralBorrowFreshMetadataChildSharedReuse.reuse input).mapping]
  exact fresh_push input.tree.tagMapping input.newTag next _ _ fresh different

/-- Two append allocations need two mapping slots; the first child's new parent
certificate and allocator state provide the second Slot without another hypothesis. -/
def next_append (input : GeneralBorrowFreshMetadataChildShared.Input)
    (room : input.tree.tagMapping.mapping.size+1 ≤ 4294967295) :
    GeneralBorrowFreshReborrowStages.Slot (GeneralBorrowFreshMetadataChildShared.result input)
      (GeneralBorrowFreshMetadataChildShared.append input).certificates.depth
      (GeneralBorrowFreshMetadataChildShared.index input) := by
  have data := GeneralBorrowFreshMetadataChildShared.append input
  apply GeneralBorrowFreshReborrowStages.Slot.append data.noFree data.aligned
  rw [data.mapping]
  simpa only [GeneralBorrowFreshMetadataChildShared.mapping,Array.size_push] using room

theorem topology_frame (before after : BorrowTree) (nodes : after.nodes = before.nodes)
    (oldLocation newLocation : LocationTree) (protections : ProtectedTags) :
    (source_normal_projection after newLocation protections).topology =
      (source_normal_projection before oldLocation protections).topology := by
  unfold_general_projection
  unfold_general_topology
  rw [nodes]
end DuplicatePrefix.GeneralBorrowFreshMetadataChildAllocator
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshMetadataChildAllocator." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved allocator metadata dependency {dependency}"
