import duplicate_prefix.GeneralBorrowRetainedMutableChain
import duplicate_prefix.GeneralBorrowFreshRestoreData
import duplicate_prefix.GeneralBorrowFreshPathExtension
namespace DuplicatePrefix.GeneralBorrowRetainedMutableAncestor
open Miri.DataStructures Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowRetainedMutableAccess GeneralBorrowRetainedMutableChain GeneralRangeMapOrigins
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
structure Row where
  index : UniIndex
  tag : BorTag
structure Handle (tree : BorrowTree) (current : UniIndex) (row : Row) : Prop where
  present : ∃node,tree.nodeAt row.index=some node
  lookup : tree.indexOfTag row.tag=some row.index
  subset : ∀location : LocationTree,∀position∈(source_normal_projection tree location {}).topology.ancestorPath row.index.toNat,
    position∈(source_normal_projection tree location {}).topology.ancestorPath current.toNat

theorem topology (before after : BorrowTree) (same : after.nodes=before.nodes) (location : LocationTree) :
    (source_normal_projection after location {}).topology=(source_normal_projection before location {}).topology := by
  unfold_general_projection
  unfold_general_topology
  rw [same]

theorem self {root offset len} (s : Current root offset len) : Handle s.state.tree s.index ⟨s.index,s.tag⟩ :=
  ⟨⟨s.state.node,s.state.present⟩,s.state.lookup,by intro location position member;exact member⟩

def select {root offset len} (s : Current root offset len) (row : Row) (held : Handle s.state.tree s.index row) : Current root offset len := by
  let node:=Classical.choose held.present
  have present:=Classical.choose_spec held.present
  have restore:=GeneralBorrowFreshRestoreData.from_paths s.state.tree {} {} s.index row.index node present held.subset
    (by intro location index node found localChild foreignTarget; rfl)
  have owned : OwnedOn (GeneralBorrowRange.LocationOwned s.state.tree {} row.index .Write) offset (offset+len) s.state.tree.locations := by
    apply GeneralBorrowFreshLifetimeRestore.restore_owned_on s.state.tree {} {} (fun _ h=>h) s.index row.index (fun _=>true) restore
    intro position valid positive start stop
    exact GeneralBorrowFreshMixedChild.write_combined s.state.tree _ {} s.index (s.state.owned position valid positive start stop)
  exact ⟨row.index,row.tag,{s.state with node:=node,present:=present,lookup:=held.lookup,owned:=owned}⟩

theorem access {root offset len} (s : Current root offset len) (row : Row) (held : Handle s.state.tree s.index row) (kind : AccessKind) :
    Handle (build s.state kind).state.tree s.index row := by
  have nodes:=GeneralBorrowRetainedMutableAccessFacts.build_nodes s.state kind
  have mapping:=GeneralBorrowRetainedMutableAccessFacts.build_mapping s.state kind
  refine ⟨?_,?_,?_⟩
  · obtain ⟨node,present⟩:=held.present
    exact ⟨node,by change (build s.state kind).state.tree.nodes.get row.index=some node;rw [nodes];exact present⟩
  · change (build s.state kind).state.tree.tagMapping.get row.tag=some row.index
    rw [mapping];exact held.lookup
  · intro location position member
    rw [topology s.state.tree _ nodes location] at member ⊢
    exact held.subset location position member

theorem activate {root offset len} (s : Current root offset len) (row : Row) (held : Handle s.state.tree s.index row)
    (tag : BorTag) (fresh : GeneralBorrowTagMap.Fresh s.state.tree.tagMapping tag) (positive : len≠0)
    (room : s.state.tree.nodes.size+5≤4294967295) :
    let output:=GeneralBorrowRetainedMutableActivate.build s.state tag fresh positive room
    Handle output.state.tree output.index row := by
  let d:=GeneralBorrowRetainedMutableReborrow.data s.state tag fresh positive
  let inside:=(GeneralBorrowFreshDefaultSequence.child d {}).tree
  let reserve:=GeneralBorrowSharedRootMutableReservation.build s.state.tree tag s.index offset len d s.state.owned s.state.resources.allocator s.state.resources.clean
  let output:=GeneralBorrowRetainedMutableActivate.build s.state tag fresh positive room
  have frame:=GeneralBorrowFreshReadFrame.frame inside (.concrete tag) (Size.ofBytes offset) (Size.ofBytes len) .Write {} .VisitChildrenOfAccessed
  change (GeneralBorrowRetainedMutableActivate.operation s.state tag fresh positive).tree={inside with locations:=(GeneralBorrowRetainedMutableActivate.operation s.state tag fresh positive).tree.locations} at frame
  have nodes : output.state.tree.nodes=inside.nodes := by rw [output.actual];simpa only using congrArg BorrowTree.nodes frame
  have mapping : output.state.tree.tagMapping=inside.tagMapping := by rw [output.actual];simpa only using congrArg BorrowTree.tagMapping frame
  obtain ⟨old,present⟩:=held.present
  obtain ⟨next,found,tagged,exposed⟩:=reserve.oldNode row.index old present
  have different : tag≠row.tag := by
    intro equal
    have absent : s.state.tree.indexOfTag tag=none := by
      unfold BorrowTree.indexOfTag UniKeyMap.get
      rw [GeneralBorrowTagMap.fresh_find s.state.tree.tagMapping tag fresh];rfl
    rw [equal,held.lookup] at absent
    cases absent
  refine ⟨⟨next,?_⟩,?_,?_⟩
  · change output.state.tree.nodes.get row.index=some next
    rw [nodes];exact found
  · change output.state.tree.tagMapping.get row.tag=some row.index
    rw [mapping];exact (reserve.oldLookup row.tag different).trans held.lookup
  · intro location position member
    rw [topology inside output.state.tree nodes location] at member ⊢
    have valid : row.index.toNat<(source_normal_projection s.state.tree location {}).topology.nodes.size := by
      have bound:=GeneralBorrowNodeUpdate.lookup_valid s.state.tree.nodes row.index old present
      unfold_general_projection
      unfold_general_topology
      simpa only [Array.size_map] using bound
    exact GeneralBorrowFreshPathExtension.subset _ _ _ _ _ (reserve.attach location) valid (held.subset location) position member

theorem activate_path {root offset len} (s : Current root offset len) (row : Row) (held : Handle s.state.tree s.index row)
    (tag : BorTag) (fresh : GeneralBorrowTagMap.Fresh s.state.tree.tagMapping tag) (positive : len≠0)
    (room : s.state.tree.nodes.size+5≤4294967295) :
    let output:=GeneralBorrowRetainedMutableActivate.build s.state tag fresh positive room
    ∀location : LocationTree,(source_normal_projection output.state.tree location {}).topology.ancestorPath row.index.toNat=
      (source_normal_projection s.state.tree location {}).topology.ancestorPath row.index.toNat := by
  let d:=GeneralBorrowRetainedMutableReborrow.data s.state tag fresh positive
  let inside:=(GeneralBorrowFreshDefaultSequence.child d {}).tree
  let reserve:=GeneralBorrowSharedRootMutableReservation.build s.state.tree tag s.index offset len d s.state.owned s.state.resources.allocator s.state.resources.clean
  let output:=GeneralBorrowRetainedMutableActivate.build s.state tag fresh positive room
  have frame:=GeneralBorrowFreshReadFrame.frame inside (.concrete tag) (Size.ofBytes offset) (Size.ofBytes len) .Write {} .VisitChildrenOfAccessed
  change (GeneralBorrowRetainedMutableActivate.operation s.state tag fresh positive).tree={inside with locations:=(GeneralBorrowRetainedMutableActivate.operation s.state tag fresh positive).tree.locations} at frame
  have nodes : output.state.tree.nodes=inside.nodes := by rw [output.actual];simpa only using congrArg BorrowTree.nodes frame
  obtain ⟨old,present⟩:=held.present
  change ∀location : LocationTree,(source_normal_projection output.state.tree location {}).topology.ancestorPath row.index.toNat=
      (source_normal_projection s.state.tree location {}).topology.ancestorPath row.index.toNat
  intro location
  rw [topology inside output.state.tree nodes location]
  have valid : row.index.toNat<(source_normal_projection s.state.tree location {}).topology.nodes.size := by
    have bound:=GeneralBorrowNodeUpdate.lookup_valid s.state.tree.nodes row.index old present
    unfold_general_projection
    unfold_general_topology
    simpa only [Array.size_map] using bound
  exact GeneralBorrowFreshPathExtension.target_path _ _ _ _ _ (reserve.attach location) valid (held.subset location)

end
end DuplicatePrefix.GeneralBorrowRetainedMutableAncestor
