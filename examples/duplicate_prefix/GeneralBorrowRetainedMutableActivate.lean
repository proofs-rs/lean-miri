import duplicate_prefix.GeneralBorrowRetainedMutableReborrowFacts
import duplicate_prefix.GeneralBorrowRetainedMutableAccessFacts
namespace DuplicatePrefix.GeneralBorrowRetainedMutableActivate
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowRetainedMutableAccess GeneralRangeMapOrigins GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

def operation {root child : UniIndex} {childTag : BorTag} {offset len : UInt64}
    (s : State root child childTag offset len) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh s.tree.tagMapping tag) (positive : len≠0) :=
  (GeneralBorrowFreshDefaultSequence.child (GeneralBorrowRetainedMutableReborrow.data s tag fresh positive) {}).tree.performNormalAccessRange
    tag (Size.ofBytes offset) (Size.ofBytes len) .Write {} .VisitChildrenOfAccessed

structure Output {root child : UniIndex} {childTag : BorTag} {offset len : UInt64}
    (s : State root child childTag offset len) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh s.tree.tagMapping tag) (positive : len≠0) where
  index : UniIndex
  state : State root index tag offset len
  actual : state.tree=(operation s tag fresh positive).tree
  readCompleted : (GeneralBorrowFreshDefaultSequence.read (GeneralBorrowRetainedMutableReborrow.data s tag fresh positive) {}).status=.Completed
  constructed : (GeneralBorrowFreshDefaultSequence.child (GeneralBorrowRetainedMutableReborrow.data s tag fresh positive) {}).outcome=.ok ()
  activated : (operation s tag fresh positive).status=.Completed
  path : ∀ location : LocationTree,(source_normal_projection state.tree location {}).topology.ancestorPath index.toNat =
    index.toNat :: (source_normal_projection s.tree location {}).topology.ancestorPath child.toNat
  growth : state.tree.nodes.size≤s.tree.nodes.size+1
  future : ∀ future,GeneralBorrowTagMap.Fresh s.tree.tagMapping future→tag≠future→GeneralBorrowTagMap.Fresh state.tree.tagMapping future

def build {root child : UniIndex} {childTag : BorTag} {offset len : UInt64}
    (s : State root child childTag offset len) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh s.tree.tagMapping tag) (positive : len≠0)
    (room : s.tree.nodes.size+5≤4294967295) : Output s tag fresh positive := by
  let d := GeneralBorrowRetainedMutableReborrow.data s tag fresh positive
  let inside := (GeneralBorrowFreshDefaultSequence.child d {}).tree
  let index := GeneralBorrowFreshDefaultSequence.index d
  have done := GeneralBorrowFreshDefaultSequence.run s.tree tag child offset len d {} s.owned
  let reserve := GeneralBorrowSharedRootMutableReservation.build s.tree tag child offset len d s.owned s.resources.allocator s.resources.clean
  let node := Classical.choose reserve.metadata.node
  have present := (Classical.choose_spec reserve.metadata.node).1
  have insideBounds : offset.toNat+len.toNat≤inside.locations.size.bytes.toNat := by rw [reserve.metadata.capacity];exact s.bounds
  let result := operation s tag fresh positive
  have facts := GeneralBorrowRangeLocal.access inside {} tag index root (Size.ofBytes offset) (Size.ofBytes len)
    .Write .Write .VisitChildrenOfAccessed (by intro impossible;cases impossible) reserve.metadata.nodeFits reserve.metadata.certificates.depth
    reserve.metadata.certificates.children node present reserve.metadata.roots reserve.metadata.certificates.covered reserve.metadata.lookup
    reserve.metadata.well offset (offset+len) done.2.2.1 insideBounds (Nat.le_refl _) (Nat.le_refl _)
  change result.status=.Completed ∧ OwnedOn (GeneralBorrowRange.LocationOwned result.tree {} index .Write) offset (offset+len) result.tree.locations ∧
    result.tree.locations.WellFormed ∧ result.tree.locations.size=inside.locations.size at facts
  have frame := GeneralBorrowFreshReadFrame.frame inside (.concrete tag) (Size.ofBytes offset) (Size.ofBytes len) .Write {} .VisitChildrenOfAccessed
  change result.tree={inside with locations:=result.tree.locations} at frame
  have nodes : result.tree.nodes=inside.nodes := by simpa only using congrArg BorrowTree.nodes frame
  have mapping : result.tree.tagMapping=inside.tagMapping := by simpa only using congrArg BorrowTree.tagMapping frame
  have clean : GeneralBorrowGcVacantClean.VacantClean result.tree := by
    intro query vacant
    have old : inside.nodes.get query=none := by rw [←nodes];exact vacant
    have kept := GeneralBorrowFreshActiveOnRange.ranged inside {} tag index root query (Size.ofBytes offset) (Size.ofBytes len)
      .Write .Write .VisitChildrenOfAccessed (by intro impossible;cases impossible) reserve.metadata.certificates.depth reserve.metadata.certificates.children
      node present reserve.metadata.roots reserve.metadata.certificates.covered reserve.metadata.lookup old (reserve.clean query old)
      reserve.metadata.well offset (offset+len) done.2.2.1 insideBounds (Nat.le_refl _) (Nat.le_refl _)
    exact kept.2
  have allocator : GeneralBorrowGcAllocator.Invariant result.tree := by
    rw [frame];exact ⟨reserve.allocator.pool,reserve.allocator.accounting,reserve.allocator.unique,reserve.allocator.nodeTags⟩
  have growth : result.tree.nodes.size≤s.tree.nodes.size+1 := by rw [nodes];exact reserve.size
  have path : ∀ location : LocationTree,(source_normal_projection result.tree location {}).topology.ancestorPath index.toNat =
      index.toNat :: (source_normal_projection s.tree location {}).topology.ancestorPath child.toNat := by
    intro location
    rw [frame]
    exact (reserve.attach location).childPath
  refine {
    index:=index,state:={
      tree:=result.tree,resources:={
        depth:=GeneralBorrowFreshReadFrame.depth_on inside result.tree nodes reserve.metadata.certificates.depth,
        children:=by rw [frame];exact reserve.metadata.certificates.children,
        covered:=by rw [frame];exact reserve.metadata.certificates.covered,
        roots:=by rw [frame];exact reserve.metadata.roots,
        allocator:=allocator,clean:=clean,well:=facts.2.2.1,room:=by omega },
      node:=node,present:=by change result.tree.nodes.get index=some node;rw [nodes];exact present,
      lookup:=by change result.tree.tagMapping.get tag=some index;rw [mapping];exact reserve.metadata.lookup,
      bounds:=by rw [facts.2.2.2];exact insideBounds,owned:=facts.2.1 },
    actual:=rfl,readCompleted:=done.1,constructed:=done.2.1,activated:=facts.1,path:=path,growth:=growth,future:=?_ }
  intro future unused different
  apply GeneralBorrowForestForeignSharedFresh.fresh_of_absent
  change result.tree.tagMapping.get future=none
  rw [mapping]
  have old := reserve.oldLookup future different
  have absent : s.tree.indexOfTag future=none := by
    unfold BorrowTree.indexOfTag UniKeyMap.get
    rw [GeneralBorrowTagMap.fresh_find s.tree.tagMapping future unused];rfl
  exact old.trans absent
end
end DuplicatePrefix.GeneralBorrowRetainedMutableActivate
