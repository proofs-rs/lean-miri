import duplicate_prefix.GeneralBorrowRetainedMutableAccess
namespace DuplicatePrefix.GeneralBorrowRetainedMutableReborrow
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowRetainedMutableAccess GeneralRangeMapOrigins GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

def data {root child : UniIndex} {childTag : BorTag} {offset len : UInt64}
    (s : State root child childTag offset len) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh s.tree.tagMapping tag) (nonzero : len≠0) :
    GeneralBorrowFreshDefaultSequence.Data s.tree tag child offset len := by
  let d := entryData s tag fresh
  exact {
    parentTag:=childTag,root:=root,parentNode:=s.node,depth:=d.depth,children:=d.children,parentPresent:=s.present,
    roots:=s.resources.roots,covered:=d.covered,parentTagPresent:=s.lookup,tagFresh:=fresh,nodeFits:=d.nodeFits,
    slot:=d.slot,nonzero:=nonzero,well:=s.resources.well,bounds:=s.bounds,
    clean:=s.resources.clean _ (GeneralBorrowFreshDefaultStages.slot_vacant s.tree d.depth child d.slot) }

structure Output {root child : UniIndex} {childTag : BorTag} {offset len : UInt64}
    (s : State root child childTag offset len) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh s.tree.tagMapping tag) (nonzero : len≠0) where
  state : State root child childTag offset len
  actual : state.tree = (GeneralBorrowFreshDefaultSequence.child (data s tag fresh nonzero) {}).tree
  readCompleted : (GeneralBorrowFreshDefaultSequence.read (data s tag fresh nonzero) {}).status = .Completed
  constructed : (GeneralBorrowFreshDefaultSequence.child (data s tag fresh nonzero) {}).outcome = .ok ()

def build {root child : UniIndex} {childTag : BorTag} {offset len : UInt64}
    (s : State root child childTag offset len) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh s.tree.tagMapping tag) (nonzero : len≠0)
    (room : s.tree.nodes.size+5≤4294967295) : Output s tag fresh nonzero := by
  let d := data s tag fresh nonzero
  let result := GeneralBorrowFreshDefaultSequence.child d {}
  let index := GeneralBorrowFreshDefaultSequence.index d
  have done := GeneralBorrowFreshDefaultSequence.run s.tree tag child offset len d {} s.owned
  let reserve := GeneralBorrowSharedRootMutableReservation.build s.tree tag child offset len d s.owned s.resources.allocator s.resources.clean
  let info := reserve.oldNode child s.node s.present
  let node := Classical.choose info
  have present := (Classical.choose_spec info).1
  have restore : GeneralBorrowFreshLifetimeRestore.RestoreTo result.tree {} {} index child (fun _=>true) := by
    refine ⟨GeneralBorrowNodeUpdate.lookup_valid result.tree.nodes child node present,?_,?_⟩
    · intro location position localAccess
      have member : position∈(source_normal_projection result.tree location {}).topology.ancestorPath child.toNat := by
        unfold GeneralBorrowAnchor.relation at localAccess
        split at localAccess
        next member => exact member
        next => cases localAccess
      have attach := reserve.attach location
      have oldPath := attach.oldPath child.toNat attach.parentValid attach.parentDifferent
      rw [oldPath] at member
      refine ⟨?_,rfl⟩
      unfold GeneralBorrowAnchor.relation
      have inPath : position∈(source_normal_projection result.tree location {}).topology.ancestorPath index.toNat := by
        rw [attach.childPath]
        exact List.mem_cons_of_mem _ member
      simp only [inPath,ite_true]
    · intro location position sourceLocal targetForeign
      have empty : (source_normal_projection result.tree location {}).protectedNodes=[] := by
        unfold_general_projection
        simp [ProtectedTags.contains,ProtectedTags.get]
      rw [empty];rfl
  have owned : OwnedOn (GeneralBorrowRange.LocationOwned result.tree {} child .Write) offset (offset+len) result.tree.locations := by
    apply GeneralBorrowFreshLifetimeRestore.restore_owned_on result.tree {} {} (fun _ h=>h) index child (fun _=>true) restore
    intro position valid positive start stop
    exact GeneralBorrowFreshMixedChild.write_combined result.tree _ {} index (done.2.2.1 position valid positive start stop)
  have different : tag≠childTag := by
    intro same
    have absent : s.tree.indexOfTag tag=none := by
      unfold BorrowTree.indexOfTag UniKeyMap.get
      rw [GeneralBorrowTagMap.fresh_find s.tree.tagMapping tag fresh]
      rfl
    rw [same,s.lookup] at absent
    cases absent
  exact {
    state := {
      tree := result.tree
      resources := {
        depth:=reserve.metadata.certificates.depth,children:=reserve.metadata.certificates.children,
        covered:=reserve.metadata.certificates.covered,roots:=reserve.metadata.roots,allocator:=reserve.allocator,
        clean:=reserve.clean,well:=reserve.metadata.well,room:=by
          change (GeneralBorrowFreshDefaultSequence.child d {}).tree.nodes.size+4≤4294967295
          have size:=reserve.size
          omega }
      node := node
      present := present
      lookup := (reserve.oldLookup childTag different).trans s.lookup
      bounds := by rw [reserve.metadata.capacity];exact s.bounds
      owned := owned }
    actual := rfl
    readCompleted := done.1
    constructed := done.2.1 }
end
end DuplicatePrefix.GeneralBorrowRetainedMutableReborrow
