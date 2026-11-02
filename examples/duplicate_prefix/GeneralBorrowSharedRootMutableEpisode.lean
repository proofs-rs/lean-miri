import duplicate_prefix.GeneralBorrowSharedRootMutableReservation
import duplicate_prefix.GeneralBorrowSharedRootBankState
import duplicate_prefix.GeneralBorrowFreshLifetimeRestore
import duplicate_prefix.GeneralBorrowForestForeignSharedFresh
namespace DuplicatePrefix.GeneralBorrowSharedRootMutableEpisode
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralBorrowProjection GeneralRangeMapOrigins GeneralBorrowFreshReleaseMixed GeneralBorrowSharedRootLabel
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

def read {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len) :=
  s.bank.tree.performNormalAccessRange rootTag (Size.ofBytes offset) (Size.ofBytes len) .Read {} .VisitChildrenOfAccessed

def reservation {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len) (tag : BorTag) :=
  (read s).tree.newChild (Size.ofBytes offset) (.concrete rootTag) tag
    (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false

def operation {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len) (tag : BorTag) :=
  (reservation s tag).tree.performNormalAccessRange tag (Size.ofBytes offset) (Size.ofBytes len) .Write {} .VisitChildrenOfAccessed

def Completed {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len) (tag : BorTag) : Prop :=
  (read s).status = .Completed ∧ (reservation s tag).outcome = .ok () ∧ (operation s tag).status = .Completed

def supplied {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh s.bank.tree.tagMapping tag) (nonzero : len≠0) :
    GeneralBorrowFreshDefaultSequence.Data s.bank.tree tag root offset len := by
  let d := GeneralBorrowSharedRootBankState.entryData s tag fresh
  exact {
    parentTag:=rootTag,root:=root,parentNode:=d.node,depth:=d.depth,children:=d.children,parentPresent:=d.parentPresent,
    roots:=s.bank.resources.roots,covered:=d.covered,parentTagPresent:=d.tagPresent,tagFresh:=fresh,nodeFits:=d.nodeFits,
    slot:=d.slot,nonzero:=nonzero,well:=s.bank.resources.well,bounds:=s.bank.bounds,
    clean:=s.bank.resources.clean _ (GeneralBorrowFreshDefaultStages.slot_vacant s.bank.tree d.depth root d.slot) }

private theorem combined (tree : BorrowTree) (location : LocationTree) (root : UniIndex)
    (owned : GeneralBorrowRange.LocationOwned tree {} root .Write location) : Combined tree {} root (writable root) location := by
  have read := (GeneralBorrowFreshMixedChild.write_combined tree location {} root owned).1
  refine ⟨read,?_⟩
  intro position valid
  by_cases same : position=root.toNat
  · obtain ⟨state,present,permission⟩:=owned.2.permissions position (by rw[←owned.2.locationsAligned];exact valid)
    exact ⟨state,present,by simpa [GeneralBorrowPermissions.Required,GeneralBorrowPermissions.AccessOwned,writable,same] using permission⟩
  · obtain ⟨state,present,permission⟩:=read.2.permissions position (by rw[←read.2.locationsAligned];exact valid)
    exact ⟨state,present,by simpa [GeneralBorrowPermissions.Required,GeneralBorrowPermissions.AccessOwned,writable,same] using permission⟩

structure Output {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len) (tag : BorTag) where
  state : GeneralBorrowSharedRootBankState.State root rootTag offset len
  actual : state.bank.tree = (operation s tag).tree
  handles : state.bank.handles = [root]
  completed : Completed s tag
  growth : (operation s tag).tree.nodes.size ≤ s.bank.tree.nodes.size+1
  fresh : ∀ future, GeneralBorrowTagMap.Fresh s.bank.tree.tagMapping future → tag≠future →
    GeneralBorrowTagMap.Fresh (operation s tag).tree.tagMapping future
  child : ∃ index node, (operation s tag).tree.nodeAt index=some node ∧ node.tag=tag

/-- One actual root Read, unprotected Default reservation and child-tag Write
rebuilds a root-selectable bank. All old nodes remain physical; every old shared
handle is retired from the selectable bank after activation. Append/reuse,
exposed-root data, allocator coherence and vacant Clean are preserved internally. -/
def build {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh s.bank.tree.tagMapping tag) (nonzero : len≠0)
    (room : s.bank.tree.nodes.size+5≤4294967295) : Output s tag := by
  let d := supplied s tag fresh nonzero
  let initial := GeneralBorrowSharedRootBankState.entryData s tag fresh
  have rootOwned : OwnedOn (GeneralBorrowRange.LocationOwned s.bank.tree {} root .Write) offset (offset+len) s.bank.tree.locations := initial.owned
  have constructed := GeneralBorrowFreshDefaultSequence.run s.bank.tree tag root offset len d {} rootOwned
  let reserve := GeneralBorrowSharedRootMutableReservation.build s.bank.tree tag root offset len d rootOwned s.bank.resources.allocator s.bank.resources.clean
  let inside := (reservation s tag).tree
  let child := GeneralBorrowFreshDefaultSequence.index d
  let childNode := Classical.choose reserve.metadata.node
  have childPresent := (Classical.choose_spec reserve.metadata.node).1
  have childTag := (Classical.choose_spec reserve.metadata.node).2.1
  have childUnexposed := (Classical.choose_spec reserve.metadata.node).2.2
  have insideRoot : inside.roots = #[root] := reserve.metadata.roots
  have insideCapacity : inside.locations.size=s.bank.tree.locations.size := reserve.metadata.capacity
  have insideBounds : offset.toNat+len.toNat≤inside.locations.size.bytes.toNat := by rw[insideCapacity];exact s.bank.bounds
  have activated := GeneralBorrowRangeLocal.access inside {} tag child root (Size.ofBytes offset) (Size.ofBytes len)
    .Write .Write .VisitChildrenOfAccessed (by intro impossible;cases impossible) reserve.metadata.nodeFits reserve.metadata.certificates.depth
    reserve.metadata.certificates.children childNode childPresent insideRoot reserve.metadata.certificates.covered reserve.metadata.lookup
    reserve.metadata.well offset (offset+len) constructed.2.2.1 insideBounds (Nat.le_refl _) (Nat.le_refl _)
  let final := operation s tag
  change final.status = .Completed ∧ OwnedOn (GeneralBorrowRange.LocationOwned final.tree {} child .Write) offset (offset+len) final.tree.locations ∧
    final.tree.locations.WellFormed ∧ final.tree.locations.size=inside.locations.size at activated
  have frame := GeneralBorrowFreshReadFrame.frame inside (.concrete tag) (Size.ofBytes offset) (Size.ofBytes len) .Write {} .VisitChildrenOfAccessed
  change final.tree={inside with locations:=final.tree.locations} at frame
  have nodes : final.tree.nodes=inside.nodes := by simpa only using congrArg BorrowTree.nodes frame
  have mapping : final.tree.tagMapping=inside.tagMapping := by simpa only using congrArg BorrowTree.tagMapping frame
  have roots : final.tree.roots=inside.roots := by simpa only using congrArg BorrowTree.roots frame
  let rootInfo := reserve.oldNode root d.parentNode d.parentPresent
  let rootNode := Classical.choose rootInfo
  have rootPresent := (Classical.choose_spec rootInfo).1
  have rootTagEq := (Classical.choose_spec rootInfo).2.1
  have rootExposed := (Classical.choose_spec rootInfo).2.2
  have originalTag : d.parentNode.tag=rootTag := (Classical.choose_spec s.rootPresent).2
  have rootPresentFinal : final.tree.nodeAt root=some rootNode := by change final.tree.nodes.get root=_;rw[nodes];exact rootPresent
  have rootPathInside (location : LocationTree) : (source_normal_projection inside location {}).topology.ancestorPath root.toNat=[root.toNat] := by
    have attach:=reserve.attach location
    exact (attach.oldPath root.toNat attach.parentValid attach.parentDifferent).trans (s.rootPath location)
  have rootPath (location : LocationTree) : (source_normal_projection final.tree location {}).topology.ancestorPath root.toNat=[root.toNat] := by
    rw[frame];exact rootPathInside location
  have ancestor (location : LocationTree) : root.toNat∈(source_normal_projection final.tree location {}).topology.ancestorPath child.toNat := by
    rw[frame]
    change root.toNat∈(source_normal_projection inside location {}).topology.ancestorPath child.toNat
    have path : (source_normal_projection inside location {}).topology.ancestorPath child.toNat =
        child.toNat :: (source_normal_projection s.bank.tree location {}).topology.ancestorPath root.toNat := (reserve.attach location).childPath
    rw[path,s.rootPath location]
    simp
  have restore : GeneralBorrowFreshLifetimeRestore.RestoreTo final.tree {} {} child root (fun _=>true) := by
    refine ⟨GeneralBorrowNodeUpdate.lookup_valid final.tree.nodes root rootNode rootPresentFinal,?_,?_⟩
    · intro location position localAccess
      have member : position∈(source_normal_projection final.tree location {}).topology.ancestorPath root.toNat := by
        unfold GeneralBorrowAnchor.relation at localAccess
        split at localAccess
        next member => exact member
        next => cases localAccess
      rw[rootPath location] at member
      have same : position=root.toNat := List.mem_singleton.mp member
      subst position
      refine ⟨?_,rfl⟩
      unfold GeneralBorrowAnchor.relation
      simp only [ancestor location,ite_true]
    · intro location position sourceLocal targetForeign
      have empty : (source_normal_projection final.tree location {}).protectedNodes=[] := by
        unfold_general_projection
        simp [ProtectedTags.contains,ProtectedTags.get]
      rw[empty];rfl
  have finalRootOwned : OwnedOn (GeneralBorrowRange.LocationOwned final.tree {} root .Write) offset (offset+len) final.tree.locations := by
    apply GeneralBorrowFreshLifetimeRestore.restore_owned_on final.tree {} {} (fun _ h=>h) child root (fun _=>true) restore
    intro position valid positive start stop
    exact GeneralBorrowFreshMixedChild.write_combined final.tree _ {} child (activated.2.1 position valid positive start stop)
  have finalClean : GeneralBorrowGcVacantClean.VacantClean final.tree := by
    intro query vacant
    have oldVacant : inside.nodes.get query=none := by rw[←nodes];exact vacant
    have preserved := GeneralBorrowFreshActiveOnRange.ranged inside {} tag child root query (Size.ofBytes offset) (Size.ofBytes len)
      .Write .Write .VisitChildrenOfAccessed (by intro impossible;cases impossible) reserve.metadata.certificates.depth reserve.metadata.certificates.children
      childNode childPresent insideRoot reserve.metadata.certificates.covered reserve.metadata.lookup oldVacant (reserve.clean query oldVacant)
      reserve.metadata.well offset (offset+len) constructed.2.2.1 insideBounds (Nat.le_refl _) (Nat.le_refl _)
    exact preserved.2
  have nextAllocator : GeneralBorrowGcAllocator.Invariant final.tree := by
    rw[frame]
    exact ⟨reserve.allocator.pool,reserve.allocator.accounting,reserve.allocator.unique,reserve.allocator.nodeTags⟩
  have growth : final.tree.nodes.size≤s.bank.tree.nodes.size+1 := by rw[nodes];exact reserve.size
  have resources : GeneralBorrowRecursiveSharedResources.Resources final.tree root := {
    depth:=GeneralBorrowFreshReadFrame.depth_on inside final.tree nodes reserve.metadata.certificates.depth,
    children:=by rw[frame];exact reserve.metadata.certificates.children,
    covered:=by rw[frame];exact reserve.metadata.certificates.covered,
    roots:=roots.trans insideRoot,allocator:=nextAllocator,clean:=finalClean,well:=activated.2.2.1,
    room:=by have size:=growth;omega }
  have capacity : final.tree.locations.size=s.bank.tree.locations.size := activated.2.2.2.trans reserve.metadata.capacity
  refine {
    state:={
      bank:={
        tree:=final.tree,resources:=resources,handles:=[root],
        present:=by intro index member;have same:=List.mem_singleton.mp member;subst index;exact ⟨rootNode,rootPresentFinal⟩,
        bounds:=by rw[capacity];exact s.bank.bounds,
        owned:=by intro index member position valid positive start stop;have same:=List.mem_singleton.mp member;subst index
                  exact (combined final.tree _ root (finalRootOwned position valid positive start stop)).1 },
      rootMember:=List.mem_singleton_self root,rootPresent:=⟨rootNode,rootPresentFinal,rootTagEq.trans originalTag⟩,
      rootPath:=rootPath,paths:=by intro index member location;have same:=List.mem_singleton.mp member;subst index;rw[rootPath];simp,
      owned:=by intro index member position valid positive start stop;have same:=List.mem_singleton.mp member;subst index
                exact combined final.tree _ root (finalRootOwned position valid positive start stop) },
    actual:=rfl,handles:=rfl,completed:=⟨constructed.1,constructed.2.1,activated.1⟩,growth:=growth,fresh:=?_,child:=?_ }
  · intro future unused different
    apply GeneralBorrowForestForeignSharedFresh.fresh_of_absent
    change final.tree.tagMapping.get future=none
    rw[mapping]
    have old:=reserve.oldLookup future different
    have absent : s.bank.tree.indexOfTag future=none := by unfold BorrowTree.indexOfTag UniKeyMap.get;rw[GeneralBorrowTagMap.fresh_find s.bank.tree.tagMapping future unused];rfl
    exact old.trans absent
  · refine ⟨child,childNode,?_,childTag⟩
    change final.tree.nodes.get child=some childNode
    rw[nodes]
    exact childPresent

def next {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh s.bank.tree.tagMapping tag) (nonzero : len≠0)
    (room : s.bank.tree.nodes.size+5≤4294967295) := (build s tag fresh nonzero room).state

theorem tree {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh s.bank.tree.tagMapping tag) (nonzero : len≠0)
    (room : s.bank.tree.nodes.size+5≤4294967295) : (next s tag fresh nonzero room).bank.tree=(operation s tag).tree :=
  (build s tag fresh nonzero room).actual

theorem facts {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh s.bank.tree.tagMapping tag) (nonzero : len≠0)
    (room : s.bank.tree.nodes.size+5≤4294967295) : Completed s tag := (build s tag fresh nonzero room).completed

theorem handles_length {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh s.bank.tree.tagMapping tag) (nonzero : len≠0)
    (room : s.bank.tree.nodes.size+5≤4294967295) : (next s tag fresh nonzero room).bank.handles.length=1 := by
  change (build s tag fresh nonzero room).state.bank.handles.length=1
  rw[(build s tag fresh nonzero room).handles];rfl

theorem size {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh s.bank.tree.tagMapping tag) (nonzero : len≠0)
    (room : s.bank.tree.nodes.size+5≤4294967295) : (next s tag fresh nonzero room).bank.tree.nodes.size≤s.bank.tree.nodes.size+1 := by
  rw[tree];exact (build s tag fresh nonzero room).growth

theorem fresh_tag {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh s.bank.tree.tagMapping tag) (nonzero : len≠0)
    (room : s.bank.tree.nodes.size+5≤4294967295) (future : BorTag)
    (unused : GeneralBorrowTagMap.Fresh s.bank.tree.tagMapping future) (different : tag≠future) :
    GeneralBorrowTagMap.Fresh (next s tag fresh nonzero room).bank.tree.tagMapping future := by
  rw[tree];exact (build s tag fresh nonzero room).fresh future unused different
end
end DuplicatePrefix.GeneralBorrowSharedRootMutableEpisode
