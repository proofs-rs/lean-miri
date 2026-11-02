import duplicate_prefix.GeneralBorrowSharedRootBankExposure
import duplicate_prefix.GeneralBorrowFreshActiveOnRange
import duplicate_prefix.GeneralBorrowGcSharedRootBank
namespace DuplicatePrefix.GeneralBorrowSharedRootAccessReset
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralBorrowSharedRootLabel
open DuplicatePrefix.GeneralBorrowFreshReleaseMixed DuplicatePrefix.GeneralBorrowPermissions DuplicatePrefix.GeneralBorrowAnchor
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

def operation {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len) (kind : AccessKind) :=
  s.bank.tree.performNormalAccessRange rootTag (Size.ofBytes offset) (Size.ofBytes len) kind {} .VisitChildrenOfAccessed

private theorem combined (tree : BorrowTree) (location : LocationTree) (root : UniIndex)
    (owned : GeneralBorrowRange.LocationOwned tree {} root .Write location) :
    Combined tree {} root (writable root) location := by
  have read := (GeneralBorrowFreshMixedChild.write_combined tree location {} root owned).1
  refine ⟨read,?_⟩
  intro position valid
  by_cases same : position = root.toNat
  · obtain ⟨state,present,permission⟩ := owned.2.permissions position (by rw [←owned.2.locationsAligned];exact valid)
    exact ⟨state,present,by simpa [Required,AccessOwned,writable,same] using permission⟩
  · obtain ⟨state,present,permission⟩ := read.2.permissions position (by rw [←read.2.locationsAligned];exact valid)
    exact ⟨state,present,by simpa [Required,AccessOwned,writable,same] using permission⟩

structure Output {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len) (kind : AccessKind) where
  state : GeneralBorrowSharedRootBankState.State root rootTag offset len
  actual : state.bank.tree = (operation s kind).tree
  handles : state.bank.handles = [root]
  completed : (operation s kind).status = .Completed

/-- A genuine original-root Read/Write rebuilds a singleton selectable root
bank. Old child nodes remain in the actual tree, but are discarded as selectable
handles because a root Write may have disabled their permissions. -/
def build {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len)
    (tag : BorTag) (fresh : GeneralBorrowTagMap.Fresh s.bank.tree.tagMapping tag) (kind : AccessKind) : Output s kind := by
  let data := GeneralBorrowSharedRootBankState.entryData s tag fresh
  let tree := s.bank.tree
  let result := operation s kind
  have fits : tree.nodes.data.size ≤ 4294967296 := data.nodeFits
  have owned : OwnedOn (GeneralBorrowRange.LocationOwned tree {} root .Write) offset (offset+len) tree.locations := data.owned
  have facts := GeneralBorrowRangeLocal.access tree {} rootTag root root (Size.ofBytes offset) (Size.ofBytes len)
    kind .Write .VisitChildrenOfAccessed (by intro impossible;cases impossible) fits s.bank.resources.depth s.bank.resources.children
    data.node data.parentPresent s.bank.resources.roots s.bank.resources.covered data.tagPresent s.bank.resources.well offset (offset+len)
    owned s.bank.bounds (Nat.le_refl _) (Nat.le_refl _)
  have frame := GeneralBorrowFreshReadFrame.frame tree (.concrete rootTag) (Size.ofBytes offset) (Size.ofBytes len) kind {} .VisitChildrenOfAccessed
  change result.tree = {tree with locations := result.tree.locations} at frame
  have nodes : result.tree.nodes = tree.nodes := by have equal := congrArg BorrowTree.nodes frame;exact equal
  have mapping : result.tree.tagMapping = tree.tagMapping := by have equal := congrArg BorrowTree.tagMapping frame;exact equal
  have roots : result.tree.roots = tree.roots := by have equal := congrArg BorrowTree.roots frame;exact equal
  have clean : GeneralBorrowGcVacantClean.VacantClean result.tree := by
    intro query vacant
    have previous : tree.nodes.get query = none := by rw [←nodes];exact vacant
    have preserved := GeneralBorrowFreshActiveOnRange.ranged tree {} rootTag root root query (Size.ofBytes offset) (Size.ofBytes len)
      kind .Write .VisitChildrenOfAccessed (by intro impossible;cases impossible) s.bank.resources.depth s.bank.resources.children data.node
      data.parentPresent s.bank.resources.roots s.bank.resources.covered data.tagPresent previous (s.bank.resources.clean query previous)
      s.bank.resources.well offset (offset+len) owned s.bank.bounds (Nat.le_refl _) (Nat.le_refl _)
    exact preserved.2
  have rootPresent : result.tree.nodes.get root = some data.node := by rw [nodes];exact data.parentPresent
  have tagged : data.node.tag = rootTag := by
    have lookup := s.bank.resources.allocator.nodeTags root data.node data.parentPresent
    have original := (Classical.choose_spec s.rootPresent).2
    change (Classical.choose s.rootPresent).tag = rootTag at original
    exact original
  have rootPath : ∀ loc : LocationTree, (source_normal_projection result.tree loc {}).topology.ancestorPath root.toNat = [root.toNat] := by
    intro loc
    have topology : (source_normal_projection result.tree loc {}).topology = (source_normal_projection tree loc {}).topology := by
      rw [frame];rfl
    rw [topology];exact s.rootPath loc
  have nextResources : GeneralBorrowRecursiveSharedResources.Resources result.tree root := {
    depth := GeneralBorrowFreshReadFrame.depth_on tree result.tree nodes s.bank.resources.depth
    children := by rw [frame];exact s.bank.resources.children
    covered := by rw [frame];exact s.bank.resources.covered
    roots := roots.trans s.bank.resources.roots
    allocator := {
      pool := by simpa only [nodes,mapping] using s.bank.resources.allocator.pool
      accounting := by simpa only [GeneralBorrowFreshStagePool.Accounting,nodes,mapping] using s.bank.resources.allocator.accounting
      unique := by simpa only [GeneralBorrowGcAllocator.KeyUnique,mapping] using s.bank.resources.allocator.unique
      nodeTags := by intro index node present;rw [nodes] at present;rw [mapping];exact s.bank.resources.allocator.nodeTags index node present }
    clean := clean
    well := facts.2.2.1
    room := by rw [show result.tree.nodes.size = tree.nodes.size from congrArg UniValMap.size nodes];exact s.bank.resources.room }
  have capacity : result.tree.locations.size = tree.locations.size := facts.2.2.2
  have rootOwned : OwnedOn (GeneralBorrowRange.LocationOwned result.tree {} root .Write) offset (offset+len) result.tree.locations := facts.2.1
  exact {
    state := {
      bank := {
        tree := result.tree,resources := nextResources,handles := [root]
        present := by intro index member;have same := List.mem_singleton.mp member;subst index;exact ⟨data.node,rootPresent⟩
        bounds := by rw [capacity];exact s.bank.bounds
        owned := by
          intro index member position valid positive before after
          have same := List.mem_singleton.mp member;subst index
          exact (combined result.tree _ root (rootOwned position valid positive before after)).1 }
      rootMember := List.mem_singleton_self root
      rootPresent := ⟨data.node,rootPresent,tagged⟩
      rootPath := rootPath
      paths := by intro index member loc;have same := List.mem_singleton.mp member;subst index;rw [rootPath];simp
      owned := by
        intro index member position valid positive before after
        have same := List.mem_singleton.mp member;subst index
        exact combined result.tree _ root (rootOwned position valid positive before after) }
    actual := rfl,handles := rfl,completed := facts.1 }
end
end DuplicatePrefix.GeneralBorrowSharedRootAccessReset
