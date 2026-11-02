import duplicate_prefix.GeneralBorrowRetainedMutableEpisode
namespace DuplicatePrefix.GeneralBorrowRetainedMutableAccess
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralRangeMapOrigins GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section
structure State (root child : UniIndex) (childTag : BorTag) (offset len : UInt64) where
  tree : BorrowTree
  resources : GeneralBorrowRecursiveSharedResources.Resources tree root
  node : TreeNode
  present : tree.nodeAt child = some node
  lookup : tree.indexOfTag childTag = some child
  bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat
  owned : OwnedOn (GeneralBorrowRange.LocationOwned tree {} child .Write) offset (offset+len) tree.locations

def operation {root child : UniIndex} {childTag : BorTag} {offset len : UInt64}
    (s : State root child childTag offset len) (kind : AccessKind) :=
  s.tree.performNormalAccessRange childTag (Size.ofBytes offset) (Size.ofBytes len) kind {} .VisitChildrenOfAccessed

structure Output {root child : UniIndex} {childTag : BorTag} {offset len : UInt64}
    (s : State root child childTag offset len) (kind : AccessKind) where
  state : State root child childTag offset len
  actual : state.tree = (operation s kind).tree
  completed : (operation s kind).status = .Completed

def build {root child : UniIndex} {childTag : BorTag} {offset len : UInt64}
    (s : State root child childTag offset len) (kind : AccessKind) : Output s kind := by
  let tree := s.tree
  let result := operation s kind
  have fits : tree.nodes.data.size ≤ 4294967296 := by have room := s.resources.room;change tree.nodes.data.size+4 ≤ _ at room;omega
  have owned : OwnedOn (GeneralBorrowRange.LocationOwned tree {} child .Write) offset (offset+len) tree.locations := s.owned
  have facts := GeneralBorrowRangeLocal.access tree {} childTag child root (Size.ofBytes offset) (Size.ofBytes len)
    kind .Write .VisitChildrenOfAccessed (by intro impossible;cases impossible) fits s.resources.depth s.resources.children
    s.node s.present s.resources.roots s.resources.covered s.lookup s.resources.well offset (offset+len)
    owned s.bounds (Nat.le_refl _) (Nat.le_refl _)
  have frame := GeneralBorrowFreshReadFrame.frame tree (.concrete childTag) (Size.ofBytes offset) (Size.ofBytes len) kind {} .VisitChildrenOfAccessed
  change result.tree = {tree with locations := result.tree.locations} at frame
  have nodes : result.tree.nodes = tree.nodes := by have equal := congrArg BorrowTree.nodes frame;exact equal
  have mapping : result.tree.tagMapping = tree.tagMapping := by have equal := congrArg BorrowTree.tagMapping frame;exact equal
  have roots : result.tree.roots = tree.roots := by have equal := congrArg BorrowTree.roots frame;exact equal
  have clean : GeneralBorrowGcVacantClean.VacantClean result.tree := by
    intro query vacant
    have previous : tree.nodes.get query = none := by rw [←nodes];exact vacant
    have preserved := GeneralBorrowFreshActiveOnRange.ranged tree {} childTag child root query (Size.ofBytes offset) (Size.ofBytes len)
      kind .Write .VisitChildrenOfAccessed (by intro impossible;cases impossible) s.resources.depth s.resources.children s.node
      s.present s.resources.roots s.resources.covered s.lookup previous (s.resources.clean query previous)
      s.resources.well offset (offset+len) owned s.bounds (Nat.le_refl _) (Nat.le_refl _)
    exact preserved.2
  have nextResources : GeneralBorrowRecursiveSharedResources.Resources result.tree root := {
    depth := GeneralBorrowFreshReadFrame.depth_on tree result.tree nodes s.resources.depth
    children := by rw [frame];exact s.resources.children
    covered := by rw [frame];exact s.resources.covered
    roots := roots.trans s.resources.roots
    allocator := {
      pool := by simpa only [nodes,mapping] using s.resources.allocator.pool
      accounting := by simpa only [GeneralBorrowFreshStagePool.Accounting,nodes,mapping] using s.resources.allocator.accounting
      unique := by simpa only [GeneralBorrowGcAllocator.KeyUnique,mapping] using s.resources.allocator.unique
      nodeTags := by intro index node present;rw [nodes] at present;rw [mapping];exact s.resources.allocator.nodeTags index node present }
    clean := clean
    well := facts.2.2.1
    room := by rw [show result.tree.nodes.size = tree.nodes.size from congrArg UniValMap.size nodes];exact s.resources.room }
  have capacity : result.tree.locations.size = tree.locations.size := facts.2.2.2
  exact {
    state := {
      tree := result.tree
      resources := nextResources
      node := s.node
      present := by change result.tree.nodes.get child = some s.node;rw [nodes];exact s.present
      lookup := by change result.tree.tagMapping.get childTag = some child;rw [mapping];exact s.lookup
      bounds := by rw [capacity];exact s.bounds
      owned := facts.2.1 }
    actual := rfl
    completed := facts.1 }

def ofEpisode {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh s.bank.tree.tagMapping tag) (nonzero : len≠0)
    (room : s.bank.tree.nodes.size+5≤4294967295) :
    State root (GeneralBorrowRetainedMutableEpisode.build s tag fresh nonzero room).childIndex tag offset len := by
  let output := GeneralBorrowRetainedMutableEpisode.build s tag fresh nonzero room
  have member : output.childIndex ∈ output.state.bank.handles := by rw [output.handles];simp
  let info := output.state.bank.present _ member
  let node := Classical.choose info
  have present := Classical.choose_spec info
  exact {
    tree := output.state.bank.tree
    resources := output.state.bank.resources
    node := node
    present := present,lookup := output.childLookup,bounds := output.state.bank.bounds,owned := output.childOwned }

noncomputable def entryData {root child : UniIndex} {childTag : BorTag} {offset len : UInt64}
    (s : State root child childTag offset len) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh s.tree.tagMapping tag) :
    GenericAsMutPtrEntryValidity.Data s.tree {} childTag tag offset len := by
  let depth := GeneralBorrowCanonicalParentDepth.normalize s.tree.nodes s.resources.depth
  have aligned := GeneralBorrowFreshStagePool.empty_aligned s.tree s.resources.allocator.accounting
  have fits : s.tree.tagMapping.deassigned.back? = none → s.tree.tagMapping.mapping.size ≤ 4294967295 := by
    intro empty;rw [aligned empty]
    have room := s.resources.room
    change s.tree.nodes.data.size+4 ≤ _ at room
    omega
  exact {
    parent := child,root := root,node := s.node,depth := depth
    children := s.resources.children,parentPresent := s.present,roots := s.resources.roots,covered := s.resources.covered
    tagPresent := s.lookup,tagFresh := fresh
    protectorFresh := by
      intro row member same
      have recorded := (GeneralBorrowFreshReuseProtection.entries_get s.tree.nodes row.1 row.2).mp (Array.mem_toList_iff.mpr member)
      have lookup := s.resources.allocator.nodeTags row.1 row.2 recorded
      have absent : s.tree.tagMapping.get tag = none := by
        unfold UniKeyMap.get;rw [GeneralBorrowTagMap.fresh_find s.tree.tagMapping tag fresh];rfl
      rw [same,absent] at lookup
      cases lookup
    nodeFits := by have room := s.resources.room;change s.tree.nodes.data.size+4 ≤ _ at room;omega
    slot := GeneralBorrowCanonicalParentDepth.slot s.tree s.resources.depth child s.node s.present s.resources.allocator.pool aligned fits
    well := s.resources.well,owned := s.owned }

def run {root child : UniIndex} {childTag : BorTag} {offset len : UInt64}
    (s : State root child childTag offset len) : List AccessKind → State root child childTag offset len
  | [] => s
  | kind::rest => run (build s kind).state rest

inductive History {root child : UniIndex} {childTag : BorTag} {offset len : UInt64} :
    State root child childTag offset len → List AccessKind → State root child childTag offset len → Prop
  | nil (s) : History s [] s
  | cons (s) (kind) (rest) (final) :
      (operation s kind).status = .Completed →
      History (build s kind).state rest final → History s (kind::rest) final

theorem run_history {root child : UniIndex} {childTag : BorTag} {offset len : UInt64}
    (s : State root child childTag offset len) (kinds : List AccessKind) : History s kinds (run s kinds) := by
  induction kinds generalizing s with
  | nil => exact .nil s
  | cons kind rest ih => exact .cons s kind rest _ (build s kind).completed (ih _)
end
end DuplicatePrefix.GeneralBorrowRetainedMutableAccess
