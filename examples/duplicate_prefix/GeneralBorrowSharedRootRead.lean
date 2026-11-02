import duplicate_prefix.GeneralBorrowSharedRootAccessReset
import duplicate_prefix.GeneralBorrowUnprotectedReadLocalBank
namespace DuplicatePrefix.GeneralBorrowSharedRootRead
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralBorrowSharedRootLabel
open DuplicatePrefix.GeneralBorrowFreshReleaseMixed
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

structure Output {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len) where
  state : GeneralBorrowSharedRootBankState.State root rootTag offset len
  actual : state.bank.tree = (GeneralBorrowSharedRootAccessReset.operation s .Read).tree
  handles : state.bank.handles = s.bank.handles
  completed : (GeneralBorrowSharedRootAccessReset.operation s .Read).status = .Completed

/-- A genuine root Read preserves every selectable child and the original
root's writable labels. Only root Write needs the singleton bank reset. -/
def build {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len)
    (tag : BorTag) (fresh : GeneralBorrowTagMap.Fresh s.bank.tree.tagMapping tag) : Output s := by
  let reset := GeneralBorrowSharedRootAccessReset.build s tag fresh .Read
  let tree := s.bank.tree
  let nextTree := reset.state.bank.tree
  let data := GeneralBorrowSharedRootBankState.entryData s tag fresh
  have frame := GeneralBorrowFreshReadFrame.frame tree (.concrete rootTag) (Size.ofBytes offset) (Size.ofBytes len) .Read {} .VisitChildrenOfAccessed
  change (GeneralBorrowSharedRootAccessReset.operation s .Read).tree = {tree with locations := (GeneralBorrowSharedRootAccessReset.operation s .Read).tree.locations} at frame
  have shaped : nextTree = {tree with locations := nextTree.locations} := by
    rw [show nextTree = (GeneralBorrowSharedRootAccessReset.operation s .Read).tree from reset.actual]
    exact frame
  have nodes : nextTree.nodes = tree.nodes := by have equal := congrArg BorrowTree.nodes shaped;exact equal
  have preserved := GeneralBorrowUnprotectedReadLocalBank.preserves tree rootTag root root s.bank.handles
    (Size.ofBytes offset) (Size.ofBytes len) .VisitChildrenOfAccessed data.nodeFits s.bank.resources.depth s.bank.resources.children
    data.node data.parentPresent s.bank.resources.roots s.bank.resources.covered data.tagPresent s.bank.resources.well offset (offset+len)
    (s.bank.owned root s.rootMember) s.bank.owned s.bank.bounds (Nat.le_refl _) (Nat.le_refl _)
  have readable : ∀ target ∈ s.bank.handles, OwnedOn (GeneralBorrowRange.LocationOwned nextTree {} target .Read)
      offset (offset+len) nextTree.locations := by
    intro target member
    have owner : OwnedOn (GeneralBorrowRange.LocationOwned tree {} target .Read) offset (offset+len) nextTree.locations := by
      rw [show nextTree = (GeneralBorrowSharedRootAccessReset.operation s .Read).tree from reset.actual]
      exact preserved.2.1 target member
    have transport (loc : LocationTree) : GeneralBorrowRange.LocationOwned nextTree {} target .Read loc =
        GeneralBorrowRange.LocationOwned tree {} target .Read loc := by rw [shaped];rfl
    intro position valid positive before after
    rw [transport]
    exact owner position valid positive before after
  have paths : ∀ target ∈ s.bank.handles, ∀ loc : LocationTree,
      root.toNat ∈ (source_normal_projection nextTree loc {}).topology.ancestorPath target.toNat := by
    intro target member loc
    have topology : (source_normal_projection nextTree loc {}).topology = (source_normal_projection tree loc {}).topology := by rw [shaped];rfl
    rw [topology];exact s.paths target member loc
  have rootMem : root ∈ reset.state.bank.handles := by rw [reset.handles];simp
  exact {
    state := {
      bank := {
        tree := nextTree,resources := reset.state.bank.resources,handles := s.bank.handles
        present := by intro index member;obtain ⟨node,found⟩ := s.bank.present index member;exact ⟨node,by change nextTree.nodes.get index = some node;rw [nodes];exact found⟩
        bounds := reset.state.bank.bounds
        owned := readable }
      rootMember := s.rootMember
      rootPresent := reset.state.rootPresent
      rootPath := reset.state.rootPath
      paths := paths
      owned := by
        intro target member position valid positive before after
        have rootMixed := (reset.state.owned root rootMem position valid positive before after).2
        exact GeneralBorrowSharedRootLabel.transfer nextTree _ root root target rootMixed
          (readable target member position valid positive before after)
          (by rw [reset.state.rootPath];simp) (paths target member _) }
    actual := reset.actual,handles := rfl,completed := reset.completed }
end
end DuplicatePrefix.GeneralBorrowSharedRootRead
