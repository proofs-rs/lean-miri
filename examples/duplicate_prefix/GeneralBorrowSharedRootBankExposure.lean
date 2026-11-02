import duplicate_prefix.GeneralBorrowRootExposureGc
import duplicate_prefix.GeneralBorrowFreshMixedShape
namespace DuplicatePrefix.GeneralBorrowSharedRootBankExposure
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowView DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralRangeMapOrigins
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- Flags/cache-independent shape transports the complete arbitrary branching
root-writable handle bank, without a numerical cache-coherence claim. -/
def of_shape {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len) (next : BorrowTree)
    (shape : treeShape next = treeShape s.bank.tree) :
    GeneralBorrowSharedRootBankState.State root rootTag offset len := by
  have geometry := GeneralBorrowFreshGeometry.shape_frame s.bank.tree next shape s.bank.resources.well
  have topology : ∀ loc, (source_normal_projection next loc {}).topology = (source_normal_projection s.bank.tree loc {}).topology := by
    intro loc
    exact congrArg (fun normal => normal.1)
      (GeneralBorrowFreshOwnership.projection_shape s.bank.tree next loc loc {}
        (GeneralBorrowFreshMetadata.node_array s.bank.tree next shape) rfl)
  let old := Classical.choose s.rootPresent
  have present := (Classical.choose_spec s.rootPresent).1
  have tagged := (Classical.choose_spec s.rootPresent).2
  have fields := GeneralBorrowFreshMetadata.node_fields s.bank.tree next shape root old present
  let node := Classical.choose fields
  have facts := Classical.choose_spec fields
  exact {
    bank := {
      tree := next
      resources := GeneralBorrowRootExposureGc.resources s.bank.tree next root s.bank.resources shape
      handles := s.bank.handles
      present := by
        intro index member
        obtain ⟨value,found⟩ := s.bank.present index member
        obtain ⟨after,stored,_⟩ := GeneralBorrowFreshMetadata.node_exists s.bank.tree next shape index value found
        exact ⟨after,stored⟩
      bounds := by rw [geometry.2];exact s.bank.bounds
      owned := fun index member => GeneralBorrowFreshOwnedOn.shape_preserves s.bank.tree next shape {} index .Read offset (offset+len) (s.bank.owned index member) }
    rootMember := s.rootMember
    rootPresent := ⟨node,facts.1,facts.2.1.trans tagged⟩
    rootPath := by intro loc;rw [topology];exact s.rootPath loc
    paths := by intro index member loc;rw [topology];exact s.paths index member loc
    owned := fun index member => GeneralBorrowFreshMixedShape.shape_preserves s.bank.tree next shape {} index
      (GeneralBorrowSharedRootLabel.writable root) offset (offset+len) (s.owned index member) }

theorem shape {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len) :
    treeShape (s.bank.tree.exposeTag {} rootTag).tree = treeShape s.bank.tree := by
  obtain ⟨node,present,tagged⟩ := s.rootPresent
  have mapped : s.bank.tree.indexOfTag rootTag = some root := by
    have lookup := s.bank.resources.allocator.nodeTags root node present
    rw [tagged] at lookup
    exact lookup
  cases flag : node.isExposed with
  | false => exact (GeneralBorrowRootExposureFrame.expose s.bank.tree rootTag root node mapped present s.bank.resources.depth flag {}).2.1
  | true => rw [GeneralBorrowRootExposureFrame.already s.bank.tree rootTag root node mapped present flag {}]

/-- A real root exposure, including repeated early-return requests, retains all
selectable writable-label banks and next-operation resources. -/
def next {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len) :=
  of_shape s (s.bank.tree.exposeTag {} rootTag).tree (shape s)

theorem tree {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len) :
    (next s).bank.tree = (s.bank.tree.exposeTag {} rootTag).tree := rfl

theorem handles {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len) :
    (next s).bank.handles = s.bank.handles := rfl

theorem size {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len) :
    (next s).bank.tree.nodes.size = s.bank.tree.nodes.size :=
  GeneralBorrowFreshMetadata.node_size s.bank.tree _ (shape s)

theorem fresh_tag {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len)
    (tag : BorTag) (fresh : GeneralBorrowTagMap.Fresh s.bank.tree.tagMapping tag) :
    GeneralBorrowTagMap.Fresh (next s).bank.tree.tagMapping tag := by
  change GeneralBorrowTagMap.Fresh (s.bank.tree.exposeTag {} rootTag).tree.tagMapping tag
  rw [GeneralBorrowFreshMetadata.mapping s.bank.tree _ (shape s)]
  exact fresh
end
end DuplicatePrefix.GeneralBorrowSharedRootBankExposure
