import duplicate_prefix.GeneralBorrowSharedRootBankState
import duplicate_prefix.GeneralBorrowSharedBankAdvance

namespace DuplicatePrefix.GeneralBorrowSharedRootBankAdvance
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowSharedRootBankState DuplicatePrefix.GeneralBorrowSharedRootLabel
open DuplicatePrefix.GeneralBorrowRecursiveSharedHistory DuplicatePrefix.GeneralBorrowFreshSharedSequence
open DuplicatePrefix.GeneralBorrowFreshReleaseMixed DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralRangeMapOrigins
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- A real branching shared stage retains the original root's mutable label at
all old and new selectable handles, using the selected stage's proved Mixed
result and the independently preserved Read bank. -/
noncomputable def next {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : State root rootTag offset len) (parent : UniIndex) (member : parent ∈ s.bank.handles)
    (tag : BorTag) (fresh : GeneralBorrowTagMap.Fresh s.bank.tree.tagMapping tag)
    (nonzero : len ≠ 0) (room : s.bank.tree.nodes.size+5 ≤ 4294967295) :
    State root rootTag offset len := by
  let selected := select s parent member
  let d := supplied selected tag fresh nonzero
  let actual := GeneralBorrowRecursiveSharedHistory.next selected tag fresh nonzero false room
  let bank := GeneralBorrowSharedBankAdvance.next s.bank parent member tag fresh nonzero room
  have different := GeneralBorrowSharedBankNodes.different s.bank parent member tag fresh nonzero root s.rootMember
  have differentNat : (index d).toNat ≠ root.toNat := by
    intro same
    exact different (GeneralBorrowNodeUpdate.index_injective root (index d) same.symm)
  have labels := GeneralBorrowSharedRootLabel.extend root (index d).toNat differentNat
  have current : OwnedOn (Combined bank.tree {} (index d) (writable root)) offset (offset+len) bank.tree.locations := by
    have own := actual.owned
    change OwnedOn (Combined bank.tree {} (index d)
      (GeneralBorrowFreshMixedChild.extend (writable root) (index d).toNat)) offset (offset+len) bank.tree.locations at own
    rw [labels] at own
    exact own
  have paths : ∀ target ∈ bank.handles, ∀ location : LocationTree,
      root.toNat ∈ (source_normal_projection bank.tree location {}).topology.ancestorPath target.toNat := by
    intro target memberAfter location
    have attached := GeneralBorrowFreshSharedStageAttachAny.attach s.bank.tree tag parent offset len d {} false
      (writable root) selected.owned location location {}
    rcases List.mem_cons.mp memberAfter with same | old
    · subst target
      change root.toNat ∈ (source_normal_projection (child d {} false).tree location {}).topology.ancestorPath (index d).toNat
      exact (congrArg (fun path : List Nat => root.toNat ∈ path) attached.childPath).mpr
        (List.mem_cons_of_mem _ (s.paths parent member location))
    · obtain ⟨node,present⟩ := s.bank.present target old
      have valid := GeneralBorrowNodeUpdate.lookup_valid s.bank.tree.nodes target node present
      have targetDiff := GeneralBorrowSharedBankNodes.different s.bank parent member tag fresh nonzero target old
      have targetDiffNat : target.toNat ≠ (index d).toNat := fun equal => targetDiff (GeneralBorrowNodeUpdate.index_injective _ _ equal)
      have size : (source_normal_projection s.bank.tree location {}).topology.nodes.size = s.bank.tree.nodes.data.size := by
        unfold_general_projection;unfold_general_topology;simp only [Array.size_map]
      have oldPath := attached.oldPath target.toNat (by rw [size];exact valid) targetDiffNat
      change root.toNat ∈ (source_normal_projection (child d {} false).tree location {}).topology.ancestorPath target.toNat
      exact (congrArg (fun path : List Nat => root.toNat ∈ path) oldPath).mpr (s.paths target old location)
  let rootNode := Classical.choose s.rootPresent
  have rootPresent := (Classical.choose_spec s.rootPresent).1
  have rootTagged := (Classical.choose_spec s.rootPresent).2
  have retained := GeneralBorrowFreshSharedStagePaths.old_node
    s.bank.tree tag parent offset len d {} false (writable root) selected.owned root rootNode rootPresent
  let afterNode := Classical.choose retained
  have afterPresent := (Classical.choose_spec retained).1
  have afterTag := (Classical.choose_spec retained).2.1
  exact {
    bank := bank
    rootMember := List.mem_cons_of_mem _ s.rootMember
    rootPresent := ⟨afterNode,afterPresent,afterTag.trans rootTagged⟩
    rootPath := by
      intro location
      have attached := GeneralBorrowFreshSharedStageAttachAny.attach s.bank.tree tag parent offset len d {} false
        (writable root) selected.owned location location {}
      have valid := GeneralBorrowNodeUpdate.lookup_valid s.bank.tree.nodes root rootNode rootPresent
      have size : (source_normal_projection s.bank.tree location {}).topology.nodes.size = s.bank.tree.nodes.data.size := by
        unfold_general_projection;unfold_general_topology;simp only [Array.size_map]
      have oldPath := attached.oldPath root.toNat (by rw [size];exact valid) (Ne.symm differentNat)
      exact oldPath.trans (s.rootPath location)
    paths := paths
    owned := by
      intro target targetMember position valid positive before after
      have sourceOwned := current position valid positive before after
      have targetRead := bank.owned target targetMember position valid positive before after
      exact GeneralBorrowSharedRootLabel.transfer bank.tree _ root (index d) target sourceOwned.2 targetRead
        (paths (index d) (List.mem_cons_self) _) (paths target targetMember _) }
theorem handles_length {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : State root rootTag offset len) (parent : UniIndex) (member : parent ∈ s.bank.handles)
    (tag : BorTag) (fresh : GeneralBorrowTagMap.Fresh s.bank.tree.tagMapping tag)
    (nonzero : len ≠ 0) (room : s.bank.tree.nodes.size+5 ≤ 4294967295) :
    (next s parent member tag fresh nonzero room).bank.handles.length = s.bank.handles.length+1 := rfl

theorem size {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : State root rootTag offset len) (parent : UniIndex) (member : parent ∈ s.bank.handles)
    (tag : BorTag) (fresh : GeneralBorrowTagMap.Fresh s.bank.tree.tagMapping tag)
    (nonzero : len ≠ 0) (room : s.bank.tree.nodes.size+5 ≤ 4294967295) :
    (next s parent member tag fresh nonzero room).bank.tree.nodes.size ≤ s.bank.tree.nodes.size+1 :=
  GeneralBorrowSharedBankAdvance.size s.bank parent member tag fresh nonzero room
end DuplicatePrefix.GeneralBorrowSharedRootBankAdvance
