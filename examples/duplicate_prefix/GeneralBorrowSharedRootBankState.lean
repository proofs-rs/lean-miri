import duplicate_prefix.GeneralBorrowSharedBankSeed
import duplicate_prefix.GeneralBorrowSharedRootLabel
import duplicate_prefix.GeneralBorrowRecursiveRootRestore

namespace DuplicatePrefix.GeneralBorrowSharedRootBankState
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshReleaseMixed DuplicatePrefix.GeneralBorrowProjection
open DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralBorrowSharedRootLabel

set_option autoImplicit false in
/-- A readable prior-parent bank with the original root's mutable label retained
at every selectable anchor. All fields describe data and permissions. -/
structure State (root : UniIndex) (rootTag : BorTag) (offset len : UInt64) where
  bank : GeneralBorrowSharedBankState.State root offset len
  rootMember : root ∈ bank.handles
  rootPresent : ∃ node, bank.tree.nodeAt root = some node ∧ node.tag = rootTag
  rootPath : ∀ location : LocationTree,
    (source_normal_projection bank.tree location {}).topology.ancestorPath root.toNat = [root.toNat]
  paths : ∀ target ∈ bank.handles, ∀ location : LocationTree,
    root.toNat ∈ (source_normal_projection bank.tree location {}).topology.ancestorPath target.toNat
  owned : ∀ target ∈ bank.handles,
    OwnedOn (Combined bank.tree {} target (writable root)) offset (offset+len) bank.tree.locations

noncomputable def select {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : State root rootTag offset len) (parent : UniIndex) (member : parent ∈ s.bank.handles) :
    GeneralBorrowRecursiveSharedHistory.State root offset len :=
  { GeneralBorrowSharedBankState.select s.bank parent member with
    writable := writable root, owned := s.owned parent member }

/-- The original root's ordinary entry certificate is recovered internally from
the stronger bank contract, at any generated topology depth. -/
noncomputable def entryData {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : State root rootTag offset len) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh s.bank.tree.tagMapping tag) :
    GenericAsMutPtrEntryValidity.Data s.bank.tree {} rootTag tag offset len := by
  let selected := select s root s.rootMember
  have facts : GeneralBorrowRecursiveRootRestore.RootFacts selected rootTag := {
    present := s.rootPresent, path := s.rootPath
    ancestor := s.paths root s.rootMember
    writable := by simp [selected,select,writable]
    protections := rfl }
  exact GeneralBorrowRecursiveRootRestore.entryData selected rootTag tag facts fresh

private theorem write_root (tree : BorrowTree) (location : LocationTree) (root : UniIndex)
    (owned : GeneralBorrowRange.LocationOwned tree {} root .Write location) :
    Combined tree {} root (writable root) location := by
  have read := (GeneralBorrowFreshMixedChild.write_combined tree location {} root owned).1
  refine ⟨read,?_⟩
  intro position valid
  by_cases same : position = root.toNat
  · obtain ⟨state,present,permission⟩ := owned.2.permissions position (by rw [←owned.2.locationsAligned];exact valid)
    exact ⟨state,present,by simpa [GeneralBorrowPermissions.Required,GeneralBorrowPermissions.AccessOwned,writable,same] using permission⟩
  · obtain ⟨state,present,permission⟩ := read.2.permissions position (by rw [←read.2.locationsAligned];exact valid)
    exact ⟨state,present,by simpa [GeneralBorrowPermissions.Required,GeneralBorrowPermissions.AccessOwned,writable,same] using permission⟩

def of_partition (tree : BorrowTree) (root : UniIndex) (capacity : UInt64)
    (s : GeneralBorrowPartitionState.State tree root capacity) (offset len : UInt64)
    (bounds : offset.toNat+len.toNat ≤ capacity.toNat) : State root s.node.tag offset len := by
  let bank := GeneralBorrowSharedBankSeed.of_partition tree root capacity s offset len bounds
  have facts := GeneralBorrowRecursiveRootRestore.of_partition tree root capacity s offset len bounds
  exact {
    bank := bank, rootMember := by simp [bank,GeneralBorrowSharedBankSeed.of_partition]
    rootPresent := ⟨s.node,s.star.present,rfl⟩
    rootPath := facts.path
    paths := by
      intro target member location
      have same : target = root := List.mem_singleton.mp member
      subst target
      exact facts.ancestor location
    owned := by
      intro target member position valid positive before after
      have same : target = root := List.mem_singleton.mp member
      subst target
      exact write_root tree _ root (s.owned position valid) }
end DuplicatePrefix.GeneralBorrowSharedRootBankState
