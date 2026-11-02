import empty_function.RankNormalization
import Miri.Interpreter.MachineHooks

/-! Raw current-state facts needed by zero-sized protection. No clause mentions
an operation result, trace, future permission or function safety. Existing
exposure caches and permissions at occupied nodes remain unconstrained here:
the zero-sized constructor and fresh unexposed release do not query them. -/
namespace EmptyFunction.TreeRuntimeInput
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false

/-- Finite allocator and graph data for an arbitrary live tree. Rank witnesses
have no numeric bound; compression derives the bounds used by the source loop.
Vacant permission slots are clean independently of sparse node vacancy. -/
structure TreeFormed (tree : BorrowTree) (nextTag : BorTag) where
  parentRank : RankNormalization.ParentRank tree.nodes
  freeValid : ∀ index ∈ tree.tagMapping.deassigned,
    index.toNat < tree.nodes.size ∧ tree.nodes.get index = none
  freeUnique : tree.tagMapping.deassigned.toList.Nodup
  accounting : tree.tagMapping.mapping.size + tree.tagMapping.deassigned.size = tree.nodes.size
  vacantClean : ∀ index, tree.nodes.get index = none →
    ∀ position (valid : position < tree.locations.entries.size),
      tree.locations.entries[position].data.perms.get index = none
  mappedNodes : ∀ row ∈ tree.tagMapping.mapping,
    ∃ node, tree.nodes.get row.2 = some node ∧ node.tag = row.1
  nodeTags : ∀ index node, tree.nodes.get index = some node →
    tree.tagMapping.get node.tag = some index
  uniqueTags : (tree.tagMapping.mapping.toList.map Prod.fst).Nodup
  tagsBelow : ∀ row ∈ tree.tagMapping.mapping, row.1.value.toNat < nextTag.value.toNat

/-- Current bookkeeping high-water facts. Numeric counter headroom is a
separate resource requirement. No empty protector/root cache is required. -/
structure GlobalFormed (global : GlobalState) : Prop where
  protectedBelow : ∀ row ∈ global.protectedTags.entries,
    row.1.value.toNat < global.nextPointerTag.value.toNat
  rootsBelow : ∀ row ∈ global.rootPointerTags,
    row.2.value.toNat < global.nextPointerTag.value.toNat

/-- Runtime facts cover arbitrary live allocations; no particular tree shape,
exposure profile, free-pool choice or contents are imposed. -/
structure World {K U : Type} (before : Interpreter.MachineHooks.MachineState K U)
    (tracker : Interpreter.MachineHooks.BorrowState) : Prop where
  enabled : before.borrowTracker = some tracker
  globals : GlobalFormed tracker.global
  liveTrees : ∀ row ∈ before.memory.live, Nonempty (TreeFormed row.2.allocation.extra tracker.global.nextPointerTag)

namespace GlobalFormed
variable {global : GlobalState}

/-- The actual next tag has no preexisting protector. -/
theorem nextNotProtected (input : GlobalFormed global) :
    global.protectedTags.get global.nextPointerTag = none := by
  have absent : global.protectedTags.entries.find? (fun row => row.1 == global.nextPointerTag) = none := by
    apply Array.find?_eq_none.mpr
    intro row member same
    have equal : row.1 = global.nextPointerTag := by simpa only [beq_iff_eq] using same
    have below := input.protectedBelow row member
    rw [equal] at below
    exact (Nat.lt_irrefl _) below
  simp [ProtectedTags.get, absent]

/-- Registering and ending the fresh empty_function protector restores arbitrary original
protector entries. No empty global protector table is required. -/
theorem protectorRoundtrip (input : GlobalFormed global) (kind : ProtectorKind) :
    (global.protectedTags.insert global.nextPointerTag kind).remove global.nextPointerTag =
      global.protectedTags := by
  have clean : global.protectedTags.entries.filter (fun row => row.1 != global.nextPointerTag) =
      global.protectedTags.entries := by
    apply Array.filter_eq_self.mpr
    intro row member
    have below := input.protectedBelow row member
    have different : row.1 ≠ global.nextPointerTag := by
      intro equal
      rw [equal] at below
      exact (Nat.lt_irrefl _) below
    simp [different]
  simp [ProtectedTags.insert, ProtectedTags.remove, clean]

end GlobalFormed

namespace TreeFormed
variable {tree : BorrowTree} {nextTag : BorTag}

theorem appendAligned (input : TreeFormed tree nextTag)
    (empty : tree.tagMapping.deassigned.back? = none) :
    tree.tagMapping.mapping.size = tree.nodes.size := by
  have nil := Array.back?_eq_none_iff.mp empty
  have count := input.accounting
  simpa [nil] using count

theorem reuseValid (input : TreeFormed tree nextTag) (index : UniIndex)
    (selected : tree.tagMapping.deassigned.back? = some index) :
    index.toNat < tree.nodes.size ∧ tree.nodes.get index = none := by
  obtain ⟨rest, eq⟩ := Array.back?_eq_some_iff.mp selected
  apply input.freeValid index
  rw [eq]
  simp

/-- High-water data proves freshness of the actual next tag. -/
theorem nextFresh (input : TreeFormed tree nextTag) :
    tree.tagMapping.get nextTag = none := by
  have absent : tree.tagMapping.mapping.find? (fun row => row.1 == nextTag) = none := by
    apply Array.find?_eq_none.mpr
    intro row member same
    have equal : row.1 = nextTag := by simpa only [beq_iff_eq] using same
    have below := input.tagsBelow row member
    rw [equal] at below
    exact (Nat.lt_irrefl _) below
  simp [UniKeyMap.get, absent]

/-- A concrete parent tag selects a physically present original node. -/
theorem parentPresent (input : TreeFormed tree nextTag) (tag : BorTag) (index : UniIndex)
    (tagged : tree.tagMapping.get tag = some index) :
    ∃ node, tree.nodes.get index = some node := by
  unfold UniKeyMap.get at tagged
  cases found : tree.tagMapping.mapping.find? (fun row => row.1 == tag) with
  | none => simp [found] at tagged
  | some row =>
    have member := Array.mem_of_find?_eq_some found
    obtain ⟨node,present,_⟩ := input.mappedNodes row member
    have indexEq : row.2 = index := by simpa [found] using tagged
    exact ⟨node,indexEq ▸ present⟩

/-- Raw runtime structure plus counter room discharges every graph/allocator
premise of the concrete unit constructor, including strict rank slack. -/
theorem construct (input : TreeFormed tree nextTag) (parentTag : BorTag) (parent : UniIndex)
    (tagged : tree.tagMapping.get parentTag = some parent)
    (room : tree.tagMapping.mapping.size ≤ 4294967295)
    (offset : Size) (initial : LocationState) :
    ∃ after, tree.newChild offset (.concrete parentTag) nextTag
      (Miri.DataStructures.DedupRangeMap.new Size.ZERO initial) (.ReservedFrz false) true =
      ⟨after, .ok ()⟩ := by
  obtain ⟨node,present⟩ := input.parentPresent parentTag parent tagged
  exact RankNormalization.concrete_child_of_rank tree input.parentRank
    parentTag nextTag parent node tagged present input.nextFresh room
    input.appendAligned input.reuseValid offset initial

/-- Raw freshness and free-pool accounting determine an actual fresh vacant
slot. The returned insertion equation is proved here, never input validity. -/
theorem allocate (input : TreeFormed tree nextTag)
    (room : tree.tagMapping.mapping.size ≤ 4294967295) :
    ∃ mapping index, tree.tagMapping.insert nextTag = .Inserted mapping index ∧
      mapping.get nextTag = some index ∧ tree.nodes.get index = none := by
  cases available : tree.tagMapping.deassigned.back? with
  | none =>
    let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
    let mapping : UniKeyMap BorTag := {
      mapping := (tree.tagMapping.mapping.filter fun row => row.1 != nextTag).push (nextTag,index)
      deassigned := tree.tagMapping.deassigned }
    have inserted : tree.tagMapping.insert nextTag = .Inserted mapping index := by
      simp [UniKeyMap.insert, available, UniIndex.ofNat?, room, input.nextFresh, mapping, index]
    have endEq : index.toNat = tree.nodes.data.size := by
      simp only [index,UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega : tree.tagMapping.mapping.size < 2^32)]
      exact input.appendAligned available
    have vacant : tree.nodes.get index = none := by
      unfold UniValMap.get
      simp [endEq]
    have selected : mapping.get nextTag = some index := by
      simp [mapping, UniKeyMap.get, Array.find?_push]
      have emptyFind : tree.tagMapping.mapping.find? (fun _ => false) = none :=
        Array.find?_eq_none.mpr (by intro row member; simp)
      rw [emptyFind]
      rfl
    exact ⟨mapping,index,inserted,selected,vacant⟩
  | some index =>
    let mapping : UniKeyMap BorTag := {
      mapping := (tree.tagMapping.mapping.filter fun row => row.1 != nextTag).push (nextTag,index)
      deassigned := tree.tagMapping.deassigned.pop }
    have inserted : tree.tagMapping.insert nextTag = .Inserted mapping index := by
      simp [UniKeyMap.insert, available, input.nextFresh, mapping]
    have vacant := (input.reuseValid index available).2
    have selected : mapping.get nextTag = some index := by
      simp [mapping, UniKeyMap.get, Array.find?_push]
      have emptyFind : tree.tagMapping.mapping.find? (fun _ => false) = none :=
        Array.find?_eq_none.mpr (by intro row member; simp)
      rw [emptyFind]
      rfl
    exact ⟨mapping,index,inserted,selected,vacant⟩

/-- Concrete protection and release follow from the same original tree facts,
including arbitrary reuse pools and permissions at occupied node indices. -/
theorem constructAndRelease (input : TreeFormed tree nextTag) (parentTag : BorTag) (parent : UniIndex)
    (tagged : tree.tagMapping.get parentTag = some parent)
    (room : tree.tagMapping.mapping.size ≤ 4294967295)
    (offset : Size) (initial : LocationState) (protections : ProtectedTags) :
    ∃ after, tree.newChild offset (.concrete parentTag) nextTag
      (Miri.DataStructures.DedupRangeMap.new Size.ZERO initial) (.ReservedFrz false) true =
      ⟨after, .ok ()⟩ ∧ after.releaseProtector nextTag protections = ⟨after,.Released⟩ := by
  obtain ⟨node,present⟩ := input.parentPresent parentTag parent tagged
  obtain ⟨mapping,index,inserted,selected,vacant⟩ := input.allocate room
  have release := BorrowTree.ZeroProtection.Release.concrete_zero_release tree parentTag nextTag index parent
    node mapping inserted tagged present vacant selected (input.vacantClean index vacant) offset initial protections
  obtain ⟨after, constructed⟩ := input.construct parentTag parent tagged room offset initial
  exact ⟨after, constructed, by simpa only [constructed] using release⟩

/-- Wildcard protection creates a fresh unexposed root; its empty reservation
can be released without changing the resulting tree. -/
theorem wildcardConstructAndRelease (input : TreeFormed tree nextTag)
    (room : tree.tagMapping.mapping.size ≤ 4294967295)
    (offset : Size) (initial : LocationState) (protections : ProtectedTags) :
    ∃ after, tree.newChild offset .wildcard nextTag
      (Miri.DataStructures.DedupRangeMap.new Size.ZERO initial) (.ReservedFrz false) true =
      ⟨after, .ok ()⟩ ∧ after.releaseProtector nextTag protections = ⟨after,.Released⟩ := by
  obtain ⟨mapping,index,inserted,selected,vacant⟩ := input.allocate room
  have constructed := BorrowTree.ZeroProtection.Release.wildcard_zero_eq tree nextTag index mapping inserted offset initial
  have release := BorrowTree.ZeroProtection.Release.wildcard_zero_release tree nextTag index mapping inserted selected
    (input.vacantClean index vacant) offset initial protections
  exact ⟨_, constructed, by simpa only [constructed] using release⟩

end TreeFormed
end EmptyFunction.TreeRuntimeInput
