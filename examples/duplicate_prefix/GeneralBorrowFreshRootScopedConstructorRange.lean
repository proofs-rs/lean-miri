import duplicate_prefix.GeneralBorrowFreshRootScopedAttach
import duplicate_prefix.GeneralBorrowFreshInstallation

namespace DuplicatePrefix.GeneralBorrowFreshRootScopedConstructorRange
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshNode GeneralBorrowFreshMaterialization GeneralBorrowFreshInstallation GeneralRangeMapOrigins
open GeneralBorrowFreshRootScopedAttach
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
attribute [local irreducible] UniValMap.insert

/-- The actual modifyRange iterator and its split/merge preparation lift raw
owner-window rows into full other-root callbacks after physical attachment.
Both callback kinds keep the same support and selected-root cutoff. -/
theorem ranged (tree : BorrowTree) (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (index parent : UniIndex) (parentNode newNode : TreeNode) (state : LocationState)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodes.get parent = some parentNode)
    (hidden : newNode.isExposed = false)
    (size : tree.nodes.size ≤ (attachedNodes tree.nodes index parent parentNode newNode).size)
    (nextDepth : GeneralBorrowExposure.ParentDepth (attachedNodes tree.nodes index parent parentNode newNode))
    (mapping : UniKeyMap BorTag) (protections : ProtectedTags) (selected : UniIndex) (maximum : BorTag)
    (offset len : Size) (well : tree.locations.WellFormed)
    (bounds : offset.bytes.toNat+len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (owned : OwnedOn (fun location => Nonempty (GeneralBorrowFreshRootScopedRow.Row tree location protections
      parent selected maximum)) offset.bytes (offset.bytes+len.bytes) tree.locations) :
    let changed := tree.locations.modifyRange offset len (fun _ location => materialized location index state)
    let stage := GeneralBorrowFreshMetadataChildAttach.staged tree index parent parentNode newNode mapping changed.state
    OwnedOn (Framed stage protections parent selected maximum) offset.bytes (offset.bytes+len.bytes) changed.state := by
  dsimp only
  let prepared := tree.locations.iterMut offset len
  let modify : ByteRange → LocationTree → LocationTree :=
    fun _ location => materialized location index state
  let changed := tree.locations.modifyRange offset len modify
  let stage := GeneralBorrowFreshMetadataChildAttach.staged tree index parent parentNode newNode mapping changed.state
  have selectedOwned := (GeneralRangeMapOriginPrepare.selected_owned_on tree.locations offset len well bounds
    (fun location => Nonempty (GeneralBorrowFreshRootScopedRow.Row tree location protections
      parent selected maximum)) offset.bytes (offset.bytes+len.bytes) owned
    (Nat.le_refl _) (Nat.le_refl _)).2.1
  have sizes : changed.state.entries.size = prepared.state.entries.size := by
    dsimp only [changed,prepared]
    rw [GeneralBorrowFreshModify.state_exact tree.locations offset len modify well bounds,GeneralBorrowFreshModify.fold_size]
  intro position valid positive start stop
  have oldValid : position < prepared.state.entries.size := by rw [←sizes];exact valid
  obtain ⟨outputValid,entryEq⟩ := GeneralBorrowFreshModify.entry_exact tree.locations offset len modify
    (fun _ location => materialized_idempotent location index state) well bounds position oldValid
  have rangeEq : (changed.state.entries[position]'valid).range = (prepared.state.entries[position]'oldValid).range := by
    have known := congrArg RangeMapSegment.range entryEq
    by_cases member : position ∈ (tree.locations.iterMut offset len).positions.toList
    · simpa only [member,↓reduceIte] using known
    · simpa only [member,↓reduceIte] using known
  change (changed.state.entries[position]'valid).range.start.toNat < (offset.bytes+len.bytes).toNat at start
  change offset.bytes.toNat < (changed.state.entries[position]'valid).range.stop.toNat at stop
  rw [rangeEq] at start stop
  obtain ⟨old⟩ := selectedOwned position oldValid positive start stop
  have framed : Framed {tree with nodes := attachedNodes tree.nodes index parent parentNode newNode}
      protections parent selected maximum (changed.state.entries[position]'valid).data := by
    apply GeneralBorrowFreshRootScopedAttach.row tree formed depth index parent parentNode newNode vacant parentPresent hidden size
      nextDepth (prepared.state.entries[position]'oldValid).data _ protections selected maximum old
    intro query node present
    have neq : query ≠ index := by intro same;rw [same,vacant] at present;cases present
    have dataEq := congrArg RangeMapSegment.data entryEq
    by_cases member : position ∈ (tree.locations.iterMut offset len).positions.toList
    · simp only [member,↓reduceIte] at dataEq
      rw [dataEq]
      exact GeneralBorrowFreshLocation.get_other _ index query _ neq
    · simp only [member,↓reduceIte] at dataEq
      rw [dataEq]
  exact context _ mapping changed.state _ protections parent selected maximum framed

end DuplicatePrefix.GeneralBorrowFreshRootScopedConstructorRange
