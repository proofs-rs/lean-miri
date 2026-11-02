import duplicate_prefix.ChildConstructor
import duplicate_prefix.ParentBorrowAccess
import duplicate_prefix.MemoryCopyBridge
import duplicate_prefix.Bounds
import Miri.TreeBorrows.RetagPipelineEffectful

/-! The actual effectful mutable slice entry retag and its heap/protector effects. -/
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace DuplicatePrefix.RetagEntry
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows
open Miri.TreeBorrows.RetagPipeline
open Lean Elab Tactic

private def sourceName (suffix : String) : CoreM Name := do
  let names := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith suffix && name.toString.contains "RetagPipelineEffectful" then
      some name else none
  match names with
  | [name] => pure name
  | _ => throwError "expected exact effectful source helper {suffix}"

elab "unfold_entry_source" : tactic => do
  let names ← #[".runReborrow", ".accessTreeForReborrow", ".updateTreeExtra",
    ".buildInsidePermissions", ".addEvent", ".finish", ".fail"].mapM fun suffix =>
      return mkIdent (← sourceName suffix)
  evalTactic (← `(tactic| simp only [$[$names:ident],*]))

elab "unfold_entry_helper " suffix:str : tactic => do
  let name := mkIdent (← sourceName suffix.getString)
  evalTactic (← `(tactic| unfold $name:ident))

elab "entry_tree_update" : term => do
  return mkConst (← sourceName ".updateTreeExtra")

def entryHooks (id : AllocId) (offset len : UInt64) : RetagPipeline.Hooks :=
  { allocationResolution := some ⟨id, Size.ofBytes offset, .concrete ChildBorrow.rootTag⟩,
    freezeVisitor := .ok (DedupRangeMap.new (Size.ofBytes len) true) }

def request (id : AllocId) (offset len : UInt64) : Request :=
  { typeFacts := ⟨true, true, true⟩
    referenceKind := .Mutable
    mode := .FnEntry
    config := ⟨false, false⟩
    layoutSize := Size.ofBytes len
    originalProvenance := some (.concrete id ChildBorrow.rootTag)
    pointeeIsFreeze := true
    preciseInteriorMut := false
    hooks := entryHooks id offset len }

def entryGlobal (id : AllocId) : GlobalState :=
  { nextPointerTag := ChildBorrow.childTag
    rootPointerTags := #[(id, ChildBorrow.rootTag)] }

def protectedGlobal (id : AllocId) : GlobalState :=
  { entryGlobal id with
    nextPointerTag := ⟨3, by decide⟩
    protectedTags := ({} : ProtectedTags).insert ChildBorrow.childTag .StrongProtector }

def protectedFrame (frame : FrameState) (id : AllocId) : FrameState :=
  frame.addProtector id ChildBorrow.childTag

theorem allocate_child_tag (id : AllocId) :
    (entryGlobal id).newPointerTag = .ok
      ({entryGlobal id with nextPointerTag := ⟨3, by decide⟩}, ChildBorrow.childTag) := by
  rfl

theorem register_child_protector (id : AllocId) (frame : FrameState) :
    ({entryGlobal id with nextPointerTag := ⟨3, by decide⟩}).addProtector
      frame id ChildBorrow.childTag .StrongProtector =
      (protectedGlobal id, protectedFrame frame id) := by
  rfl

def updatedMemory {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (tree : BorrowTree) : MemoryState Provenance BorrowTree K :=
  { memory with live := ((memory.live.filter fun row => row.1 != id).push
    (id, { entry with allocation := entry.allocation.setExtra tree })) }

def childTree (capacity offset len : UInt64) : BorrowTree :=
  BorrowRangeAccess.canonicalChildTree ChildBorrow.rootTag ChildBorrow.childTag
    (BorrowRangeAccess.partitionWithInside capacity offset (offset + len)
      BorrowRangeAccess.rootLocation (BorrowRangeAccess.childLocation false))

theorem update_tree_exact {K : Type} [DecidableEq K]
    (memory : MemoryState Provenance BorrowTree K) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree K) (tree : BorrowTree)
    (present : memory.live.find? (fun row => row.1 == id) = some (id, entry)) :
    entry_tree_update memory id tree = .ok (updatedMemory memory id entry tree) := by
  unfold_entry_helper ".updateTreeExtra"
  rw [present]
  exact MemoryCopyBridge.set_live_exact memory id entry (entry.allocation.setExtra tree) present

theorem updated_memory_twice {K : Type}
    (memory : MemoryState Provenance BorrowTree K) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree K) (first second : BorrowTree) :
    updatedMemory (updatedMemory memory id entry first) id
      {entry with allocation := entry.allocation.setExtra first} second =
      updatedMemory memory id entry second := by
  have replaced := MemoryCopyBridge.live_update_twice memory id
    {entry with allocation := entry.allocation.setExtra first}
    {entry with allocation := entry.allocation.setExtra second}
  exact replaced

theorem mutable_entry_full_exact {K E H : Type} [DecidableEq K]
    (memory : MemoryState Provenance BorrowTree K) (frame : FrameState)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (capacity offset len : UInt64) (external : E)
    (present : memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (root : entry.allocation.extra = BorrowTree.new ChildBorrow.rootTag (Size.ofBytes capacity))
    (positive : (0 : UInt64) < len)
    (bounds : offset.toNat + len.toNat ≤ capacity.toNat) :
    let result := Effectful.retagPointerValue ⟨memory, entryGlobal id, frame⟩
      (request id offset len) external (⟨none⟩ : Effectful.Hooks K E H)
    (result.outcome, result.state, result.external) =
      (.ok (some (.concrete id ChildBorrow.childTag)),
        ⟨updatedMemory memory id entry (childTree capacity offset len),
          protectedGlobal id, protectedFrame frame id⟩, external) := by
  have nonzero : len ≠ 0 := by intro h; subst len; exact (UInt64.lt_irrefl 0) positive
  have addOk := DuplicatePrefix.size_add_ok (Size.ofBytes offset) (Size.ofBytes len)
    (by have limit := capacity.toNat_lt; dsimp only [Size.ofBytes]; omega)
  have info := MemoryCopyBridge.live_alloc_info memory id entry present
  have policy : RetagPolicy.create ⟨true, true, true⟩ .Mutable .FnEntry
      ⟨false, false⟩ = some ChildBorrow.fnEntryPolicy := by decide
  have readNotWrite : (AccessKind.Read == .Write) = false := rfl
  have tagsDistinct : ChildBorrow.rootTag ≠ ChildBorrow.childTag := by decide
  have parentAccess := ParentBorrowAccess.parent_with_child_protector
    ChildBorrow.rootTag ChildBorrow.childTag capacity offset len .Read
    tagsDistinct positive bounds
  simp only [BorrowRangeAccess.childProtected, ChildBorrow.childTag,
    ProtectedTags.insert, Array.filter_empty, Array.push_empty] at parentAccess
  have noWrap : ¬ offset + len < offset := by
    have limit := capacity.toNat_lt
    have fits : offset.toNat + len.toNat < 2 ^ 64 := by omega
    simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, Nat.mod_eq_of_lt fits]
    omega
  unfold Effectful.retagPointerValue
  unfold_entry_helper ".addEvent"
  simp [request, entryHooks, RetagTypeShape.reference, RetagTypeShape.classify,
    policy, GlobalState.newPointerTag, entryGlobal,
    ChildBorrow.childTag, BorTag.succ, BorTag.ofUInt64, Id.run, bind, pure]
  unfold_entry_helper ".runReborrow"
  unfold_entry_helper ".addEvent"
  unfold_entry_helper ".buildInsidePermissions"
  simp [entryGlobal, ChildBorrow.fnEntryPolicy,
    GlobalState.isTrackedPointerTag, GlobalState.addProtector, FrameState.addProtector,
    ChildBorrow.mutable_fn_entry_initial_location, RetagPolicy.initialLocationState,
    Permission.strongestIdempotentForeignAccess, Permission.associatedAccess,
    Tree.LocationState.newAccessed, info, present, Except.bind, Except.pure,
    Except.mapError, Id.run, bind, pure]
  unfold_entry_helper ".accessTreeForReborrow"
  unfold_entry_helper ".addEvent"
  simp only [DedupRangeMap.new, DedupRangeMap.iterAll, Size.ofBytes,
    beq_iff_eq, nonzero, ↓reduceIte, ← Array.forIn_toList]
  simp only [List.forIn_cons, List.forIn_nil, Id.run, bind, pure]
  simp only [Permission.associatedAccess, reduceCtorEq, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte, UInt64.sub_zero, addOk, present, root]
  simp only [beq_iff_eq, reduceCtorEq, Bool.false_and, Bool.false_eq_true,
    ↓reduceIte, Size.add, Size.ofBytes, UInt64.add_zero, UInt64.lt_irrefl]
  simp only [readNotWrite, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  simp only [noWrap, ↓reduceIte]
  simp only [ProtectedTags.insert, Array.filter_empty, Array.push_empty]
  erw [parentAccess.1, parentAccess.2]
  let parentTree := { BorrowTree.new ChildBorrow.rootTag (Size.ofBytes capacity) with
    locations := RangeMapNonempty.intervalPartition capacity offset (offset + len)
      BorrowRangeAccess.rootLocation }
  have parentStored := update_tree_exact memory id entry parentTree present
  erw [parentStored]
  have completedSelf : (BorrowTree.BorrowTreeAccessStatus.Completed != .Completed) = false := rfl
  simp only [completedSelf, Bool.false_eq_true, ↓reduceIte, bne_iff_ne,
    nonzero, Bool.true_eq, List.forIn_nil, Id.run, bind, pure]
  simp only [ite_eq_left nonzero, List.forIn_nil, Id.run, bind, pure]
  have updatedPresent : (updatedMemory memory id entry parentTree).live.find?
      (fun row => row.1 == id) =
      some (id, {entry with allocation := entry.allocation.setExtra parentTree}) :=
    MemoryCopyBridge.live_lookup_replaced memory id _
  rw [updatedPresent]
  simp only [Allocation.setExtra, Allocation.mapExtra]
  have childStep := ChildConstructor.new_child_partition_exact
    ChildBorrow.rootTag ChildBorrow.childTag tagsDistinct capacity offset len positive bounds
  simp only [DedupRangeMap.new, Size.ofBytes, beq_iff_eq, nonzero, ↓reduceIte,
    ChildBorrow.fnEntryLocation] at childStep
  erw [childStep]
  have childStored := update_tree_exact (updatedMemory memory id entry parentTree) id
    {entry with allocation := entry.allocation.setExtra parentTree}
    (childTree capacity offset len) updatedPresent
  erw [childStored]
  unfold_entry_helper ".finish"
  unfold_entry_helper ".addEvent"
  simp [Except.bind, Except.pure, Id.run, bind, pure, updated_memory_twice,
    protectedGlobal, entryGlobal, protectedFrame, FrameState.addProtector,
    ProtectedTags.insert, ChildBorrow.childTag]

theorem mutable_entry_exact {K E H : Type} [DecidableEq K]
    (memory : MemoryState Provenance BorrowTree K) (frame : FrameState)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (capacity offset len : UInt64) (external : E)
    (present : memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (root : entry.allocation.extra = BorrowTree.new ChildBorrow.rootTag (Size.ofBytes capacity))
    (positive : (0 : UInt64) < len)
    (bounds : offset.toNat + len.toNat ≤ capacity.toNat) :
    let result := Effectful.retagPointerValue ⟨memory, entryGlobal id, frame⟩
      (request id offset len) external (⟨none⟩ : Effectful.Hooks K E H)
    (result.outcome, result.state) =
      (.ok (some (.concrete id ChildBorrow.childTag)),
        ⟨updatedMemory memory id entry (childTree capacity offset len),
          protectedGlobal id, protectedFrame frame id⟩) := by
  exact congrArg (fun p => (p.1, p.2.1))
    (mutable_entry_full_exact (H := H) memory frame id entry capacity offset len external
      present root positive bounds)

#print axioms mutable_entry_full_exact
#print axioms mutable_entry_exact

end DuplicatePrefix.RetagEntry

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.RetagEntry.mutable_entry_exact,
      ``DuplicatePrefix.RetagEntry.mutable_entry_full_exact,
      ``DuplicatePrefix.RetagEntry.update_tree_exact,
      ``DuplicatePrefix.RetagEntry.updated_memory_twice] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"
