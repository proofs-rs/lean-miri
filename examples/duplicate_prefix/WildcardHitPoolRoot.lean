import duplicate_prefix.EmptyForestSharedPoolNext
import duplicate_prefix.WildcardHitRootDepth

namespace DuplicatePrefix.WildcardHitPoolRoot
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshNode DuplicatePrefix.GeneralBorrowNodeUpdate
open GeneralBorrowExposure (ParentDepth)
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] UniValMap.insert

/-- Raw actual allocator choice for a new wildcard root. No rank slack is
required because the new node has no parent. -/
inductive Slot (tree : BorrowTree) where
  | append (noFree : tree.tagMapping.deassigned.back? = none)
      (aligned : tree.tagMapping.mapping.size = tree.nodes.data.size)
      (fits : tree.tagMapping.mapping.size ≤ 4294967295)
  | reuse (index : UniIndex) (available : tree.tagMapping.deassigned.back? = some index)
      (bounded : index.toNat < tree.nodes.data.size) (vacant : tree.nodes.get index = none)

namespace Slot
variable {tree : BorrowTree}
def index : Slot tree → UniIndex
  | .append .. => ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
  | .reuse child .. => child
def free : Slot tree → Array UniIndex
  | .append .. => tree.tagMapping.deassigned
  | .reuse .. => tree.tagMapping.deassigned.pop
def mapping (slot : Slot tree) (tag : BorTag) : UniKeyMap BorTag :=
  ⟨tree.tagMapping.mapping.push (tag,slot.index),slot.free⟩
def after (slot : Slot tree) (tag : BorTag) : BorrowTree :=
  WildcardHitZeroConstructor.installed tree (slot.mapping tag) slot.index tag (.ReservedFrz false) .None
def growth : Slot tree → Nat | .append .. => 1 | .reuse .. => 0

theorem vacant (slot : Slot tree) : tree.nodes.get slot.index = none := by
  cases slot with
  | append noFree aligned fits =>
    have endEq : (⟨UInt32.ofNat tree.tagMapping.mapping.size⟩ : UniIndex).toNat = tree.nodes.data.size := by
      simp only [UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega : tree.tagMapping.mapping.size < 2^32)]
      exact aligned
    change tree.nodes.get (⟨UInt32.ofNat tree.tagMapping.mapping.size⟩ : UniIndex) = none
    unfold UniValMap.get
    simp [endEq]
  | reuse child available bounded vacant => exact vacant

/-- Actual zero protected FnEntry wildcard child, with the source's genuine
free-slot reuse or append branch and no constructor-success premise. -/
theorem child (slot : Slot tree) (tag : BorTag) (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (offset : UInt64) :
    tree.newChild (Size.ofBytes offset) .wildcard tag
      (DedupRangeMap.new Size.ZERO ChildBorrow.fnEntryLocation) (.ReservedFrz false) true =
      ⟨slot.after tag,.ok ()⟩ := by
  cases slot with
  | append noFree aligned fits =>
    exact WildcardHitZeroConstructor.append tree tag fresh noFree fits (.ReservedFrz false) .None true rfl rfl rfl _ offset
  | reuse child available bounded vacant =>
    exact WildcardHitZeroConstructor.reuse tree tag child fresh available (.ReservedFrz false) .None true rfl rfl rfl _ offset

theorem size (slot : Slot tree) (tag : BorTag) : (slot.after tag).nodes.size = tree.nodes.size+slot.growth := by
  cases slot with
  | append noFree aligned fits =>
    have endEq : (⟨UInt32.ofNat tree.tagMapping.mapping.size⟩ : UniIndex).toNat = tree.nodes.data.size := by
      simp only [UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega : tree.tagMapping.mapping.size < 2^32)]
      exact aligned
    exact append_size tree.nodes _ (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None) endEq
  | reuse child available bounded vacant =>
    exact GeneralBorrowFreshReuseNode.bounded_size tree.nodes child _ bounded

private noncomputable def reuse_depth (nodes : UniValMap TreeNode) (before : ParentDepth nodes)
    (index : UniIndex) (node : TreeNode) (bounded : index.toNat < nodes.data.size)
    (vacant : nodes.get index = none) (parentless : node.parent = none) : ParentDepth (nodes.insert index node) where
  depth := fun query => if query = index then 0 else before.depth query
  bounded := by
    intro query value lookup
    rw [GeneralBorrowFreshReuseNode.bounded_size nodes index node bounded]
    by_cases same : query = index
    · simp only [same,ite_true];omega
    · simp only [same,ite_false]
      rw [GeneralBorrowFreshLocation.get_other nodes index query node same] at lookup
      exact before.bounded query value lookup
  parent := by
    intro query value lookup earlier edge
    by_cases same : query = index
    · subst query
      rw [GeneralBorrowFreshLocation.get_same] at lookup
      cases lookup
      rw [parentless] at edge
      cases edge
    · rw [GeneralBorrowFreshLocation.get_other nodes index query node same] at lookup
      obtain ⟨ancestor,present,smaller⟩ := before.parent query value lookup earlier edge
      have different : earlier ≠ index := by
        intro equal
        rw [equal,vacant] at present
        cases present
      refine ⟨ancestor,(GeneralBorrowFreshLocation.get_other nodes index earlier node different).trans present,?_⟩
      simpa only [different,same,ite_false] using smaller

noncomputable def depth (slot : Slot tree) (before : ParentDepth tree.nodes) (tag : BorTag) : ParentDepth (slot.after tag).nodes := by
  cases slot with
  | append noFree aligned fits =>
    have endEq : (⟨UInt32.ofNat tree.tagMapping.mapping.size⟩ : UniIndex).toNat = tree.nodes.data.size := by
      simp only [UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega : tree.tagMapping.mapping.size < 2^32)]
      exact aligned
    exact WildcardHitRootDepth.append_root tree.nodes before _ _ endEq rfl
  | reuse child available bounded vacant => exact reuse_depth tree.nodes before child _ bounded vacant rfl

theorem allocator (slot : Slot tree) (tag : BorTag)
    (pool : GeneralBorrowFreshAllocatorInvariant.Pool tree.nodes tree.tagMapping.deassigned)
    (accounting : GeneralBorrowFreshStagePool.Accounting tree) :
    GeneralBorrowFreshAllocatorInvariant.Pool (slot.after tag).nodes (slot.after tag).tagMapping.deassigned ∧
    GeneralBorrowFreshStagePool.Accounting (slot.after tag) := by
  refine ⟨?_,?_⟩
  · cases slot with
    | append noFree aligned fits =>
      have empty := Array.back?_eq_none_iff.mp noFree
      change GeneralBorrowFreshAllocatorInvariant.Pool _ tree.tagMapping.deassigned
      rw [empty]
      exact ⟨by simp,by simp,by simp⟩
    | reuse child available bounded vacant =>
      exact GeneralBorrowFreshAllocatorInvariant.consume tree.nodes tree.tagMapping.deassigned pool child available _
  · unfold GeneralBorrowFreshStagePool.Accounting
    change (slot.mapping tag).mapping.size+(slot.mapping tag).deassigned.size = (slot.after tag).nodes.size
    rw [size slot tag]
    simp only [mapping,Array.size_push]
    unfold GeneralBorrowFreshStagePool.Accounting at accounting
    cases slot with
    | append noFree aligned fits =>
      have empty := Array.back?_eq_none_iff.mp noFree
      simp only [free,growth,empty,Array.size_empty,Nat.add_zero]
      simpa only [empty,Array.size_empty,Nat.add_zero] using congrArg (fun n => n+1) accounting
    | reuse child available bounded vacant =>
      have positive : 0 < tree.tagMapping.deassigned.size := by
        obtain ⟨rest,eq⟩ := Array.back?_eq_some_iff.mp available
        rw [eq,Array.size_push];omega
      simp only [free,growth,Array.size_pop,Nat.add_zero]
      omega

theorem vacant_clean (slot : Slot tree) (tag : BorTag) (clean : GeneralBorrowGcVacantClean.VacantClean tree) :
    GeneralBorrowGcVacantClean.VacantClean (slot.after tag) :=
  GeneralBorrowGcVacantClean.insert_preserves tree slot.index _ clean

theorem release (slot : Slot tree) (tag : BorTag) (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (clean : GeneralBorrowGcVacantClean.VacantClean tree) (protections : ProtectedTags) :
    (slot.after tag).releaseProtector tag protections = ⟨slot.after tag,.Released⟩ := by
  apply EmptyForestUnmaterializedRelease.release (slot.after tag) tag slot.index
    (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None)
  · exact GeneralBorrowTagMap.pushed_get_new tree.tagMapping tag fresh slot.index slot.free
  · exact GeneralBorrowFreshLocation.get_same tree.nodes slot.index _
  · rfl
  · exact clean slot.index slot.vacant

end Slot

/-- Select the real wildcard-root allocator branch from arbitrary coherent free
pool data, without a successful tag-insertion premise. -/
def factory (tree : BorrowTree)
    (pool : GeneralBorrowFreshAllocatorInvariant.Pool tree.nodes tree.tagMapping.deassigned)
    (accounting : GeneralBorrowFreshStagePool.Accounting tree)
    (fits : tree.tagMapping.mapping.size ≤ 4294967295) : Slot tree :=
  match available : tree.tagMapping.deassigned.back? with
  | none => .append available (GeneralBorrowFreshStagePool.empty_aligned tree accounting available) fits
  | some index => .reuse index available (pool.bounded index (Array.mem_of_back? available))
      (pool.vacant index (Array.mem_of_back? available))

end DuplicatePrefix.WildcardHitPoolRoot
