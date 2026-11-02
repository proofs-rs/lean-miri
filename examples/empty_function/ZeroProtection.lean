import Miri.Interpreter.TypedRetag

namespace EmptyFunction.ZeroProtection
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.DataStructures Miri.Interpreter
set_option autoImplicit false

/-- Tag freshness and a u32 capacity bound suffice for allocation, including
arbitrary reusable slots. Neither insertion success nor an empty free pool is
an input. -/
theorem insert_fresh {A : Type} [BEq A] (map : UniKeyMap A) (key : A)
    (fresh : map.get key = none) (room : map.mapping.size ≤ 4294967295) :
    ∃ after index, map.insert key = .Inserted after index := by
  unfold UniKeyMap.insert
  cases available : map.deassigned.back? with
  | none =>
    simp [UniIndex.ofNat?, room, fresh]
  | some index => simp [fresh]

/-- Empty unit protection has an empty inside map: it cannot request byte
accesses or materialize per-byte permissions through that map. -/
theorem empty_inside (initial : Tree.LocationState) :
    (DedupRangeMap.new Size.ZERO initial).iterAll = #[] := by rfl

/-- A wildcard zero-byte protected child is a fresh lazy root. The theorem
covers both allocator branches without any successful-constructor premise. -/
theorem wildcard_child (tree : BorrowTree) (tag : BorTag)
    (fresh : tree.tagMapping.get tag = none)
    (room : tree.tagMapping.mapping.size ≤ 4294967295) (offset : Size)
    (initial : Tree.LocationState) :
    ∃ after index, tree.newChild offset .wildcard tag
      (DedupRangeMap.new Size.ZERO initial) (.ReservedFrz false) true =
      ⟨after, .ok ()⟩ ∧ after.locations = tree.locations ∧
      after.roots = tree.roots.push index := by
  obtain ⟨mapping, index, inserted⟩ := insert_fresh tree.tagMapping tag fresh room
  let node : TreeNode := {
    tag := tag, parent := none, children := #[]
    defaultInitialPermission := .ReservedFrz false, defaultInitialSifa := .None, isExposed := false }
  let after : BorrowTree := { tree with
    tagMapping := mapping
    nodes := tree.nodes.insert index node, roots := tree.roots.push index }
  refine ⟨after, index, ?_, rfl, rfl⟩
  simp [BorrowTree.newChild, inserted, after, node, DedupRangeMap.new, DedupRangeMap.iterAll,
    Permission.isInitial, Permission.isUnique, Permission.strongestIdempotentForeignAccess, Size.ZERO, Size.ofBytes]

end EmptyFunction.ZeroProtection
