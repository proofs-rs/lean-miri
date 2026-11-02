import duplicate_prefix.GeneralBorrowWildcardVirtualLeaf
import duplicate_prefix.GeneralBorrowWildcardVirtualLeafFold

namespace DuplicatePrefix.GeneralBorrowNewerVirtualRootSkip
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowWildcardVirtualLeaf (effective)
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Raw conditions for skipping a foreign root before inspecting its children.
Disabled requires no SIFA hypothesis. The Cell alternative records the real
Write skip cache explicitly; no operation outcome is an input. -/
def Raw (state : LocationState) : Prop :=
  state.permission = .Disabled ∨
    (state.permission = .Cell ∧ state.idempotentForeignAccess = .Write)

theorem skip_foreign (state : LocationState) (kind : AccessKind) (raw : Raw state) :
    state.skipIfKnownNoop kind .ForeignAccess = .SkipSelfAndChildren := by
  rcases raw with disabled | ⟨cell, cached⟩
  · simp [LocationState.skipIfKnownNoop,AccessRelatedness.isForeign,disabled,Permission.isDisabled]
  · cases kind <;> simp [LocationState.skipIfKnownNoop,AccessRelatedness.isForeign,cell,cached,
      IdempotentForeignAccess.canSkipForeignAccess,IdempotentForeignAccess.fromForeign,
      IdempotentForeignAccess.isLocal,IdempotentForeignAccess.le,IdempotentForeignAccess.rank]

/-- Real wildcard callback on a newer virtual root skips before traversing
children, performs no permission/cache mutation and completes. Arbitrary
children, exposures, protectors and descendant states are allowed; no leaf,
coherent-cache, supporting-exposure or old-tag bound is required.

This is a component theorem for a nonzero physical root position, not a
whole-call input-coverage theorem. The physical root-zero case is excluded:
that case requires a genuine exposed supporting witness. -/
theorem access (tree : BorrowTree) (location : LocationTree) (root : UniIndex)
    (node : TreeNode) (maximum : BorTag) (kind : AccessKind) (protections : ProtectedTags)
    (present : tree.nodes.get root = some node)
    (newer : maximum.value < node.tag.value)
    (raw : Raw (effective location root node)) :
    tree.performWildcardAccessAt location root (some maximum) kind protections true =
      ⟨location,.Completed⟩ := by
  have notPast : ¬ 1 > tree.nodes.size*2+1 := by omega
  have related : location.exposedCache.accessRelatedness root root kind true true = some .ForeignAccess := by
    simpa using GeneralBorrowWildcardRelatednessBounds.root_classify location.exposedCache root kind true
  have skipped := skip_foreign (effective location root node) kind raw
  dsimp only [effective] at skipped
  unfold BorrowTree.performWildcardAccessAt
  simp only [Id.run,bind,pure,ForIn.forIn]
  name_range_scan
  have first : scan () (location,false,.Completed,#[(root,false)],0) =
      .yield (location,false,.Completed,#[],1) := by
    simp only [scan]
    unfold_leaf_helpers
    simp [present,newer,related,notPast]
    unfold_leaf_helpers
    simp [skipped]
  have last : scan () (location,false,.Completed,#[],1) =
      .done (location,false,.Completed,#[],1) := by
    simp [scan]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [first,bind]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [last,bind,pure]
  rfl

/-- Any finite list of such newer virtual roots completes in source order.
Repeated roots are harmless here because every real callback leaves the whole
location unchanged. No leaf or descendant permission restriction is added. -/
theorem fold (tree : BorrowTree) (location : LocationTree) (roots : List UniIndex)
    (maximum : BorTag) (kind : AccessKind) (protections : ProtectedTags)
    (raw : ∀ root ∈ roots, ∃ node, tree.nodes.get root = some node ∧
      maximum.value < node.tag.value ∧ Raw (effective location root node)) :
    GeneralBorrowWildcardVirtualLeafFold.run tree roots location (some maximum) kind protections =
      ⟨location,.Completed⟩ := by
  induction roots with
  | nil => rfl
  | cons root rest ih =>
    obtain ⟨node,present,newer,state⟩ := raw root (by simp)
    have first := access tree location root node maximum kind protections present newer state
    simp only [GeneralBorrowWildcardVirtualLeafFold.run,first,beq_self_eq_true,ite_true]
    exact ih (by intro query member;exact raw query (by simp [member]))

end DuplicatePrefix.GeneralBorrowNewerVirtualRootSkip
