import duplicate_prefix.GeneralBorrowTwoRootPolicySeed

namespace DuplicatePrefix.GeneralBorrowPolicyReservationForeignRead
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowTwoRootConstructed (first second)
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

set_option autoImplicit false in
/-- An absent cache and the real nonzero-root wildcard flag select foreign
Read. The policy reservation's Read SIFA skips the whole component before any
permission/cache mutation. No operation-success premise is used. -/
theorem access (tree : BorrowTree) (location : LocationTree) (root : UniIndex)
    (node : TreeNode) (maximum : BorTag)
    (present : tree.nodes.get root = some node)
    (stored : location.perms.get root = some GeneralBorrowTwoRootPolicySeed.reserved)
    (cache : location.exposedCache.nodes.get root = none)
    (newer : maximum.value < node.tag.value) :
    tree.performWildcardAccessAt location root (some maximum) .Read {} true =
      ⟨location,.Completed⟩ := by
  have notPast : ¬ 1 > tree.nodes.size*2+1 := by omega
  have related : location.exposedCache.accessRelatedness root root .Read true true = some .ForeignAccess := by
    simp [ExposedCache.accessRelatedness,cache,Id.run,pure]
  unfold BorrowTree.performWildcardAccessAt
  simp only [Id.run,bind,pure,ForIn.forIn]
  name_range_scan
  have step1 : scan () (location,false,.Completed,#[(root,false)],0) =
      .yield (location,false,.Completed,#[],1) := by
    simp only [scan]
    unfold_leaf_helpers
    simp [present,stored,newer,related,notPast,GeneralBorrowTwoRootPolicySeed.reserved,
      LocationState.skipIfKnownNoop,AccessRelatedness.isForeign,
      IdempotentForeignAccess.fromForeign,IdempotentForeignAccess.canSkipForeignAccess,
      Id.run,bind,pure]
    unfold_leaf_helpers
    simp [IdempotentForeignAccess.isLocal,IdempotentForeignAccess.le]
  have step2 : scan () (location,false,.Completed,#[],1) =
      .done (location,false,.Completed,#[],1) := by
    simp [scan,bind,pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [step1,bind,pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [step2,bind,pure]
  rfl

set_option autoImplicit false in
/-- The actual preactivation policy seed has exactly this stable reservation
component at root position one. It remains writable by a later local Write. -/
theorem policy_component (rootTag parentTag : BorTag) (ordered : rootTag.value < parentTag.value) :
    (GeneralBorrowTwoRootPolicySeed.tree rootTag parentTag).performWildcardAccessAt
      GeneralBorrowTwoRootPolicySeed.location second (some rootTag) .Read {} true =
      ⟨GeneralBorrowTwoRootPolicySeed.location,.Completed⟩ := by
  exact access _ _ _ _ _ rfl rfl rfl ordered

end DuplicatePrefix.GeneralBorrowPolicyReservationForeignRead
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowPolicyReservationForeignRead.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved policy reservation foreign-read dependency {name}: {dependency}"
