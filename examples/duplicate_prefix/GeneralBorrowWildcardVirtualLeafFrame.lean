import duplicate_prefix.GeneralBorrowWildcardRootCacheFrame

namespace DuplicatePrefix.GeneralBorrowWildcardVirtualLeafFrame
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowNodeUpdate
open DuplicatePrefix.GeneralBorrowWildcardVirtualLeaf
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Every row outside the visited virtual root retains its actual map lookup. -/
def Frame (root : UniIndex) (before after : LocationTree) : Prop :=
  ∀ query, query ≠ root → after.perms.get query = before.perms.get query ∧
    after.exposedCache.nodes.get query = before.exposedCache.nodes.get query

theorem materialized_other (location : LocationTree) (root : UniIndex) (node : TreeNode)
    (query : UniIndex) (different : query ≠ root) :
    (materialized location root node).perms.get query = location.perms.get query := by
  unfold materialized UniValMap.orInsert
  split
  · rfl
  · exact GeneralBorrowFreshLocation.get_other _ root query _ different

theorem materialized_effective (location : LocationTree) (root : UniIndex) (node : TreeNode) :
    effective (materialized location root node) root node = effective location root node := by
  unfold materialized effective UniValMap.orInsert
  split <;> simp_all [GeneralBorrowFreshLocation.get_same]

/-- Actual foreign leaf execution preserves ownership and frames all other
permission/cache rows. Parentless is needed for the cache frame; ParentDepth
also discharges the actual cache walk's completion condition. -/
theorem foreign_access (tree : BorrowTree) (location : LocationTree) (root : UniIndex)
    (node : TreeNode) (maximum : Option BorTag) (kind : AccessKind) (protections : ProtectedTags)
    (present : tree.nodes.get root = some node) (leaf : node.children = #[])
    (parents : GeneralBorrowExposure.ParentDepth tree.nodes) (parentless : node.parent = none)
    (foreignData : onlyForeign node maximum = true ∨
      GeneralBorrowWildcardRelatednessBounds.count location.exposedCache root kind = 0)
    (owned : GeneralBorrowPermissions.ForeignOwned (effective location root node)
      (protections.contains node.tag)) :
    ∃ after, tree.performWildcardAccessAt location root maximum kind protections true =
      ⟨after,.Completed⟩ ∧
      GeneralBorrowPermissions.ForeignOwned (effective after root node) (protections.contains node.tag) ∧
      Frame root location after := by
  have nonempty : 0 < tree.nodes.size := by
    have valid := lookup_valid tree.nodes root node present
    unfold UniValMap.size
    omega
  have notPast : ¬ 2 > tree.nodes.size*2+1 := by omega
  have notPast1 : ¬ 1 > tree.nodes.size*2+1 := by omega
  have related : location.exposedCache.accessRelatedness root root kind true
      (onlyForeign node maximum) = some .ForeignAccess := by
    rw [GeneralBorrowWildcardRelatednessBounds.root_classify]
    rcases foreignData with clamp | zero
    · simp [clamp]
    · simp [zero]
  unfold onlyForeign at related
  obtain skip | ⟨recorded,next,transition,record,access,preserved⟩ :=
    GeneralBorrowPermissions.visit_success (effective location root node) .ForeignAccess
      (protections.contains node.tag) kind owned
  · refine ⟨location,?_,owned,fun _ _ => ⟨rfl,rfl⟩⟩
    unfold BorrowTree.performWildcardAccessAt
    simp only [Id.run,bind,pure,ForIn.forIn]
    name_range_scan
    have step1 : scan () (location,false,.Completed,#[(root,false)],0) =
        .yield (location,false,.Completed,#[],1) := by
      simp only [scan]
      try unfold_leaf_helpers
      simp [present,notPast1,Id.run,bind,pure]
      try unfold_leaf_helpers
      cases maximum <;> simp_all [effective,AccessRelatedness.isForeign]
      all_goals try unfold_leaf_helpers
      all_goals simp_all [effective,AccessRelatedness.isForeign]
    have step2 : scan () (location,false,.Completed,#[],1) =
        .done (location,false,.Completed,#[],1) := by simp [scan,bind,pure]
    rw [Lean.Loop.forIn_eq_of_monadTail]
    simp only [step1,bind,pure]
    rw [Lean.Loop.forIn_eq_of_monadTail]
    simp only [step2,bind,pure]
    rfl
  · have recurse : (effective location root node).skipIfKnownNoop kind .ForeignAccess = .Recurse := by
      unfold LocationState.recordNewAccess at record
      split at record <;> simp_all
    let updated : LocationTree := {location with perms :=
      ((location.perms.orInsert root node.defaultLocationState).1.insert root recorded).insert root next}
    let update := location.exposedCache.updateExposure tree.nodes root
      ((effective location root node).permission.strongestAllowedLocalAccess (protections.contains node.tag))
      (next.permission.strongestAllowedLocalAccess (protections.contains node.tag))
    have cacheOK : update.outcome = .ok () :=
      GeneralBorrowExposure.update_exposure_succeeds location.exposedCache tree.nodes parents root node present _ _
    let after : LocationTree := {updated with exposedCache :=
      if node.isExposed && !transition.isNoop then update.cache else location.exposedCache}
    have same : after.perms.get root = some next := by
      dsimp only [after,updated]
      exact GeneralBorrowFreshLocation.get_same ((location.perms.orInsert root node.defaultLocationState).1.insert root recorded) root next
    have afterOwned : GeneralBorrowPermissions.ForeignOwned (effective after root node)
        (protections.contains node.tag) := by
      simpa only [effective,same,Option.getD_some,GeneralBorrowPermissions.Owned] using preserved
    have afterFrame : Frame root location after := by
      intro query different
      constructor
      · dsimp only [after,updated]
        rw [GeneralBorrowFreshLocation.get_other _ root query next different,
          GeneralBorrowFreshLocation.get_other _ root query recorded different]
        exact materialized_other location root node query different
      · change (if node.isExposed && !transition.isNoop then update.cache else location.exposedCache).nodes.get query = _
        by_cases active : (node.isExposed && !transition.isNoop) = true
        · rw [if_pos active]
          exact GeneralBorrowWildcardRootCacheFrame.update_other location.exposedCache tree.nodes root query node
            present parentless different _ _
        · rw [if_neg active]
    refine ⟨after,?_,afterOwned,afterFrame⟩
    clear afterOwned afterFrame same
    unfold BorrowTree.performWildcardAccessAt
    simp only [Id.run,bind,pure,ForIn.forIn]
    name_range_scan
    have step1 : scan () (location,false,.Completed,#[(root,false)],0) =
        .yield (location,false,.Completed,#[(root,true)],1) := by
      simp only [scan]
      try unfold_leaf_helpers
      simp [present,leaf,notPast1,Id.run,bind,pure]
      try unfold_leaf_helpers
      cases maximum <;> simp_all [effective,AccessRelatedness.isForeign,leaf]
      all_goals try unfold_leaf_helpers
      all_goals simp_all [effective,AccessRelatedness.isForeign,leaf]
    let witness := node.isExposed &&
      ((effective location root node).permission.strongestAllowedLocalAccess (protections.contains node.tag)).allows kind &&
      (maximum.isNone || maximum.any (fun tag => tag.value >= node.tag.value))
    have step2 : scan () (location,false,.Completed,#[(root,true)],1) =
        .yield (after,witness,.Completed,#[],2) := by
      dsimp only [witness]
      simp only [scan]
      try unfold_leaf_helpers
      simp [present,notPast,Id.run,bind,pure]
      try unfold_leaf_helpers
      cases maximum <;> simp_all [effective,after,updated,update,UniValMap.orInsert,
        LocationState.AccessResult.resultingState]
      all_goals try unfold_leaf_helpers
      all_goals try simp_all [effective,after,updated,update,UniValMap.orInsert,LocationState.AccessResult.resultingState]
      all_goals cases stored : location.perms.get root <;> simp_all [effective,after,updated,update,UniValMap.orInsert,LocationState.AccessResult.resultingState]
      all_goals try simp only [cacheOK]
      all_goals split <;> simp_all [after,updated,update,UniValMap.orInsert,LocationState.AccessResult.resultingState]
      all_goals cases exposedEq : node.isExposed <;> simp_all
      all_goals split <;> try simp_all [Bool.and_eq_false_iff]
      all_goals cases allowedEq : ((effective location root node).permission.strongestAllowedLocalAccess (protections.contains node.tag)).allows kind <;> simp_all [effective]
      all_goals simp_all only [UInt64.lt_iff_toNat_lt,UInt64.le_iff_toNat_le]
      all_goals grind
    have step3 : scan () (after,witness,.Completed,#[],2) =
        .done (after,witness,.Completed,#[],2) := by simp [scan,bind,pure]
    rw [Lean.Loop.forIn_eq_of_monadTail]
    simp only [step1,bind,pure]
    rw [Lean.Loop.forIn_eq_of_monadTail]
    simp only [step2,bind,pure]
    rw [Lean.Loop.forIn_eq_of_monadTail]
    simp only [step3,bind,pure]
    simp

/-- Arbitrary self-counts select either the foreign or materialization branch.
Both preserve effective foreign ownership and frame all other actual rows. -/
theorem access (tree : BorrowTree) (location : LocationTree) (root : UniIndex)
    (node : TreeNode) (maximum : Option BorTag) (kind : AccessKind) (protections : ProtectedTags)
    (present : tree.nodes.get root = some node) (leaf : node.children = #[])
    (parents : GeneralBorrowExposure.ParentDepth tree.nodes) (parentless : node.parent = none)
    (owned : GeneralBorrowPermissions.ForeignOwned (effective location root node)
      (protections.contains node.tag)) :
    ∃ after, tree.performWildcardAccessAt location root maximum kind protections true =
      ⟨after,.Completed⟩ ∧
      GeneralBorrowPermissions.ForeignOwned (effective after root node) (protections.contains node.tag) ∧
      Frame root location after := by
  by_cases foreign : onlyForeign node maximum = true ∨
      GeneralBorrowWildcardRelatednessBounds.count location.exposedCache root kind = 0
  · exact foreign_access tree location root node maximum kind protections present leaf parents parentless foreign owned
  · have notOnly : onlyForeign node maximum = false := by
      cases value : onlyForeign node maximum <;> simp_all
    have nonzero : GeneralBorrowWildcardRelatednessBounds.count location.exposedCache root kind ≠ 0 := by
      intro zero
      exact foreign (.inr zero)
    refine ⟨materialized location root node,
      GeneralBorrowWildcardVirtualLeaf.either_access tree location root node maximum kind protections present leaf nonzero notOnly,?_,?_⟩
    · rw [materialized_effective]
      exact owned
    · intro query different
      exact ⟨materialized_other location root node query different,rfl⟩

end DuplicatePrefix.GeneralBorrowWildcardVirtualLeafFrame
