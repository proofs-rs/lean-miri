import duplicate_prefix.GeneralBorrowWildcardRelatednessBounds
import duplicate_prefix.GeneralBorrowWildcardLeaf
import duplicate_prefix.GeneralBorrowPermissions
import duplicate_prefix.GeneralBorrowExposure

namespace DuplicatePrefix.GeneralBorrowWildcardVirtualLeaf
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowNodeUpdate
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Source pre-visit tag filter, retained as data rather than an access outcome. -/
def onlyForeign (node : TreeNode) (maximum : Option BorTag) : Bool :=
  match maximum with
  | some tag => tag.value < node.tag.value
  | none => false

def effective (location : LocationTree) (root : UniIndex) (node : TreeNode) : LocationState :=
  (location.perms.get root).getD node.defaultLocationState

def materialized (location : LocationTree) (root : UniIndex) (node : TreeNode) : LocationTree :=
  { location with perms := (location.perms.orInsert root node.defaultLocationState).1 }

/-- With a real local exposure possibility, the virtual root adds a foreign
possibility. The actual visitor therefore materializes the leaf state but
performs no permission transition. No exposure/protector/ownership restriction
is needed on this Either branch. -/
theorem either_access (tree : BorrowTree) (location : LocationTree) (root : UniIndex)
    (node : TreeNode) (maximum : Option BorTag) (kind : AccessKind) (protections : ProtectedTags)
    (present : tree.nodes.get root = some node) (leaf : node.children = #[])
    (localPossible : GeneralBorrowWildcardRelatednessBounds.count location.exposedCache root kind ≠ 0)
    (notOnlyForeign : onlyForeign node maximum = false) :
    tree.performWildcardAccessAt location root maximum kind protections true =
      ⟨materialized location root node,.Completed⟩ := by
  have nonempty : 0 < tree.nodes.size := by
    have valid := lookup_valid tree.nodes root node present
    unfold UniValMap.size
    omega
  have notPast : ¬ 2 > tree.nodes.size*2+1 := by omega
  have notPast1 : ¬ 1 > tree.nodes.size*2+1 := by omega
  have related := GeneralBorrowWildcardRelatednessBounds.root_classify
    location.exposedCache root kind (onlyForeign node maximum)
  simp only [notOnlyForeign, Bool.false_or, beq_iff_eq, localPossible, ↓reduceIte] at related
  have relatedActual : location.exposedCache.accessRelatedness root root kind true
      (onlyForeign node maximum) = some .EitherAccess := by
    rw [notOnlyForeign]
    exact related
  unfold onlyForeign at relatedActual
  unfold BorrowTree.performWildcardAccessAt
  simp only [Id.run,bind,pure,ForIn.forIn]
  name_range_scan
  have step1 : scan () (location,false,.Completed,#[(root,false)],0) =
      .yield (location,false,.Completed,#[(root,true)],1) := by
    simp only [scan]
    unfold_leaf_helpers
    simp [present,leaf,relatedActual,related,notPast1,Id.run,bind,pure]
    try unfold_leaf_helpers
    try simp [leaf,relatedActual]
    try unfold_leaf_helpers
    cases maximum <;> simp_all [onlyForeign]
    all_goals try unfold_leaf_helpers
    all_goals simp_all
  let witness := node.isExposed &&
    ((effective location root node).permission.strongestAllowedLocalAccess (protections.contains node.tag)).allows kind &&
    (maximum.isNone || maximum.any (fun tag => tag.value >= node.tag.value))
  have step2 : scan () (location,false,.Completed,#[(root,true)],1) =
      .yield (materialized location root node,witness,.Completed,#[],2) := by
    simp only [scan]
    unfold_leaf_helpers
    simp [present,leaf,relatedActual,related,notPast,Id.run,bind,pure,UniValMap.orInsert,
      materialized,effective,witness]
    all_goals try unfold_leaf_helpers
    all_goals try rw [relatedActual]
    all_goals try simp [relatedActual,related,materialized,effective,witness]
    all_goals try unfold_leaf_helpers
    all_goals try rw [relatedActual]
    all_goals try simp [relatedActual,related,materialized,effective,witness]
    all_goals cases maximum <;> simp_all [onlyForeign,materialized,effective,UniValMap.orInsert]
    all_goals split <;> try simp_all [Bool.and_eq_false_iff]
    all_goals cases exposedEq : node.isExposed <;> simp_all
  have step3 : scan () (materialized location root node,witness,.Completed,#[],2) =
      .done (materialized location root node,witness,.Completed,#[],2) := by
    simp [scan,bind,pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [step1,bind,pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [step2,bind,pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [step3,bind,pure]
  simp

/-- A foreign-only virtual leaf with no exposure executes the actual source
skip/record/transition pipeline under data ownership. The cache is untouched. -/
theorem foreign_unexposed (tree : BorrowTree) (location : LocationTree) (root : UniIndex)
    (node : TreeNode) (maximum : Option BorTag) (kind : AccessKind) (protections : ProtectedTags)
    (present : tree.nodes.get root = some node) (leaf : node.children = #[])
    (unexposed : node.isExposed = false)
    (foreignData : onlyForeign node maximum = true ∨
      GeneralBorrowWildcardRelatednessBounds.count location.exposedCache root kind = 0)
    (owned : GeneralBorrowPermissions.ForeignOwned (effective location root node)
      (protections.contains node.tag)) :
    ∃ after, tree.performWildcardAccessAt location root maximum kind protections true =
      ⟨after,.Completed⟩ ∧ after.exposedCache = location.exposedCache := by
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
  · refine ⟨location,?_,rfl⟩
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
    let after : LocationTree := {location with perms :=
      ((location.perms.orInsert root node.defaultLocationState).1.insert root recorded).insert root next}
    refine ⟨after,?_,rfl⟩
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
    have step2 : scan () (location,false,.Completed,#[(root,true)],1) =
        .yield (after,false,.Completed,#[],2) := by
      simp only [scan]
      try unfold_leaf_helpers
      simp [present,unexposed,notPast,Id.run,bind,pure]
      try unfold_leaf_helpers
      cases maximum <;> simp_all [effective,after,UniValMap.orInsert,
        LocationState.AccessResult.resultingState]
      all_goals try unfold_leaf_helpers
      all_goals try simp_all [effective,after,UniValMap.orInsert,LocationState.AccessResult.resultingState]
      all_goals cases stored : location.perms.get root <;> simp_all [effective,after,UniValMap.orInsert,LocationState.AccessResult.resultingState]
    have step3 : scan () (after,false,.Completed,#[],2) =
        .done (after,false,.Completed,#[],2) := by simp [scan,bind,pure]
    rw [Lean.Loop.forIn_eq_of_monadTail]
    simp only [step1,bind,pure]
    rw [Lean.Loop.forIn_eq_of_monadTail]
    simp only [step2,bind,pure]
    rw [Lean.Loop.forIn_eq_of_monadTail]
    simp only [step3,bind,pure]
    rfl

/-- A virtual foreign leaf executes the actual skip/record/permission pipeline
and any exposed-cache update. Raw parent-depth data discharges cache traversal
errors; arbitrary cache counts and exposure levels are permitted. -/
theorem foreign_access (tree : BorrowTree) (location : LocationTree) (root : UniIndex)
    (node : TreeNode) (maximum : Option BorTag) (kind : AccessKind) (protections : ProtectedTags)
    (present : tree.nodes.get root = some node) (leaf : node.children = #[])
    (parents : GeneralBorrowExposure.ParentDepth tree.nodes)
    (foreignData : onlyForeign node maximum = true ∨
      GeneralBorrowWildcardRelatednessBounds.count location.exposedCache root kind = 0)
    (owned : GeneralBorrowPermissions.ForeignOwned (effective location root node)
      (protections.contains node.tag)) :
    ∃ after, tree.performWildcardAccessAt location root maximum kind protections true =
      ⟨after,.Completed⟩ := by
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
  · refine ⟨location,?_⟩
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
    let after := if node.isExposed && !transition.isNoop then
      {updated with exposedCache := update.cache} else updated
    refine ⟨after,?_⟩
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

/-- Every childless virtual-root component completes under raw parent-depth and
foreign-ownership data, for arbitrary self cache counts, either access kind,
optional tag cutoff, exposure flag and protector map. -/
theorem access (tree : BorrowTree) (location : LocationTree) (root : UniIndex)
    (node : TreeNode) (maximum : Option BorTag) (kind : AccessKind) (protections : ProtectedTags)
    (present : tree.nodes.get root = some node) (leaf : node.children = #[])
    (parents : GeneralBorrowExposure.ParentDepth tree.nodes)
    (owned : GeneralBorrowPermissions.ForeignOwned (effective location root node)
      (protections.contains node.tag)) :
    ∃ after, tree.performWildcardAccessAt location root maximum kind protections true =
      ⟨after,.Completed⟩ := by
  by_cases foreign : onlyForeign node maximum = true ∨
      GeneralBorrowWildcardRelatednessBounds.count location.exposedCache root kind = 0
  · exact foreign_access tree location root node maximum kind protections present leaf parents foreign owned
  · have notOnly : onlyForeign node maximum = false := by
      cases value : onlyForeign node maximum <;> simp_all
    have nonzero : GeneralBorrowWildcardRelatednessBounds.count location.exposedCache root kind ≠ 0 := by
      intro zero
      exact foreign (.inr zero)
    exact ⟨materialized location root node,
      either_access tree location root node maximum kind protections present leaf nonzero notOnly⟩

end DuplicatePrefix.GeneralBorrowWildcardVirtualLeaf
