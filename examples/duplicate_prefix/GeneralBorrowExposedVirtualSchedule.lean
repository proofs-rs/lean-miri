import duplicate_prefix.GeneralBorrowExposureCardinality
import duplicate_prefix.GeneralBorrowWildcardVirtualLeafFold
import duplicate_prefix.GeneralBorrowFreshLocation
import duplicate_prefix.GeneralBorrowVirtualRootsAdapter

namespace DuplicatePrefix.GeneralBorrowExposedVirtualSchedule
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowWildcardVirtualLeaf (effective materialized)
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- Materializing a lazy row changes no present node's semantic state. -/
theorem materialized_effective (tree : BorrowTree) (location : LocationTree)
    (root : UniIndex) (node : TreeNode) (present : tree.nodes.get root = some node)
    (query : UniIndex) (queryNode : TreeNode) (queryPresent : tree.nodes.get query = some queryNode) :
    effective (materialized location root node) query queryNode = effective location query queryNode := by
  by_cases same : query = root
  · subst query
    have eqNode := Option.some.inj (present.symm.trans queryPresent)
    subst queryNode
    cases stored : location.perms.get root
    · simp only [materialized,UniValMap.orInsert,stored,effective,Option.getD_none]
      rw [GeneralBorrowFreshLocation.get_same]
      rfl
    · simp [materialized,UniValMap.orInsert,stored,effective]
  · unfold materialized UniValMap.orInsert
    split
    · rfl
    · simp only [effective]
      rw [GeneralBorrowFreshLocation.get_other _ root query node.defaultLocationState same]

/-- Initial coherent finite-width exposure counts derive the real Either
classification; an exposed supporting leaf's actual virtual call completes
and retains every effective state, even with protected or non-ForeignOwned rows. -/
theorem step (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (node : TreeNode) (maximum : Option BorTag) (kind : AccessKind)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (short : tree.nodes.size < 65536) (present : tree.nodes.get root = some node)
    (leaf : node.children = #[]) (exposed : node.isExposed = true)
    (support : GeneralBorrowExposureCardinality.supports
      (GeneralBorrowExposureCardinality.effective location protections root node) kind = true)
    (cutoff : GeneralBorrowWildcardVirtualLeaf.onlyForeign node maximum = false) :
    location.exposedCache.accessRelatedness root root kind true false = some .EitherAccess ∧
    tree.performWildcardAccessAt location root maximum kind protections true =
      ⟨materialized location root node,.Completed⟩ ∧
    (∀ query queryNode, tree.nodes.get query = some queryNode →
      effective (materialized location root node) query queryNode = effective location query queryNode) := by
  have positive := GeneralBorrowExposureCardinality.exposed_self location.exposedCache tree.nodes
    (GeneralBorrowExposureCardinality.effective location protections) coherent short root node present exposed kind support
  have nonzero : GeneralBorrowWildcardRelatednessBounds.count location.exposedCache root kind ≠ 0 := by
    cases kind <;> simpa only [GeneralBorrowWildcardRelatednessBounds.count,
      GeneralBorrowExposureCardinality.counter] using Nat.ne_of_gt positive
  refine ⟨?_,GeneralBorrowWildcardVirtualLeaf.either_access tree location root node maximum kind protections present leaf nonzero cutoff,?_⟩
  · rw [GeneralBorrowWildcardRelatednessBounds.root_classify]
    simp [nonzero]
  · exact fun query queryNode queryPresent => materialized_effective tree location root node present query queryNode queryPresent

/-- A finite source-order schedule of exposed supporting leaves completes.
Repeated roots are allowed. Exact initial counters and all permissions survive,
so every ownership predicate on effective rows is retained. No call-success,
zero-cache, unexposed-node, or permission-transition premise is supplied. -/
theorem schedule (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (roots : List UniIndex) (nodes : UniIndex → TreeNode) (maximum : Option BorTag) (kind : AccessKind)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (short : tree.nodes.size < 65536)
    (data : ∀ root ∈ roots, tree.nodes.get root = some (nodes root) ∧
      (nodes root).children = #[] ∧ (nodes root).isExposed = true ∧
      GeneralBorrowExposureCardinality.supports
        (GeneralBorrowExposureCardinality.effective initial protections root (nodes root)) kind = true ∧
      GeneralBorrowWildcardVirtualLeaf.onlyForeign (nodes root) maximum = false) :
    ∃ after, GeneralBorrowWildcardVirtualLeafFold.run tree roots initial maximum kind protections = ⟨after,.Completed⟩ ∧
      after.exposedCache = initial.exposedCache ∧
      (∀ query node, tree.nodes.get query = some node → effective after query node = effective initial query node) := by
  have runFrom : ∀ schedule : List UniIndex, (∀ root ∈ schedule, root ∈ roots) →
      ∀ current : LocationTree, current.exposedCache = initial.exposedCache →
      (∀ query node, tree.nodes.get query = some node → effective current query node = effective initial query node) →
      ∃ after, GeneralBorrowWildcardVirtualLeafFold.run tree schedule current maximum kind protections = ⟨after,.Completed⟩ ∧
        after.exposedCache = initial.exposedCache ∧
        (∀ query node, tree.nodes.get query = some node → effective after query node = effective initial query node) := by
    intro schedule
    induction schedule with
    | nil => intro subset current cache frame; exact ⟨current,rfl,cache,frame⟩
    | cons root rest ih =>
      intro subset current cache frame
      obtain ⟨present,leaf,exposed,support,cutoff⟩ := data root (subset root (by simp))
      have positive := GeneralBorrowExposureCardinality.exposed_self initial.exposedCache tree.nodes
        (GeneralBorrowExposureCardinality.effective initial protections) coherent short root (nodes root) present exposed kind support
      have nonzero : GeneralBorrowWildcardRelatednessBounds.count current.exposedCache root kind ≠ 0 := by
        rw [cache]
        cases kind <;> simpa only [GeneralBorrowWildcardRelatednessBounds.count,
          GeneralBorrowExposureCardinality.counter] using Nat.ne_of_gt positive
      have first := GeneralBorrowWildcardVirtualLeaf.either_access tree current root (nodes root) maximum kind protections present leaf nonzero cutoff
      have nextFrame : ∀ query node, tree.nodes.get query = some node →
          effective (materialized current root (nodes root)) query node = effective initial query node := by
        intro query node member
        exact (materialized_effective tree current root (nodes root) present query node member).trans (frame query node member)
      obtain ⟨after,tail,afterCache,afterFrame⟩ := ih (fun query member => subset query (by simp [member]))
        (materialized current root (nodes root)) cache nextFrame
      refine ⟨after,?_,afterCache,afterFrame⟩
      simpa only [GeneralBorrowWildcardVirtualLeafFold.run,first,beq_self_eq_true,ite_true] using tail
  exact runFrom roots (fun _ member => member) initial rfl (fun _ _ _ => rfl)

/-- Semantic row equality retains the exact exposure-cardinality invariant,
including counters for nodes outside the visited schedule. -/
theorem coherent_frame (tree : BorrowTree) (before after : LocationTree) (protections : ProtectedTags)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree before protections)
    (cache : after.exposedCache = before.exposedCache)
    (frame : ∀ index node, tree.nodes.get index = some node → effective after index node = effective before index node) :
    GeneralBorrowExposureCardinality.LocationCoherent tree after protections := by
  intro query kind
  rw [cache,coherent query kind]
  unfold GeneralBorrowExposureCardinality.cardinality
  apply congrArg UInt16.ofNat
  apply congrArg List.length
  apply List.filter_congr
  intro row member
  have present := (GeneralBorrowFreshReuseProtection.entries_get tree.nodes row.1 row.2).mp member
  have same := frame row.1 row.2 present
  simp only [GeneralBorrowExposureCardinality.contributes,GeneralBorrowExposureCardinality.effective,
    effective] at same ⊢
  rw [same]

/-- The actual indexed extra-root callback has the same successful result,
retains coherent counters, and preserves any effective-row ownership predicate.
Roots may repeat; the source's primary-root exclusion and cutoff remain explicit. -/
theorem indexed (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (roots : List UniIndex) (nodes : UniIndex → TreeNode) (primary : UniIndex)
    (maximum : BorTag) (range : Miri.DataStructures.ByteRange) (kind : AccessKind)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (short : tree.nodes.size < 65536)
    (data : ∀ root ∈ roots, tree.nodes.get root = some (nodes root) ∧
      (nodes root).children = #[] ∧ (nodes root).isExposed = true ∧
      GeneralBorrowExposureCardinality.supports
        (GeneralBorrowExposureCardinality.effective initial protections root (nodes root)) kind = true ∧
      GeneralBorrowWildcardVirtualLeaf.onlyForeign (nodes root) (some maximum) = false)
    (different : ∀ root ∈ roots, root ≠ primary)
    (property : UniIndex → TreeNode → LocationState → Prop)
    (owned : ∀ index node, tree.nodes.get index = some node → property index node (effective initial index node)) :
    ∃ after,
      forIn (List.range' 1 roots.length) (initial,none,false)
        (GeneralBorrowVirtualRootsAdapter.scanAt tree primary roots maximum kind protections range) = (after,none,false) ∧
      GeneralBorrowExposureCardinality.LocationCoherent tree after protections ∧
      after.exposedCache = initial.exposedCache ∧
      (∀ index node, tree.nodes.get index = some node → property index node (effective after index node)) := by
  obtain ⟨after,completed,cache,frame⟩ := schedule tree initial protections roots nodes (some maximum) kind coherent short data
  refine ⟨after,?_,coherent_frame tree initial after protections coherent cache frame,cache,?_⟩
  · rw [GeneralBorrowVirtualRootsAdapter.indexed]
    exact GeneralBorrowVirtualRootsAdapter.successful tree primary maximum kind protections range roots different initial after completed
  · intro index node present
    rw [frame index node present]
    exact owned index node present
end DuplicatePrefix.GeneralBorrowExposedVirtualSchedule
