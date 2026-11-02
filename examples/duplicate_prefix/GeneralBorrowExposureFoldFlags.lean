import duplicate_prefix.GeneralBorrowExposedLeavesRoot
import duplicate_prefix.GeneralBorrowGeneratedStarShape
namespace DuplicatePrefix.GeneralBorrowExposureFoldFlags
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposeRead DuplicatePrefix.GeneralBorrowExposeReadFold
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Exact exposure flags of the source-exact pure fold, including sparse vacancies. -/
theorem flags (requests : List Request) (tree : BorrowTree) (location : LocationTree)
    (capacity : UInt64) (root query : UniIndex) :
    ((pureRun capacity root requests tree location).1.nodeAt query).map TreeNode.isExposed =
      if query ∈ requests.map Request.leaf then some true else (tree.nodeAt query).map TreeNode.isExposed := by
  induction requests generalizing tree location with
  | nil => simp only [pureRun,List.map_nil,List.not_mem_nil,ite_false]
  | cons request rest ih =>
    rw [show pureRun capacity root (request::rest) tree location =
      pureRun capacity root rest (nextTree tree location capacity root request) (nextLocation location root request) from rfl,ih]
    by_cases later : query ∈ rest.map Request.leaf
    · simp only [later,ite_true,List.map_cons,List.mem_cons,or_true]
    · simp only [later,ite_false,List.map_cons,List.mem_cons,or_false]
      by_cases same : query = request.leaf
      · subst query
        simp only [ite_true,nextTree,marked,BorrowTree.nodeAt,GeneralBorrowFreshLocation.get_same,Option.map_some]
      · simp only [same,ite_false,nextTree,marked,BorrowTree.nodeAt,
          GeneralBorrowFreshLocation.get_other _ _ _ _ same]

/-- A pure leaf exposure never removes a present node, whether it is the root,
the newly marked node or an arbitrary old sibling. -/
theorem present (requests : List Request) (tree : BorrowTree) (location : LocationTree)
    (capacity : UInt64) (root query : UniIndex) (node : TreeNode) (found : tree.nodeAt query = some node) :
    ∃ after, (pureRun capacity root requests tree location).1.nodeAt query = some after := by
  induction requests generalizing tree location node with
  | nil => exact ⟨node,found⟩
  | cons request rest ih =>
    by_cases same : query = request.leaf
    · subst query
      exact ih _ _ _ (GeneralBorrowFreshLocation.get_same tree.nodes request.leaf _)
    · exact ih _ _ node ((GeneralBorrowFreshLocation.get_other tree.nodes request.leaf query _ same).trans found)

/-- Marking only previously present leaves also cannot create a new node. -/
theorem old_present (requests : List Request) (tree : BorrowTree) (location : LocationTree)
    (capacity : UInt64) (root query : UniIndex)
    (initial : ∀ request ∈ requests,∃ node,tree.nodeAt request.leaf = some node)
    (node : TreeNode) (found : (pureRun capacity root requests tree location).1.nodeAt query = some node) :
    ∃ before,tree.nodeAt query = some before := by
  induction requests generalizing tree location with
  | nil => exact ⟨node,found⟩
  | cons request rest ih =>
    have later : ∀ other ∈ rest,∃ node,(nextTree tree location capacity root request).nodeAt other.leaf = some node := by
      intro other member
      obtain ⟨old,oldFound⟩ := initial other (by simp [member])
      by_cases same : other.leaf = request.leaf
      · rw [same];exact ⟨_,GeneralBorrowFreshLocation.get_same tree.nodes request.leaf _⟩
      · exact ⟨old,(GeneralBorrowFreshLocation.get_other tree.nodes request.leaf other.leaf _ same).trans oldFound⟩
    obtain ⟨before,beforeFound⟩ := ih _ _ later found
    by_cases same : query = request.leaf
    · subst query;exact initial request (by simp)
    · exact ⟨before,(GeneralBorrowFreshLocation.get_other tree.nodes request.leaf query _ same).symm.trans beforeFound⟩
/-- Exact permissions remain a full generator profile after all leaf exposures. -/
theorem profile (requests : List Request) (tree : BorrowTree) (location : LocationTree)
    (capacity : UInt64) (root : UniIndex)
    (initial : GeneralBorrowSharedGeneratorProfile.Profile tree location root)
    (known : ∀ request ∈ requests,∃ node,tree.nodeAt request.leaf = some node) :
    GeneralBorrowSharedGeneratorProfile.Profile (pureRun capacity root requests tree location).1
      (pureRun capacity root requests tree location).2 root := by
  have perms := pure_permissions requests tree location capacity root
  refine ⟨by rw [perms];exact initial.rootStored,?_,?_⟩
  · intro query node found different
    obtain ⟨before,beforeFound⟩ := old_present requests tree location capacity root query known node found
    rw [perms]
    exact initial.shared query before beforeFound different
  · intro query absent
    rw [perms]
    apply initial.vacant query
    cases old : tree.nodeAt query with
    | none => exact old
    | some before =>
      obtain ⟨after,afterFound⟩ := present requests tree location capacity root query before old
      rw [show (pureRun capacity root requests tree location).1.nodeAt query = none from absent] at afterFound
      cases afterFound

/-- Exposing all children of the actual star exposes every nonroot present node. -/
theorem all_nonroot (requests : List Request) (tree : BorrowTree) (location : LocationTree)
    (capacity : UInt64) (root : UniIndex) (rootNode : TreeNode)
    (star : GeneralBorrowGeneratedStarShape.Star tree root rootNode)
    (leaves : requests.map Request.leaf = rootNode.children.toList)
    (known : ∀ request ∈ requests,∃ node,tree.nodeAt request.leaf = some node)
    (query : UniIndex) (node : TreeNode)
    (found : (pureRun capacity root requests tree location).1.nodeAt query = some node) (different : query ≠ root) :
    node.isExposed = true := by
  obtain ⟨before,beforeFound⟩ := old_present requests tree location capacity root query known node found
  have member : query ∈ requests.map Request.leaf := by rw [leaves];exact (star.children query).mpr ⟨different,before,beforeFound⟩
  have exactFlags := flags requests tree location capacity root query
  rw [found,ite_eq_left member] at exactFlags
  exact Option.some.inj exactFlags

/-- Root marking preserves the exact per-node generator profile. -/
theorem mark_profile (tree : BorrowTree) (location : LocationTree) (root : UniIndex) (node : TreeNode)
    (initial : GeneralBorrowSharedGeneratorProfile.Profile tree location root) :
    GeneralBorrowSharedGeneratorProfile.Profile (marked tree root node) location root := by
  refine ⟨initial.rootStored,?_,?_⟩
  · intro query value found different
    have old : tree.nodeAt query = some value :=
      (GeneralBorrowFreshLocation.get_other tree.nodes root query _ different).symm.trans found
    exact initial.shared query value old different
  · intro query absent
    by_cases same : query = root
    · subst query
      change (tree.nodes.insert root {node with isExposed := true}).get root = none at absent
      rw [GeneralBorrowFreshLocation.get_same] at absent
      cases absent
    · apply initial.vacant
      exact (GeneralBorrowFreshLocation.get_other tree.nodes root query _ same).symm.trans absent

/-- The final real root-mark step completes the all-present-nodes exposure
invariant, after every generated child has been exposed. -/
theorem mark_all (tree : BorrowTree) (root : UniIndex) (node : TreeNode)
    (nonroot : ∀ query value,tree.nodeAt query = some value → query ≠ root → value.isExposed = true) :
    ∀ query value,(marked tree root node).nodeAt query = some value → value.isExposed = true := by
  intro query value found
  by_cases same : query = root
  · subst query
    have exactNode := GeneralBorrowFreshLocation.get_same tree.nodes root {node with isExposed := true}
    rw [show (marked tree root node).nodeAt root = some {node with isExposed := true} from exactNode] at found
    cases found;rfl
  · exact nonroot query value ((GeneralBorrowFreshLocation.get_other tree.nodes root query _ same).symm.trans found) same

end DuplicatePrefix.GeneralBorrowExposureFoldFlags
