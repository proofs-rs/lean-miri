import duplicate_prefix.GeneralBorrowExposeRead
namespace DuplicatePrefix.GeneralBorrowExposeReadFold
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposeRead DuplicatePrefix.RangeMapNonempty
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

structure Request where
  tag : BorTag
  leaf : UniIndex
  node : TreeNode

/-- Initial raw facts about a previously generated Frozen leaf. These premises
say nothing about the outcome of exposeTag or its later repetitions. -/
structure Ready (tree : BorrowTree) (location : LocationTree) (root : UniIndex)
    (rootNode : TreeNode) (request : Request) : Prop where
  tagged : tree.indexOfTag request.tag = some request.leaf
  present : tree.nodeAt request.leaf = some request.node
  rootPresent : tree.nodeAt root = some rootNode
  different : root ≠ request.leaf
  parent : request.node.parent = some root
  parentless : rootNode.parent = none
  unexposed : request.node.isExposed = false
  frozen : ∃ state, location.perms.get request.leaf = some state ∧ state.permission = .Frozen

def nextLocation (location : LocationTree) (root : UniIndex) (request : Request) : LocationTree :=
  {location with exposedCache := bumpRead (bumpRead location.exposedCache request.leaf) root}
def nextTree (tree : BorrowTree) (location : LocationTree) (capacity : UInt64) (root : UniIndex) (request : Request) : BorrowTree :=
  {(marked tree request.leaf request.node) with locations := homogeneous capacity (nextLocation location root request)}

def run (protections : ProtectedTags) : List Request → BorrowTree → BorrowTree.TreeMutationResult
  | [],tree => ⟨tree,.ok ()⟩
  | request::rest,tree =>
      let result := tree.exposeTag protections request.tag
      match result.outcome with
      | .error error => result
      | .ok () => run protections rest result.tree

def pureRun (capacity : UInt64) (root : UniIndex) : List Request → BorrowTree → LocationTree → BorrowTree × LocationTree
  | [],tree,location => (tree,location)
  | request::rest,tree,location =>
      pureRun capacity root rest (nextTree tree location capacity root request) (nextLocation location root request)

/-- Any number of distinct, initially unexposed Frozen leaves can be exposed by
an actual successful sequence. The result is the exact finite-width counter
fold, with no native evaluation and no operation-success premises. Generation
and Rust validity of the initial leaves remain separate obligations. -/
theorem run_eq (requests : List Request) (tree : BorrowTree) (location : LocationTree)
    (capacity : UInt64) (root : UniIndex) (rootNode : TreeNode) (protections : ProtectedTags)
    (locations : tree.locations = homogeneous capacity location)
    (ready : ∀ request ∈ requests, Ready tree location root rootNode request)
    (distinct : (requests.map Request.leaf).Nodup) :
    run protections requests tree = ⟨(pureRun capacity root requests tree location).1,.ok ()⟩ := by
  induction requests generalizing tree location with
  | nil => rfl
  | cons request rest ih =>
    have first := ready request (by simp)
    have actual := GeneralBorrowExposeRead.expose tree request.tag request.leaf root request.node rootNode location capacity protections
      first.tagged first.present first.rootPresent first.different first.parent first.parentless first.unexposed first.frozen locations
    have restDistinct : (rest.map Request.leaf).Nodup := (List.nodup_cons.mp distinct).2
    have later : ∀ other ∈ rest, Ready (nextTree tree location capacity root request)
        (nextLocation location root request) root rootNode other := by
      intro other member
      have old := ready other (by simp [member])
      have different : other.leaf ≠ request.leaf := by
        intro same
        exact (List.nodup_cons.mp distinct).1 (List.mem_map.mpr ⟨other,member,same⟩)
      exact {
        tagged := old.tagged
        present := (DuplicatePrefix.GeneralBorrowFreshLocation.get_other tree.nodes request.leaf other.leaf _ different).trans old.present
        rootPresent := (DuplicatePrefix.GeneralBorrowFreshLocation.get_other tree.nodes request.leaf root _ first.different).trans old.rootPresent
        different := old.different
        parent := old.parent
        parentless := old.parentless
        unexposed := old.unexposed
        frozen := old.frozen
      }
    change (match (tree.exposeTag protections request.tag).outcome with
      | .error error => tree.exposeTag protections request.tag
      | .ok () => run protections rest (tree.exposeTag protections request.tag).tree) = _
    rw [actual]
    exact ih _ _ rfl later restDistinct

/-- Exposure changes cache/flags only; all actual permission entries, including
those of an already-created wildcard root/reference, remain exactly unchanged. -/
theorem pure_permissions (requests : List Request) (tree : BorrowTree) (location : LocationTree)
    (capacity : UInt64) (root : UniIndex) :
    (pureRun capacity root requests tree location).2.perms = location.perms := by
  induction requests generalizing tree location with
  | nil => rfl
  | cons request rest ih => exact ih _ _
end DuplicatePrefix.GeneralBorrowExposeReadFold
