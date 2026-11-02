import duplicate_prefix.GeneralBorrowWildcardVirtualLeafFrame

namespace DuplicatePrefix.GeneralBorrowWildcardVirtualLeafFold
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowWildcardVirtualLeaf (effective)
open GeneralBorrowWildcardVirtualLeafFrame (Frame)
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Finite source-order adapter: every scheduled component is the actual
wildcard visitor with the virtual-root flag. Errors stop the remaining calls.
Joining this adapter to the interpreter's root-position loop is separate. -/
def run (tree : BorrowTree) (roots : List UniIndex) (location : LocationTree)
    (maximum : Option BorTag) (kind : AccessKind) (protections : ProtectedTags) :
    BorrowTree.WildcardLocationAccessResult :=
  match roots with
  | [] => ⟨location,.Completed⟩
  | root :: rest =>
    let first := tree.performWildcardAccessAt location root maximum kind protections true
    if first.status == .Completed then run tree rest first.location maximum kind protections
    else first

/-- Topology data is independent of the per-location permission/cache rows. -/
def Leaves (tree : BorrowTree) (nodes : UniIndex → TreeNode) (roots : List UniIndex) : Prop :=
  ∀ root, root ∈ roots → tree.nodes.get root = some (nodes root) ∧
    (nodes root).children = #[] ∧ (nodes root).parent = none

def Owned (nodes : UniIndex → TreeNode) (roots : List UniIndex)
    (protections : ProtectedTags) (location : LocationTree) : Prop :=
  ∀ root, root ∈ roots → GeneralBorrowPermissions.ForeignOwned
    (effective location root (nodes root)) (protections.contains (nodes root).tag)

/-- Pointwise frame transport preserves the effective lazy/default state of
an unvisited root, regardless of whether its permission row is materialized. -/
theorem owned_step (nodes : UniIndex → TreeNode) (roots : List UniIndex)
    (protections : ProtectedTags) (before after : LocationTree) (root : UniIndex)
    (owned : Owned nodes roots protections before)
    (current : GeneralBorrowPermissions.ForeignOwned (effective after root (nodes root))
      (protections.contains (nodes root).tag)) (frame : Frame root before after) :
    Owned nodes roots protections after := by
  intro query member
  by_cases same : query = root
  · subst query
    exact current
  · have lookup := (frame query same).1
    simpa only [effective,lookup] using owned query member

private theorem complete_aux (tree : BorrowTree) (nodes : UniIndex → TreeNode)
    (allRoots schedule : List UniIndex) (maximum : Option BorTag) (kind : AccessKind)
    (protections : ProtectedTags) (parents : GeneralBorrowExposure.ParentDepth tree.nodes)
    (leaves : Leaves tree nodes allRoots) (subset : ∀ root, root ∈ schedule → root ∈ allRoots)
    (location : LocationTree) (owned : Owned nodes allRoots protections location) :
    ∃ after, run tree schedule location maximum kind protections = ⟨after,.Completed⟩ ∧
      Owned nodes allRoots protections after ∧
      (∀ query, query ∉ schedule → after.perms.get query = location.perms.get query ∧
        after.exposedCache.nodes.get query = location.exposedCache.nodes.get query) := by
  induction schedule generalizing location with
  | nil => exact ⟨location,rfl,owned,fun _ _ => ⟨rfl,rfl⟩⟩
  | cons root rest ih =>
    have member : root ∈ allRoots := subset root (by simp)
    obtain ⟨present,leaf,parentless⟩ := leaves root member
    obtain ⟨middle,first,current,frame⟩ := GeneralBorrowWildcardVirtualLeafFrame.access
      tree location root (nodes root) maximum kind protections present leaf parents parentless (owned root member)
    have middleOwned := owned_step nodes allRoots protections location middle root owned current frame
    have restSubset : ∀ query, query ∈ rest → query ∈ allRoots := by
      intro query inside
      exact subset query (by simp [inside])
    obtain ⟨after,tail,afterOwned,afterFrame⟩ := ih restSubset middle middleOwned
    refine ⟨after,?_,afterOwned,?_⟩
    · simp only [run,first]
      exact tail
    · intro query absent
      have different : query ≠ root := by intro same; subst query; simp at absent
      have outside : query ∉ rest := by intro inside; exact absent (by simp [inside])
      obtain ⟨perms,cache⟩ := afterFrame query outside
      obtain ⟨perms0,cache0⟩ := frame query different
      exact ⟨perms.trans perms0,cache.trans cache0⟩

/-- Any finite collection of virtual leaf roots completes through actual
visitor calls. Effective foreign ownership persists at every scheduled root;
all normal-component rows outside that collection remain exactly unchanged.
Distinctness and counter bounds are unnecessary for this component theorem. -/
theorem complete (tree : BorrowTree) (nodes : UniIndex → TreeNode) (roots : List UniIndex)
    (location : LocationTree) (maximum : Option BorTag) (kind : AccessKind) (protections : ProtectedTags)
    (parents : GeneralBorrowExposure.ParentDepth tree.nodes) (leaves : Leaves tree nodes roots)
    (owned : Owned nodes roots protections location) :
    ∃ after, run tree roots location maximum kind protections = ⟨after,.Completed⟩ ∧
      Owned nodes roots protections after ∧
      (∀ query, query ∉ roots → after.perms.get query = location.perms.get query ∧
        after.exposedCache.nodes.get query = location.exposedCache.nodes.get query) :=
  complete_aux tree nodes roots roots maximum kind protections parents leaves (fun _ member => member) location owned

end DuplicatePrefix.GeneralBorrowWildcardVirtualLeafFold
