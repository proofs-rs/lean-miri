import duplicate_prefix.WildcardHitZeroConstructor

namespace DuplicatePrefix.WildcardHitRootDepth
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshNode DuplicatePrefix.GeneralBorrowNodeUpdate
open DuplicatePrefix.GeneralBorrowExposure
set_option maxRecDepth 65536
set_option maxHeartbeats 100000

def append_root (nodes : UniValMap TreeNode) (before : ParentDepth nodes)
    (index : UniIndex) (newNode : TreeNode)
    (atEnd : index.toNat = nodes.data.size) (parentless : newNode.parent = none) :
    ParentDepth (nodes.insert index newNode) where
  depth := fun query => if query = index then 0 else before.depth query
  bounded := by
    intro query node lookup
    rw [append_size nodes index newNode atEnd]
    by_cases same : query = index
    · simp only [same,ite_true];omega
    · simp only [same,ite_false]
      rw [append_get_other nodes index query newNode atEnd same] at lookup
      have bound := before.bounded query node lookup
      omega
  parent := by
    intro query node lookup earlier edge
    by_cases same : query = index
    · subst query
      rw [append_get_same nodes index newNode atEnd] at lookup
      cases lookup
      rw [parentless] at edge
      contradiction
    · rw [append_get_other nodes index query newNode atEnd same] at lookup
      obtain ⟨ancestor,present,smaller⟩ := before.parent query node lookup earlier edge
      have earlierNotNew : earlier ≠ index := by
        intro equal
        have bound := lookup_valid nodes earlier ancestor present
        rw [equal,atEnd] at bound
        omega
      refine ⟨ancestor,(append_get_other nodes index earlier newNode atEnd earlierNotNew).trans present,?_⟩
      simpa only [earlierNotNew,same,ite_false] using smaller

/-- The actual zero HIT root insertion retains finite parent-depth evidence
for the old forest. Its new parentless root has rank zero. -/
def installed (tree : BorrowTree) (before : ParentDepth tree.nodes)
    (mapping : UniKeyMap BorTag) (index : UniIndex) (tag : BorTag)
    (outside : Permission) (sifa : IdempotentForeignAccess)
    (atEnd : index.toNat = tree.nodes.data.size) :
    ParentDepth (WildcardHitZeroConstructor.installed tree mapping index tag outside sifa).nodes :=
  append_root tree.nodes before index (WildcardHitZeroConstructor.rootNode tag outside sifa) atEnd rfl

end DuplicatePrefix.WildcardHitRootDepth
