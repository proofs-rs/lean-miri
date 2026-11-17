import duplicate_prefix.GeneralBorrowExposedScopedLeafData
import duplicate_prefix.GeneralBorrowExposedKnownRootWritePrimaryWitness
namespace DuplicatePrefix.GeneralBorrowExposedScopedLeafWriteData
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

theorem unique_support (location : LocationTree) (protections : ProtectedTags) (index : UniIndex) (node : TreeNode)
    (unique : GeneralBorrowWildcardVirtualLeaf.effective location index node=GeneralBorrowWildcardLeaf.unique) :
    GeneralBorrowExposureCardinality.supports (GeneralBorrowExposureCardinality.effective location protections index node) .Write=true := by
  change GeneralBorrowExposureCardinality.supports
    ((GeneralBorrowWildcardVirtualLeaf.effective location index node).permission.strongestAllowedLocalAccess _) .Write=true
  rw[unique]
  cases held : protections.contains node.tag <;> rfl

/-- Exposed exact-Unique leaves have a positive Write self counter, so even a
held Unique row is classified locally and satisfies the raw Write condition. -/
theorem profile (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections) (short : tree.nodes.size<65536)
    (states : ∀index node,area.support index→tree.nodes.get index=some node→node.isExposed=true ∧
      GeneralBorrowWildcardVirtualLeaf.effective location index node=GeneralBorrowWildcardLeaf.unique) :
    GeneralBorrowExposedKnownRootWriteState.Profile tree location protections := by
  intro index node included present
  obtain ⟨exposed,unique⟩:=states index node included present
  have positive:=GeneralBorrowExposureCardinality.exposed_self location.exposedCache tree.nodes
    (GeneralBorrowExposureCardinality.effective location protections) coherent short index node present exposed .Write (unique_support location protections index node unique)
  change 0<GeneralBorrowWildcardRelatednessBounds.count location.exposedCache index .Write at positive
  have nonzero : GeneralBorrowExposedKnownRootWriteState.zero location index=false := by
    simp[GeneralBorrowExposedKnownRootWriteState.zero,Nat.ne_of_gt positive]
  rw[GeneralBorrowExposedConditionalWritePermissions.Condition,nonzero,unique]
  simp[GeneralBorrowExposedConditionalWritePermissions.Compatible,GeneralBorrowWildcardLeaf.unique,LocationState.possible,Permission.isUnique]

def virtual (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) (root : UniIndex) (node : TreeNode)
    (present : tree.nodes.get root=some node) (leaf : node.children=#[]) (included : area.support root)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections) (short : tree.nodes.size<65536)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (profile : GeneralBorrowExposedKnownRootWriteState.Profile tree location protections) :
    GeneralBorrowExposedKnownRootWriteState.Data tree location root protections where
  support := fun index=>index=root
  rooted := rfl
  present := by intro index same;subst index;exact ⟨node,present⟩
  children := by
    intro index queried same found child member
    subst index
    have equal:=Option.some.inj (present.symm.trans found)
    subst queried
    rw[leaf] at member
    cases member
  covers := by intro index same;subst index;intro row member ancestor;exact ancestor
  coherent := coherent
  short := short
  depth := depth
  included := by intro index same;subst index;exact included
  profile := profile

def primary (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) (root : UniIndex) (node : TreeNode)
    (present : tree.nodes.get root=some node) (leaf : node.children=#[]) (included : area.support root)
    (exposed : node.isExposed=true) (unique : GeneralBorrowWildcardVirtualLeaf.effective location root node=GeneralBorrowWildcardLeaf.unique)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections) (short : tree.nodes.size<65536)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (profile : GeneralBorrowExposedKnownRootWriteState.Profile tree location protections)
    (graph : GeneralBorrowExposedNonleafPrimaryPath.Reciprocal tree) :
    GeneralBorrowExposedKnownRootWritePrimaryWitness.Data tree location root protections where
  base := virtual tree location protections root node present leaf included coherent short depth profile
  graph := graph
  witness := root
  node := node
  present := present
  exposed := exposed
  support := unique_support location protections root node unique
  path := .refl root node present
end DuplicatePrefix.GeneralBorrowExposedScopedLeafWriteData
