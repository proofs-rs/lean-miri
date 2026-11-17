import duplicate_prefix.GeneralBorrowExposedKnownRootWritePrimaryPath
import duplicate_prefix.GeneralBorrowExposedKnownRootWriteInvariant
namespace DuplicatePrefix.GeneralBorrowExposedKnownRootWritePrimaryWitness
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowWildcardSubtreeStack
open GeneralBorrowExposedNonleafPrimaryPath
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]

set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

structure Data (tree : BorrowTree) (initial : LocationTree) (root : UniIndex) (protections : ProtectedTags) where
  base : GeneralBorrowExposedKnownRootWriteState.Data tree initial root protections
  graph : Reciprocal tree
  witness : UniIndex
  node : TreeNode
  present : tree.nodes.get witness = some node
  exposed : node.isExposed = true
  support : GeneralBorrowExposureCardinality.supports (GeneralBorrowExposureCardinality.effective initial protections witness node) .Write = true
  path : Path tree root witness

def Pending (tree : BorrowTree) (witness : UniIndex) (seen : Bool) (stack : Array Task) : Prop :=
  seen = true ∨ ∃ task ∈ stack.toList, Path tree task.1 witness ∧ (task.2 = true → task.1 = witness)

theorem initial {tree initial root protections} (data : Data tree initial root protections) :
    Pending tree data.witness false #[(root,false)] :=
  .inr ⟨(root,false),by simp,data.path,by simp⟩

theorem empty {tree witness seen} (pending : Pending tree witness seen #[]) : seen = true := by
  rcases pending with done | ⟨task,member,_,_⟩
  · exact done
  · simp at member

theorem pop {tree initial root protections} (data : Data tree initial root protections)
    (seen : Bool) (stack : Array Task) (index : UniIndex) (after : Bool)
    (pending : Pending tree data.witness seen (stack.push (index,after)))
    (zero : GeneralBorrowWildcardRelatednessBounds.count initial.exposedCache index .Write = 0) :
    Pending tree data.witness seen stack := by
  rcases pending with done | ⟨task,member,path,post⟩
  · exact .inl done
  · simp only [Array.toList_push,List.mem_append,List.mem_singleton] at member
    rcases member with member | same
    · exact .inr ⟨task,member,path,post⟩
    · subst task
      have positive := GeneralBorrowExposedKnownRootWritePrimaryPath.positive data.base data.witness data.node data.present data.exposed data.support index path
      rw [zero] at positive
      omega

theorem expand {tree initial root protections} (data : Data tree initial root protections)
    (seen : Bool) (stack : Array Task) (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node)
    (pending : Pending tree data.witness seen (stack.push (index,false))) :
    Pending tree data.witness seen (expanded stack index node.children) := by
  rcases pending with done | ⟨task,member,path,post⟩
  · exact .inl done
  · simp only [Array.toList_push,List.mem_append,List.mem_singleton] at member
    rcases member with member | same
    · refine .inr ⟨task,?_,path,post⟩
      simp [expanded,member]
    · subst task
      by_cases same : index = data.witness
      · refine .inr ⟨(index,true),?_,path,by intro _;exact same⟩
        simp [expanded]
      · obtain ⟨oldNode,child,found,member,path⟩ := path.first data.graph same
        have sameNode : oldNode = node := Option.some.inj (found.symm.trans present)
        subst oldNode
        refine .inr ⟨(child,false),?_,path,by simp⟩
        simp only [expanded,Array.toList_append,List.mem_append,Array.toList_map]
        exact .inr (List.mem_map.mpr ⟨child,member,rfl⟩)

theorem post {tree witness} (seen afterSeen : Bool) (stack : Array Task) (index : UniIndex)
    (pending : Pending tree witness seen (stack.push (index,true)))
    (monotone : seen = true → afterSeen = true) (found : index = witness → afterSeen = true) :
    Pending tree witness afterSeen stack := by
  rcases pending with done | ⟨task,member,path,post⟩
  · exact .inl (monotone done)
  · simp only [Array.toList_push,List.mem_append,List.mem_singleton] at member
    rcases member with member | same
    · exact .inr ⟨task,member,path,post⟩
    · subst task
      exact .inl (found (post rfl))
theorem path_supported {tree initial root protections} (data : Data tree initial root protections)
    {index : UniIndex} (path : Path tree root index) : data.base.support index := by
  induction path with
  | refl => exact data.base.rooted
  | @step parent child earlier node present edge ih =>
    obtain ⟨parentNode,found,member⟩ := data.graph child node present parent edge
    exact data.base.children parent parentNode ih found child member

theorem witness_allows {tree initial root protections} (data : Data tree initial root protections)
    (current : LocationTree) (frame : GeneralBorrowExposedKnownRootWriteState.WriteFrame initial current)
    (profile : GeneralBorrowExposedKnownRootWriteState.Profile tree current protections)
    (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node) (same : index = data.witness) :
    ((GeneralBorrowWildcardVirtualLeaf.effective current index node).permission.strongestAllowedLocalAccess (protections.contains node.tag)).allows .Write = true := by
  have positive := GeneralBorrowExposureCardinality.exposed_self initial.exposedCache tree.nodes
    (GeneralBorrowExposureCardinality.effective initial protections) data.base.coherent data.base.short data.witness data.node data.present data.exposed .Write data.support
  have nonzero : GeneralBorrowWildcardRelatednessBounds.count initial.exposedCache index .Write ≠ 0 := by
    subst index
    exact Nat.ne_of_gt positive
  exact GeneralBorrowExposedConditionalWritePermissions.local_allows _ _
    (GeneralBorrowExposedKnownRootWriteState.local_compatible tree initial current protections frame profile index node present (by subst index;exact data.base.included data.witness (path_supported data data.path)) nonzero)
end DuplicatePrefix.GeneralBorrowExposedKnownRootWritePrimaryWitness
