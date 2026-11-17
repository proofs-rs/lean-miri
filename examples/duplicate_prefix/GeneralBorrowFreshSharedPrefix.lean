import duplicate_prefix.GeneralBorrowFreshMixedConstructor
import duplicate_prefix.GeneralBorrowFreshLifetimeRestore
namespace DuplicatePrefix.GeneralBorrowFreshSharedPrefix
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowFreshMixedChild
set_option maxRecDepth 65536
set_option maxHeartbeats 300000

private theorem tag_unheld (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (index : UniIndex) (node : TreeNode) (present : tree.nodeAt index = some node)
    (unheld : protections.contains node.tag = false) :
    (source_normal_projection tree location protections).protectedNodes.contains index.toNat = false := by
  cases held : (source_normal_projection tree location protections).protectedNodes.contains index.toNat with
  | false => rfl
  | true =>
    have member := List.contains_iff_mem.mp held
    obtain ⟨found,lookup,heldProof⟩ := (GeneralBorrowFreshReuseProtection.protected_iff tree location protections index).mp member
    rw [present] at lookup
    cases lookup
    rw [unheld] at heldProof
    cases heldProof

/-- The two shared nodes have Read labels; all older nodes retain their real
Write labels. This is the metadata shape of mutable→shared-expr→shared-FnEntry. -/
def labels (expr child : UniIndex) : Nat → Bool := extend (extend (fun _ => true) expr.toNat) child.toNat

/-- Prefix paths and the real endCall fold discharge every RestoreTo condition
for the older mutable anchor. Neither a successful release nor restored Write
ownership is an input. The expression's shared tag was never protected. -/
theorem restore_data (tree : BorrowTree) (global : GlobalState) (frame : FrameState)
    (target expr child : UniIndex) (targetNode exprNode childNode : TreeNode)
    (targetPresent : tree.nodeAt target = some targetNode)
    (exprPresent : tree.nodeAt expr = some exprNode) (childPresent : tree.nodeAt child = some childNode)
    (allocation : AllocId) (childRegistered : (allocation,childNode.tag) ∈ frame.protectedTags.toList)
    (exprUnheld : global.protectedTags.contains exprNode.tag = false)
    (paths : ∀ location : LocationTree,
      (source_normal_projection tree location global.protectedTags).topology.ancestorPath child.toNat =
        child.toNat :: expr.toNat :: (source_normal_projection tree location global.protectedTags).topology.ancestorPath target.toNat)
    (exprOutside : ∀ location : LocationTree,
      expr.toNat ∉ (source_normal_projection tree location global.protectedTags).topology.ancestorPath target.toNat)
    (childOutside : ∀ location : LocationTree,
      child.toNat ∉ (source_normal_projection tree location global.protectedTags).topology.ancestorPath target.toNat) :
    GeneralBorrowFreshLifetimeRestore.RestoreTo tree global.protectedTags (global.endCall frame).protectedTags
      child target (labels expr child) := by
  have exprAfter : (global.endCall frame).protectedTags.contains exprNode.tag = false := by
    have absent := GeneralBorrowRelease.remove_fold_absent frame.protectedTags.toList global.protectedTags exprNode.tag exprUnheld
    simpa only [GlobalState.endCall,Array.foldl_toList] using absent
  have childAfter := GeneralBorrowRelease.end_call_owned_absent global frame allocation childNode.tag childRegistered
  refine ⟨GeneralBorrowNodeUpdate.lookup_valid tree.nodes target targetNode targetPresent,?_,?_⟩
  · intro location position localTarget
    have member : position ∈ (source_normal_projection tree location global.protectedTags).topology.ancestorPath target.toNat := by
      unfold GeneralBorrowAnchor.relation at localTarget
      split at localTarget
      next member => exact member
      next => contradiction
    have differentExpr : position ≠ expr.toNat := by intro same;subst position;exact exprOutside location member
    have differentChild : position ≠ child.toNat := by intro same;subst position;exact childOutside location member
    refine ⟨?_,?_⟩
    · unfold GeneralBorrowAnchor.relation
      rw [paths location]
      simp only [List.mem_cons,member,or_true,↓reduceIte]
    · simp only [labels,extend,differentExpr,differentChild,↓reduceIte]
  · intro location position localChild foreignTarget
    have member : position ∈ (source_normal_projection tree location global.protectedTags).topology.ancestorPath child.toNat := by
      unfold GeneralBorrowAnchor.relation at localChild
      split at localChild
      next member => exact member
      next => contradiction
    have outside : position ∉ (source_normal_projection tree location global.protectedTags).topology.ancestorPath target.toNat := by
      intro member
      unfold GeneralBorrowAnchor.relation at foreignTarget
      simp only [member,↓reduceIte] at foreignTarget
      cases foreignTarget
    rw [paths location] at member
    rcases List.mem_cons.mp member with same | rest
    · subst position
      exact tag_unheld tree location _ child childNode childPresent childAfter
    · rcases List.mem_cons.mp rest with same | old
      · subst position
        exact tag_unheld tree location _ expr exprNode exprPresent exprAfter
      · exact False.elim (outside old)
end DuplicatePrefix.GeneralBorrowFreshSharedPrefix
#print axioms DuplicatePrefix.GeneralBorrowFreshSharedPrefix.restore_data

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshSharedPrefix." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved shared lifetime preparation dependency {dependency}"
