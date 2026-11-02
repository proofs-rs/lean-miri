import duplicate_prefix.GeneralBorrowIsolatedLeafNormal
import duplicate_prefix.DuplicatePrefixBorrowAuthorization
namespace DuplicatePrefix.GeneralBorrowIsolatedRootPositiveNormal
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- An isolated protected-mutable root owns only its singleton physical component;
other roots and their permissions are arbitrary. Both scalar kinds are derived. -/
theorem normal (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (node : TreeNode) (present : tree.nodeAt anchor = some node)
    (parentless : node.parent = none) (leaf : node.children = #[])
    (stored : location.perms.get anchor = some GeneralBorrowFreshChild.inside) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree location protections anchor) := by
  let projection := source_normal_projection tree location protections
  have bounded := GeneralBorrowNodeUpdate.lookup_valid tree.nodes anchor node present
  have valid : anchor.toNat < projection.topology.nodes.size := by
    dsimp only [projection]
    unfold_general_projection
    unfold_general_topology
    simpa only [Array.size_map] using bounded
  have projected := projection_topology_node tree location protections anchor.toNat anchor node rfl present
  have shape : projection.topology.nodes[anchor.toNat] = ⟨none,[]⟩ := by
    rw [Array.getElem?_eq_getElem valid,Option.getD_some,parentless,leaf] at projected
    exact projected
  have nodeShape : GeneralBorrowPresence.nodeData projection.topology anchor.toNat = ⟨none,[]⟩ := by
    simp only [GeneralBorrowPresence.nodeData,Array.getElem?_eq_getElem valid,Option.getD_some,shape]
  let component : GeneralBorrowExposedScopedNormal.Component projection.topology anchor.toNat := {
    support := fun index => index = anchor.toNat
    anchor := rfl
    parents := by
      intro current same parent found
      subst current
      rw [nodeShape] at found
      cases found
    children := by
      intro current same child member
      subst current
      rw [nodeShape] at member
      cases member }
  refine ⟨⟨component,?_⟩⟩
  intro kind index included indexValid
  change index = anchor.toNat at included
  subst index
  have state : projection.stateAt anchor.toNat = some GeneralBorrowFreshChild.inside := by
    rw [projection_state tree location protections anchor.toNat anchor node (index_self anchor) rfl present]
    simp [stored]
  have path := GeneralBorrowParentlessTraversal.ancestor_path projection.topology anchor.toNat valid
    (by rw [shape])
  refine ⟨GeneralBorrowFreshChild.inside,state,?_⟩
  change DuplicatePrefixScalarAuthorization.Compatible GeneralBorrowFreshChild.inside kind
    (GeneralBorrowAnchor.relation projection anchor.toNat anchor.toNat) _
  simp only [GeneralBorrowAnchor.relation,path,List.mem_singleton,ite_true]
  cases kind <;> simp [DuplicatePrefixScalarAuthorization.Compatible,
    GeneralBorrowProtectedReadCompatible.Compatible,GeneralBorrowExposedConditionalWritePermissions.Compatible,
    GeneralBorrowFreshChild.inside] <;> rfl
end DuplicatePrefix.GeneralBorrowIsolatedRootPositiveNormal
