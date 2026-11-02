import duplicate_prefix.GeneralBorrowWildcardRootSplitAuthorization
import duplicate_prefix.GeneralBorrowIsolatedRootPositiveNormal
import duplicate_prefix.WildcardHitZeroConstructor
import duplicate_prefix.GeneralBorrowSnapshotWildcardRangeBoth
namespace DuplicatePrefix.GeneralBorrowWildcardRootRowPositive
open Miri Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2500000
/-- Row metadata ignores the segmentation stored in the surrounding tree. -/
theorem row_locations (tree : BorrowTree) (locations : DedupRangeMap LocationTree)
    (location : LocationTree) (protections : ProtectedTags)
    (source selected : Option UniIndex) (maximum : Option BorTag)
    (old : DuplicatePrefixBorrowAuthorization.Row tree location protections source selected maximum) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Row {tree with locations := locations}
      location protections source selected maximum) := by
  refine ⟨{wildcard := old.wildcard,rootPath := old.rootPath,rootPresent := old.rootPresent,
            cutoff := old.cutoff,normal := ?_,callbacks := ?_}⟩
  · intro anchor same
    obtain ⟨normal⟩ := old.normal anchor same
    exact ⟨⟨normal.component,normal.permissions⟩⟩
  · intro position valid different
    obtain ⟨support,read,write⟩ := old.callbacks position valid different
    exact ⟨support,GeneralBorrowSnapshotWildcardRangeBoth.authorization_locations tree locations location protections
      _ _ _ _ _ read,GeneralBorrowSnapshotWildcardRangeBoth.authorization_locations tree locations location protections
      _ _ _ _ _ write⟩

/-- Literal hidden root insertion and current row materialization form its full
Both row. All old callbacks are lifted; the new selected root is skipped. -/
theorem row (tree : BorrowTree) (mapping : UniKeyMap BorTag) (index : UniIndex) (tag : BorTag)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (vacant : tree.nodes.get index = none)
    (size : tree.nodes.size ≤ (tree.nodes.insert index (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None)).size)
    (bound : GeneralBorrowFreshRootCutoff.Bound tree tag)
    (before after : LocationTree) (protections : ProtectedTags)
    (slots : ∀ query node,tree.nodes.get query = some node → after.perms.get query = before.perms.get query)
    (stored : after.perms.get index = some GeneralBorrowFreshChild.inside)
    (old : DuplicatePrefixBorrowAuthorization.Row tree before protections none none none) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Row
      (WildcardHitZeroConstructor.installed tree mapping index tag (.ReservedFrz false) .None)
      after protections (some index) (some index) (some tag)) := by
  let next := WildcardHitZeroConstructor.installed tree mapping index tag (.ReservedFrz false) .None
  let node := WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None
  have present : next.nodeAt index = some node := GeneralBorrowFreshLocation.get_same tree.nodes index node
  have normal := GeneralBorrowIsolatedRootPositiveNormal.normal next after protections index node present rfl rfl stored
  have bounded := GeneralBorrowNodeUpdate.lookup_valid next.nodes index node present
  have valid : index.toNat < (source_normal_projection next default protections).topology.nodes.size := by
    unfold_general_projection
    unfold_general_topology
    simpa only [Array.size_map] using bounded
  have projected := projection_topology_node next default protections index.toNat index node rfl present
  have shape : (source_normal_projection next default protections).topology.nodes[index.toNat] = ⟨none,[]⟩ := by
    rw [Array.getElem?_eq_getElem valid,Option.getD_some] at projected
    exact projected
  have path := GeneralBorrowParentlessTraversal.ancestor_path
    (source_normal_projection next default protections).topology index.toNat valid (by rw [shape])
  refine ⟨{wildcard := ?_,rootPath := ?_,rootPresent := ?_,cutoff := ?_,normal := ?_,callbacks := ?_}⟩
  · intro impossible;cases impossible
  · intro anchor same
    have equal : anchor = index := Option.some.inj same.symm
    subst anchor
    have topology : (source_normal_projection next after protections).topology =
        (source_normal_projection next default protections).topology := by unfold_general_projection;rfl
    change ((source_normal_projection next after protections).topology.ancestorPath index.toNat).getLast? = some index.toNat
    rw [topology,path]
    rfl
  · intro root same
    have equal : root = index := Option.some.inj same.symm
    subst root
    exact ⟨node,present⟩
  · change some tag = (next.nodeAt index).map TreeNode.tag
    rw [present]
    rfl
  · intro anchor same
    have equal : anchor = index := Option.some.inj same.symm
    subst anchor
    exact normal
  · intro position positionValid different
    have oldPosition : position < tree.roots.size := by
      change position < (tree.roots.push index).size at positionValid
      rw [Array.size_push] at positionValid
      by_cases inside : position < tree.roots.size
      · exact inside
      · have same : position = tree.roots.size := by omega
        subst position
        simp only [WildcardHitZeroConstructor.installed,Array.getElem_push_eq] at different
        exact False.elim (different rfl)
    have rootEq : next.roots[position]'positionValid = tree.roots[position]'oldPosition := by
      simp only [next,WildcardHitZeroConstructor.installed,Array.getElem_push_lt oldPosition]
    obtain ⟨support,read,write⟩ := old.callbacks position oldPosition (by intro impossible;cases impossible)
    have lift (kind : AccessKind)
        (authorization : DuplicatePrefixResidualSupportAuthorization.Authorization tree before protections
          tree.roots[position] position none kind support) :=
      GeneralBorrowWildcardRootSplitAuthorization.fresh tree depth index node vacant rfl rfl size tag
        (GeneralBorrowFreshRootSupportCutoff.exposed_of_bound tree tag bound) before after protections slots
        tree.roots[position] position kind support (by intro query value included found;exact bound query value found) authorization
    refine ⟨support,?_,?_⟩
    · rw [rootEq]
      have got := lift .Read read
      refine ⟨got.rooted,got.present,got.children,got.covers,got.possible,?_,got.witness⟩
      intro entry exit legalEntry legalExit subset query value included found retained
      exact got.queries entry exit ⟨legalEntry.distinct,legalEntry.allowed⟩
        ⟨legalExit.distinct,legalExit.allowed⟩ subset query value included found retained
    · rw [rootEq]
      have got := lift .Write write
      refine ⟨got.rooted,got.present,got.children,got.covers,got.possible,?_,got.witness⟩
      intro entry exit legalEntry legalExit subset query value included found retained
      exact got.queries entry exit ⟨legalEntry.distinct,legalEntry.allowed⟩
        ⟨legalExit.distinct,legalExit.allowed⟩ subset query value included found retained
end DuplicatePrefix.GeneralBorrowWildcardRootRowPositive
