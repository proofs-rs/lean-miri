import duplicate_prefix.S02WildcardSameDestinationRootNormal
import duplicate_prefix.S02WildcardSameDestinationRootCallback
import duplicate_prefix.GeneralBorrowWildcardRootAuthorization
namespace DuplicatePrefix.S02WildcardSameDestinationRootRow
open Miri Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowNodeUpdate DuplicatePrefixBorrowAuthorization DuplicatePrefixResidualSupportAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
attribute [local irreducible] UniValMap.insert
/-- An old destination row survives adding a new hidden isolated root on an
untouched byte. The new virtual callback needs no tag-cutoff inequality. -/
theorem row (tree : BorrowTree) (mapping : UniKeyMap BorTag) (index : UniIndex) (tag : BorTag)
    (graph : GeneralBorrowStructuralHistoryState.GraphState tree)
    (vacant : tree.nodes.get index = none)
    (slot : index.toNat = tree.nodes.data.size ∨ index.toNat < tree.nodes.data.size)
    (size : tree.nodes.size ≤ (tree.nodes.insert index (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None)).size)
    (afterGraph : GeneralBorrowStructuralHistoryState.GraphState (WildcardHitZeroConstructor.installed tree mapping index tag (.ReservedFrz false) .None))
    (nonempty : 0 < tree.roots.size)
    (location : LocationTree) (protections : ProtectedTags) (clean : location.perms.get index = none)
    (source selected : Option UniIndex) (maximum : Option BorTag)
    (sourcePresent : ∀ anchor,source = some anchor → ∃ node,tree.nodeAt anchor = some node)
    (old : Row tree location protections source selected maximum) :
    Nonempty (Row (WildcardHitZeroConstructor.installed tree mapping index tag (.ReservedFrz false) .None)
      location protections source selected maximum) := by
  let node := WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None
  let after := WildcardHitZeroConstructor.installed tree mapping index tag (.ReservedFrz false) .None
  have different (query : UniIndex) (value : TreeNode) (present : tree.nodeAt query = some value) : query ≠ index := by
    intro same
    change tree.nodes.get query = some value at present
    rw [same,vacant] at present;cases present
  have oldNode (query : UniIndex) (value : TreeNode) (present : tree.nodeAt query = some value) : after.nodeAt query = some value :=
    (GeneralBorrowFreshLocation.get_other tree.nodes index query node (different query value present)).trans present
  obtain ⟨forest⟩ := graph.forest location protections
  have shape := S02WildcardSameDestinationRootTopology.nodes tree index node vacant rfl rfl slot location protections
  have freshPresent : after.nodeAt index = some node := GeneralBorrowFreshLocation.get_same tree.nodes index node
  refine ⟨{wildcard := old.wildcard,rootPath := ?_,rootPresent := ?_,cutoff := ?_,normal := ?_,callbacks := ?_}⟩
  · intro anchor same
    obtain ⟨value,present⟩ := sourcePresent anchor same
    have valid : anchor.toNat < (source_normal_projection tree location protections).topology.nodes.size := by
      rw [S02ConstructorOutsideProjection.topology_size];exact lookup_valid tree.nodes anchor value present
    have path := S02WildcardSameDestinationRootTopology.path _ _ shape forest anchor.toNat valid
    have projectionEq : (source_normal_projection after location protections).topology =
        (source_normal_projection {tree with nodes := tree.nodes.insert index node} location protections).topology := by
      unfold_general_projection
      rfl
    change ((source_normal_projection after location protections).topology.ancestorPath anchor.toNat).getLast? = _
    rw [projectionEq,path]
    exact old.rootPath anchor same
  · intro root same
    obtain ⟨value,present⟩ := old.rootPresent root same
    exact ⟨value,oldNode root value present⟩
  · cases selected with
    | none => exact old.cutoff
    | some root =>
      obtain ⟨value,present⟩ := old.rootPresent root rfl
      change maximum = (after.nodeAt root).map TreeNode.tag
      rw [oldNode root value present]
      simpa only [Option.bind_some,present,Option.map_some] using old.cutoff
  · intro anchor same
    obtain ⟨value,present⟩ := sourcePresent anchor same
    obtain ⟨normal⟩ := old.normal anchor same
    obtain ⟨next⟩ := S02WildcardSameDestinationRootNormal.normal tree graph index anchor tag value vacant present slot location protections clean normal
    exact ⟨⟨next.component,next.permissions⟩⟩
  · intro position valid neq
    by_cases oldPosition : position < tree.roots.size
    · have rootEq : after.roots[position]'valid = tree.roots[position]'oldPosition := by
        exact Array.getElem_push_lt oldPosition
      obtain ⟨support,read,write⟩ := old.callbacks position oldPosition (by rw [←rootEq];exact neq)
      refine ⟨support,?_,?_⟩
      · rw [rootEq]
        have got := GeneralBorrowWildcardRootAuthorization.insert tree (Classical.choice graph.depth) index node vacant rfl rfl size
          location location protections (fun _ _ _ => rfl) tree.roots[position] position maximum .Read support read
        refine ⟨got.rooted,got.present,got.children,got.covers,got.possible,?_,got.witness⟩
        intro entry exit legalEntry legalExit subset query value included present retained
        exact got.queries entry exit ⟨legalEntry.distinct,legalEntry.allowed⟩ ⟨legalExit.distinct,legalExit.allowed⟩ subset query value included present retained
      · rw [rootEq]
        have got := GeneralBorrowWildcardRootAuthorization.insert tree (Classical.choice graph.depth) index node vacant rfl rfl size
          location location protections (fun _ _ _ => rfl) tree.roots[position] position maximum .Write support write
        refine ⟨got.rooted,got.present,got.children,got.covers,got.possible,?_,got.witness⟩
        intro entry exit legalEntry legalExit subset query value included present retained
        exact got.queries entry exit ⟨legalEntry.distinct,legalEntry.allowed⟩ ⟨legalExit.distinct,legalExit.allowed⟩ subset query value included present retained
    · have positionEq : position = tree.roots.size := by
        change position < (tree.roots.push index).size at valid
        rw [Array.size_push] at valid
        omega
      subst position
      have rootEq : after.roots[tree.roots.size]'valid = index := Array.getElem_push_eq
      have state : (location.perms.get index).getD node.defaultLocationState = ⟨.ReservedFrz false,false,.None⟩ := by rw [clean];rfl
      refine ⟨(fun query => query = index),?_,?_⟩
      · rw [rootEq]
        exact S02WildcardSameDestinationRootCallback.authorization after afterGraph index node freshPresent rfl rfl location protections state tree.roots.size nonempty maximum .Read
      · rw [rootEq]
        exact S02WildcardSameDestinationRootCallback.authorization after afterGraph index node freshPresent rfl rfl location protections state tree.roots.size nonempty maximum .Write
end DuplicatePrefix.S02WildcardSameDestinationRootRow
