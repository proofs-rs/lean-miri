import duplicate_prefix.GeneralBorrowFreshMetadataChildDefault
import duplicate_prefix.GeneralBorrowFreshMetadataChildOld
import duplicate_prefix.GeneralBorrowFreshSharedPaths
import duplicate_prefix.GeneralBorrowStructuralReleaseGeometryFrame
namespace DuplicatePrefix.GeneralBorrowExposedConstructorAncestry
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowFreshMetadataChildAttach GeneralBorrowFreshGraph
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def topology (tree : BorrowTree) := (source_normal_projection tree default default).topology

/-- Only exposed nodes in the chosen component are constrained. Exposed nodes
in other components need not lie on this path. -/
def OnPath (tree : BorrowTree) (anchor : UniIndex) (support : Nat → Prop) : Prop :=
  ∀ query node, support query.toNat → tree.nodeAt query = some node → node.isExposed = true →
    query.toNat ∈ (topology tree).ancestorPath anchor.toNat

def extended (support : Nat → Prop) (child : UniIndex) : Nat → Prop :=
  fun position => position = child.toNat ∨ support position

/-- Actual append/SIFA exposure metadata recovers the original exposed node;
this includes sparse old node tables, not only densely populated ones. -/
theorem old_exposed (tree after : BorrowTree) (index parent query : UniIndex)
    (parentNode newNode node : TreeNode) (mapping : UniKeyMap BorTag)
    (locations : Miri.DataStructures.DedupRangeMap LocationTree)
    (atEnd : index.toNat = tree.nodes.data.size) (parentPresent : tree.nodeAt parent = some parentNode)
    (flags : GeneralBorrowFreshMetadataChildSifa.exposureShape after =
      GeneralBorrowFreshMetadataChildSifa.exposureShape (staged tree index parent parentNode newNode mapping locations))
    (different : query ≠ index) (present : after.nodeAt query = some node) (exposed : node.isExposed = true) :
    ∃ old,tree.nodeAt query = some old ∧ old.isExposed = true := by
  have same := GeneralBorrowFreshMetadataChildSifa.lookup_exposure _ after flags query
  change (after.nodeAt query).map (fun node => node.isExposed) =
    ((attached tree index parent parentNode newNode).nodeAt query).map (fun node => node.isExposed) at same
  rw [present,Option.map_some,exposed] at same
  by_cases isParent : query = parent
  · subst query
    rw [parent_lookup tree index parent parentNode newNode atEnd parentPresent] at same
    exact ⟨parentNode,parentPresent,by simpa only [Option.map_some,Option.some.injEq,updatedParent] using same.symm⟩
  · rw [other_lookup tree index parent query parentNode newNode atEnd parentPresent isParent different] at same
    cases old : tree.nodeAt query with
    | none => simp only [old,Option.map_none,reduceCtorEq] at same
    | some oldNode => exact ⟨oldNode,rfl,by simpa only [old,Option.map_some,Option.some.injEq] using same.symm⟩

theorem attach (tree after : BorrowTree) (parent child : UniIndex) (support : Nat → Prop)
    (paths : GeneralBorrowFreshSharedPaths.Attach (topology tree) (topology after) parent.toNat child.toNat)
    (old : ∀ query node,query ≠ child → after.nodeAt query = some node → node.isExposed = true →
      ∃ before,tree.nodeAt query = some before ∧ before.isExposed = true)
    (hidden : ∀ node,after.nodeAt child = some node → node.isExposed = false)
    (initial : OnPath tree parent support) : OnPath after child (extended support child) := by
  intro query node member present exposed
  have different : query ≠ child := by
    intro same
    subst query
    have flag := hidden node present
    rw [flag] at exposed
    cases exposed
  have originalMember : support query.toNat := by
    rcases member with same | original
    · exact False.elim (different (by cases query;cases child;exact congrArg UniIndex.mk (UInt32.toNat_inj.mp same)))
    · exact original
  obtain ⟨before,oldPresent,oldExposed⟩ := old query node different present exposed
  have ancestor := initial query before originalMember oldPresent oldExposed
  rw [paths.childPath]
  exact List.mem_cons_of_mem child.toNat ancestor

theorem release (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag)
    (anchor : UniIndex) (support : Nat → Prop) (initial : OnPath tree anchor support) :
    OnPath (tree.releaseProtector tag protections).tree anchor support := by
  rw [GeneralBorrowStructuralReleaseGeometryFrame.release]
  exact initial

theorem shared (input : GeneralBorrowFreshMetadataChildShared.Input) (support : Nat → Prop)
    (forest : GeneralBorrowForest.Forest (topology input.tree))
    (initial : OnPath input.tree input.parent support) :
    OnPath (GeneralBorrowFreshMetadataChildShared.result input) (GeneralBorrowFreshMetadataChildShared.index input)
      (extended support (GeneralBorrowFreshMetadataChildShared.index input)) := by
  let output := GeneralBorrowFreshMetadataChildShared.append input
  have size : (topology input.tree).nodes.size = (GeneralBorrowFreshMetadataChildShared.index input).toNat := by
    rw [GeneralBorrowFreshMetadataChildShared.at_end]
    unfold topology
    unfold_general_projection;unfold_general_topology;simp only [Array.size_map]
  have paths := GeneralBorrowFreshSharedPaths.of_append _ _ input.parent.toNat (output.extension default default default) forest
  change GeneralBorrowFreshSharedPaths.Attach (topology input.tree) (topology _) input.parent.toNat (topology input.tree).nodes.size at paths
  rw [size] at paths
  apply attach input.tree _ input.parent _ support paths
  · intro query node different present exposed
    exact old_exposed input.tree _ _ input.parent query input.parentNode _ node _ _
      (GeneralBorrowFreshMetadataChildShared.at_end input) input.parentPresent
      (GeneralBorrowFreshMetadataChildShared.exposure input) different present exposed
  · intro node present
    obtain ⟨newNode,newPresent,_,_,_,_,hidden⟩ := output.newNode
    have same : node = newNode := Option.some.inj (present.symm.trans newPresent)
    exact same ▸ hidden
  · exact initial

theorem default_child (input : GeneralBorrowFreshMetadataChildDefault.Input) (support : Nat → Prop)
    (forest : GeneralBorrowForest.Forest (topology input.tree))
    (initial : OnPath input.tree input.parent support) :
    OnPath (GeneralBorrowFreshMetadataChildDefault.result input) (GeneralBorrowFreshMetadataChildDefault.index input)
      (extended support (GeneralBorrowFreshMetadataChildDefault.index input)) := by
  let output := GeneralBorrowFreshMetadataChildDefault.append input
  have size : (topology input.tree).nodes.size = (GeneralBorrowFreshMetadataChildDefault.index input).toNat := by
    rw [GeneralBorrowFreshMetadataChildDefault.at_end]
    unfold topology
    unfold_general_projection;unfold_general_topology;simp only [Array.size_map]
  have paths := GeneralBorrowFreshSharedPaths.of_append _ _ input.parent.toNat (output.extension default default default) forest
  change GeneralBorrowFreshSharedPaths.Attach (topology input.tree) (topology _) input.parent.toNat (topology input.tree).nodes.size at paths
  rw [size] at paths
  apply attach input.tree _ input.parent _ support paths
  · intro query node different present exposed
    exact old_exposed input.tree _ _ input.parent query input.parentNode _ node _ _
      (GeneralBorrowFreshMetadataChildDefault.at_end input) input.parentPresent
      (GeneralBorrowFreshMetadataChildDefault.exposure input) different present exposed
  · intro node present
    obtain ⟨newNode,newPresent,_,_,_,_,hidden⟩ := output.newNode
    have same : node = newNode := Option.some.inj (present.symm.trans newPresent)
    exact same ▸ hidden
  · exact initial
end DuplicatePrefix.GeneralBorrowExposedConstructorAncestry
