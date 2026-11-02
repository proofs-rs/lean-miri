import duplicate_prefix.GeneralBorrowRange
import duplicate_prefix.GeneralBorrowProtectedReadRelease
import duplicate_prefix.GeneralBorrowProtectedSiblingRootRead
import duplicate_prefix.GeneralBorrowConstructorPriorPermission
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingRootOwned
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowExposure GeneralBorrowRange GeneralBorrowProtectedReadRelease
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Removing all protectors restores exclusive ownership at the original
Unique root: foreign states need only remain possible, even when protected
siblings were previously accessed. -/
theorem location (tree : BorrowTree) (location : LocationTree) (actual : ProtectedTags)
    (root : UniIndex) (rootNode : TreeNode) (present : tree.nodeAt root = some rootNode)
    (roots : tree.roots = #[root]) (covered : GeneralBorrowGraph.RootsCover tree) (depth : ParentDepth tree.nodes)
    (initial : Profile tree actual location)
    (unique : GeneralBorrowConstructorPriorPermission.At root (some .Unique) location) :
    LocationOwned tree {} root .Write location := by
  obtain ⟨⟨forest⟩,data⟩ := initial
  let normal := source_normal_projection tree location actual
  let ended := source_normal_projection tree location {}
  have topology : ended.topology = normal.topology := by dsimp only [ended,normal];unfold_general_projection;rfl
  have states : ended.locationStates = normal.locationStates := by dsimp only [ended,normal];unfold_general_projection;rfl
  have defaults : ended.defaultStates = normal.defaultStates := by dsimp only [ended,normal];unfold_general_projection;rfl
  have sameState : ∀ position,ended.stateAt position = normal.stateAt position := by
    intro position
    simp only [NormalTreeState.stateAt,states,defaults]
  have valid := GeneralBorrowProtectedReadPermissionMetadata.valid_anchor tree location actual root rootNode present
  have lastRoot := GeneralBorrowTerminal.ancestor_root_present normal.topology forest (GeneralBorrowGraph.Present tree)
    (GeneralBorrowGraph.parents_closed tree location actual depth) root.toNat root.toNat valid
    ⟨root,rootNode,rfl,present⟩
    (fun index _ found parentless => GeneralBorrowGraph.unique_root tree location actual root roots covered index found parentless)
  have terminal := GeneralBorrowTerminal.ancestor_terminal normal.topology forest root.toNat valid
  rw [lastRoot] at terminal
  have path : normal.topology.ancestorPath root.toNat = [root.toNat] := by
    change sourceAncestorPath normal.topology normal.topology.nodes.size root.toNat = _
    cases normal.topology.nodes.size with
    | zero => rfl
    | succ fuel => rw [GeneralBorrowPresence.ancestor_succ,terminal]
  have rootUnique : ∃ state,normal.stateAt root.toNat = some state ∧ state.permission = .Unique := by
    cases stored : location.perms.get root with
    | none => simp only [GeneralBorrowConstructorPriorPermission.At,stored,Option.map_none] at unique;cases unique
    | some state =>
      refine ⟨state,?_,by simpa only [GeneralBorrowConstructorPriorPermission.At,stored,Option.map_some,Option.some.injEq] using unique⟩
      rw [projection_location_state tree location actual root rootNode present]
      simp [BorrowTree.locationStateAt,present,stored]
  refine ⟨⟨by rw [topology];exact forest⟩,⟨?_,?_,?_,?_⟩⟩
  · rw [topology];exact valid
  · exact GeneralBorrowProtectedReadPermissionMetadata.projection_aligned tree location {}
  · exact (projection_sizes tree location {}).2.trans ((projection_sizes tree location {}).1.symm.trans (GeneralBorrowProtectedReadPermissionMetadata.projection_aligned tree location {}))
  · intro position bounded
    have oldBound : position < normal.locationStates.size := by rw [←states,GeneralBorrowProtectedReadPermissionMetadata.projection_aligned tree location {}];exact bounded
    obtain ⟨state,stored,readable⟩ := data position oldBound
    refine ⟨state,(sameState position).trans stored,?_⟩
    have free : ended.protectedNodes.contains position = false := by
      dsimp only [ended]
      unfold_general_projection
      simp [ProtectedTags.contains,ProtectedTags.get]
    unfold GeneralBorrowAnchor.relation
    rw [topology,path]
    split
    · next member =>
        have same : position = root.toNat := by simpa only [List.mem_singleton] using member
        subst position
        obtain ⟨rootState,rootStored,permission⟩ := rootUnique
        have equal : state = rootState := Option.some.inj (stored.symm.trans rootStored)
        subst state
        simp only [GeneralBorrowPermissions.AccessOwned,GeneralBorrowPermissions.Owned,GeneralBorrowPermissions.LocalOwned,permission]
        exact ⟨readable.1,True.intro⟩
    · simp only [GeneralBorrowPermissions.AccessOwned,GeneralBorrowPermissions.Owned,GeneralBorrowPermissions.ForeignOwned,free]
      exact ⟨readable.1,Or.inl free⟩
end DuplicatePrefix.GeneralBorrowProtectedSiblingRootOwned
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowProtectedSiblingRootOwned.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved released root ownership dependency {dependency}"
