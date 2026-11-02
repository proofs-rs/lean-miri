import duplicate_prefix.GeneralBorrowSparseReadInvariant
import duplicate_prefix.GeneralBorrowLocationSifaConsistency
namespace DuplicatePrefix.GeneralBorrowPhysicalReadable
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowStorage
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

structure Profile (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) : Prop where
  present : ∀ index node,tree.nodeAt index = some node →
    GeneralBorrowProtectedReadInvariant.Readable ((location.perms.get index).getD node.defaultLocationState) (protections.contains node.tag)
  vacant : ∀ index,tree.nodes.get index = none → location.perms.get index = none

/-- Raw per-present-node bounds and clean vacancies form the exact source
normal projection's complete scalar SIFA profile, including lazy defaults. -/
theorem projection (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (fits : tree.nodes.data.size ≤ 4294967296) (initial : Profile tree location protections) :
    GeneralBorrowSparseReadInvariant.Data (GeneralBorrowGraph.Present tree) (source_normal_projection tree location protections) := by
  intro position selected bounded
  obtain ⟨index,node,indexEq,present⟩ := selected
  obtain ⟨valid,_⟩ := array_of_node tree index node present
  have converted : UniIndex.ofNat? position = some index := by rw [←indexEq];exact index_self index
  refine ⟨(location.perms.get index).getD node.defaultLocationState,projection_state tree location protections position index node converted indexEq present,?_⟩
  rw [←indexEq,GeneralBorrowNormalPermissionMetadata.held tree location protections index node present]
  exact initial.present index node present

/-- Clean absent slots are foreign to the ancestor path of a real anchor.
Their disabled ghost state is therefore compatible with a Read, while every
real node uses its formed readable permission. -/
theorem compatible (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (depth : ParentDepth tree.nodes) (fits : tree.nodes.data.size ≤ 4294967296)
    (initial : Profile tree location protections) :
    ∀ position,position < (source_normal_projection tree location protections).topology.nodes.size →
      ∃ state,(source_normal_projection tree location protections).stateAt position = some state ∧
        GeneralBorrowProtectedReadCompatible.Compatible state
          (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) anchor.toNat position)
          ((source_normal_projection tree location protections).protectedNodes.contains position) := by
  intro position bounded
  have valid : position < tree.nodes.data.size := by
    have sizes : (source_normal_projection tree location protections).topology.nodes.size = tree.nodes.data.size := by
      unfold_general_projection;unfold_general_topology
      simp only [Array.size_mapIdx,Array.size_map]
    rw [sizes] at bounded
    exact bounded
  obtain ⟨index,converted,indexEq⟩ := index_nat position (by omega)
  cases present : tree.nodeAt index with
  | some node =>
    refine ⟨(location.perms.get index).getD node.defaultLocationState,
      projection_state tree location protections position index node converted indexEq present,?_⟩
    have readable := initial.present index node present
    rw [←GeneralBorrowNormalPermissionMetadata.held tree location protections index node present] at readable
    rw [indexEq] at readable
    exact GeneralBorrowProtectedReadInvariant.compatible _ _ _ readable
  | none =>
    have clean := initial.vacant index present
    have slot : tree.nodes.data[position] = none := by
      unfold BorrowTree.nodeAt UniValMap.get at present
      rw [indexEq,Array.getElem?_eq_getElem valid] at present
      exact present
    have actual : (source_normal_projection tree location protections).stateAt position = some ⟨.Disabled,false,.None⟩ := by
      unfold_general_projection
      simp only [NormalTreeState.stateAt,Array.getElem?_mapIdx,Array.getElem?_map,Array.getElem?_eq_getElem valid,
        converted,clean,slot,Option.map_some]
    have notAncestor : position ∉ (source_normal_projection tree location protections).topology.ancestorPath anchor.toNat := by
      intro member
      obtain ⟨other,node,otherEq,found⟩ := GeneralBorrowPresence.ancestors_present
        (source_normal_projection tree location protections).topology (GeneralBorrowGraph.Present tree)
        (GeneralBorrowGraph.parents_closed tree location protections depth)
        (source_normal_projection tree location protections).topology.nodes.size anchor.toNat
        ⟨anchor,anchorNode,rfl,anchorPresent⟩ position member
      have equal : other = index := by
        have same := index_self other
        rw [otherEq,converted] at same
        exact Option.some.inj same.symm
      rw [equal,present] at found
      cases found
    refine ⟨_,actual,?_⟩
    simp [GeneralBorrowAnchor.relation,notAncestor,GeneralBorrowProtectedReadCompatible.Compatible,
      LocationState.possible,Permission.isUnique]

/-- Actual normal Read retains physical readability at present nodes and clean
vacancies. The event schedule visits only real nodes, so GC holes require no
invented readable permissions. -/
theorem normal (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (mode : ChildrenVisitMode)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (fits : tree.nodes.data.size ≤ 4294967296) (depth : ParentDepth tree.nodes)
    (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (initial : Profile tree location protections) :
    (tree.performNormalAccessAt location anchor .Read protections mode).access.status = .Completed ∧
    (tree.performNormalAccessAt location anchor .Read protections mode).outcome = .ok () ∧
    Profile tree (tree.performNormalAccessAt location anchor .Read protections mode).location protections := by
  have pointwise := compatible tree location protections anchor anchorNode anchorPresent depth fits initial
  have valid : anchor.toNat < (source_normal_projection tree location protections).topology.nodes.size := by
    obtain ⟨valid,_⟩ := array_of_node tree anchor anchorNode anchorPresent
    unfold_general_projection;unfold_general_topology
    simpa only [Array.size_mapIdx,Array.size_map] using valid
  have complete := GeneralBorrowProtectedReadLocation.normal_succeeds tree location protections anchor mode forest valid pointwise
    depth children anchorNode anchorPresent
  have masked := GeneralBorrowSparseReadInvariant.events (GeneralBorrowGraph.Present tree)
    ((source_normal_projection tree location protections).topology.traverse anchor.toNat mode
      (sourceNormalSkipped (source_normal_projection tree location protections) .Read)).2
    ((source_normal_projection tree location protections).topology.traverse anchor.toNat mode
      (sourceNormalSkipped (source_normal_projection tree location protections) .Read)).1
    (source_normal_projection tree location protections)
    (by
      intro event member
      obtain ⟨index,node,_,indexEq,present⟩ := GeneralBorrowGraph.visited_present tree location protections depth children anchor anchorNode anchorPresent .Read mode event member
      exact ⟨index,node,indexEq,present⟩)
    (projection tree location protections fits initial)
  change GeneralBorrowSparseReadInvariant.Data (GeneralBorrowGraph.Present tree)
    ((source_normal_projection tree location protections).performAccess anchor.toNat .Read mode).tree at masked
  rw [←GeneralBorrowRangePreserves.normal_projection tree location protections anchor .Read mode fits] at masked
  refine ⟨complete.1,complete.2,?_,?_⟩
  · intro query node present
    have bound : query.toNat < (source_normal_projection tree (tree.performNormalAccessAt location anchor .Read protections mode).location protections).locationStates.size := by
      rw [(projection_sizes _ _ _).1]
      exact (array_of_node tree query node present).1
    obtain ⟨state,stored,readable⟩ := masked query.toNat ⟨query,node,rfl,present⟩ bound
    have physical := projection_location_state tree (tree.performNormalAccessAt location anchor .Read protections mode).location protections query node present
    have equal : state = ((tree.performNormalAccessAt location anchor .Read protections mode).location.perms.get query).getD node.defaultLocationState := by
      apply Option.some.inj
      exact stored.symm.trans (by simpa [BorrowTree.locationStateAt,present] using physical)
    rw [equal,GeneralBorrowNormalPermissionMetadata.held tree _ protections query node present] at readable
    exact readable
  · intro query missing
    exact GeneralBorrowFreshActiveOnClean.normal_vacant tree location protections anchor query .Read mode depth children anchorNode anchorPresent missing
      (initial.vacant query missing)

end DuplicatePrefix.GeneralBorrowPhysicalReadable
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowPhysicalReadable." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved physical readability dependency {dependency}"
