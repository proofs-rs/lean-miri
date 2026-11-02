import duplicate_prefix.GeneralBorrowStarOwnership
import duplicate_prefix.GeneralBorrowFullSharedRead
namespace DuplicatePrefix.GeneralBorrowStarRead
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowFreshAnchor
open DuplicatePrefix.GeneralBorrowAnchor DuplicatePrefix.GeneralBorrowPermissions DuplicatePrefix.GeneralBorrowSharedGeneratorProfile
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.RangeMapNonempty DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralBorrowExposeReadFold
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

private theorem parent_path (tree : BorrowTree) (root : UniIndex) (node : TreeNode) (present : tree.nodeAt root = some node) (location : LocationTree)
    (parentless : node.parent = none) :
    (source_normal_projection tree location {}).topology.ancestorPath root.toNat = [root.toNat] := by
  have parent : (GeneralBorrowPresence.nodeData (source_normal_projection tree location {}).topology root.toNat).parent = none := by
    change ((source_normal_projection tree location {}).topology.nodes[root.toNat]?.getD ⟨none,[]⟩).parent = none
    rw [projection_topology_node tree location {} root.toNat root node rfl present]
    simp only [parentless,Option.map_none]
  change sourceAncestorPath (source_normal_projection tree location {}).topology
    (source_normal_projection tree location {}).topology.nodes.size root.toNat = _
  cases (source_normal_projection tree location {}).topology.nodes.size with
  | zero => rfl
  | succ fuel => rw [GeneralBorrowPresence.ancestor_succ,parent]

/-- The exact sparse profile supplies root Read ownership.
No successful access or history-size premise is needed. Vacancies are clean. -/
theorem read_owned (tree : BorrowTree) (root : UniIndex) (node : TreeNode) (present : tree.nodeAt root = some node) (location : LocationTree)
    (parentless : node.parent = none) (profile : Profile tree location root)
    (fits : tree.nodes.size ≤ 4294967296) :
    AnchorOwned (source_normal_projection tree location {}) root.toNat .Read := by
  change tree.nodes.data.size ≤ 4294967296 at fits
  have topologySize : (source_normal_projection tree location {}).topology.nodes.size = tree.nodes.data.size := by
    unfold_general_projection
    unfold_general_topology
    simp only [Array.size_map]
  have emptyProtected : (source_normal_projection tree location {}).protectedNodes = [] := by
    unfold_general_projection
    simp [ProtectedTags.contains,ProtectedTags.get]
  have parentValid := GeneralBorrowNodeUpdate.lookup_valid tree.nodes root node present
  refine ⟨by rw [topologySize];exact parentValid,
    (projection_sizes tree location {}).1.trans topologySize.symm,
    (projection_sizes tree location {}).2.trans topologySize.symm,?_⟩
  intro position valid
  have bounded : position < tree.nodes.data.size := by rw [←topologySize];exact valid
  have fit : position ≤ 4294967295 := by omega
  obtain ⟨index,converted,indexEq⟩ := index_nat position fit
  have relation : relation (source_normal_projection tree location {}) root.toNat position =
      if position = root.toNat then .LocalAccess else .ForeignAccess := by
    simp only [GeneralBorrowAnchor.relation,parent_path tree root node present location parentless,List.mem_singleton]
  have unheld : (source_normal_projection tree location {}).protectedNodes.contains position = false := by rw [emptyProtected];rfl
  by_cases sameRoot : index = root
  · subst index
    refine ⟨GeneralBorrowWildcardLeaf.unique,?_,?_⟩
    · simpa [profile.rootStored] using projection_state tree location {} position root node converted indexEq present
    · rw [unheld,relation,←indexEq,ite_eq_left rfl]
      exact ⟨rfl,by decide⟩
  · cases present : tree.nodeAt index with
    | some node =>
      have stored := profile.shared index node present sameRoot
      refine ⟨sharedState,?_,?_⟩
      · simpa [stored] using projection_state tree location {} position index node converted indexEq present
      · rw [relation,ite_eq_right (fun same => sameRoot (GeneralBorrowNodeUpdate.index_injective index root (indexEq.trans same))),unheld]
        exact ⟨rfl,Or.inl rfl⟩
    | none =>
      have clean := profile.vacant index present
      have noRoot : position ≠ root.toNat := fun same => sameRoot (GeneralBorrowNodeUpdate.index_injective index root (indexEq.trans same))
      refine ⟨⟨.Disabled,false,.None⟩,?_,?_⟩
      · unfold_general_projection
        unfold NormalTreeState.stateAt
        simp only [Array.getElem?_mapIdx,converted,clean,Array.getElem?_map,
          Array.getElem?_eq_getElem bounded,Option.map_some]
        have slot : tree.nodes.data[position] = none := by
          unfold BorrowTree.nodeAt UniValMap.get at present
          rw [indexEq,Array.getElem?_eq_getElem bounded] at present
          exact present
        simp only [slot]
      · rw [relation,ite_eq_right noRoot,unheld]
        exact ⟨rfl,Or.inl rfl⟩

private theorem unique_stable (recorded : LocationState) (held : Bool)
    (record : GeneralBorrowWildcardLeaf.unique.recordNewAccess .Read .LocalAccess = .Recorded recorded) :
    (recorded.performAccess .Read .LocalAccess held).resultingState = GeneralBorrowWildcardLeaf.unique := by
  have same : recorded = GeneralBorrowWildcardLeaf.unique := by
    change LocationState.RecordAccessResult.Recorded GeneralBorrowWildcardLeaf.unique = .Recorded recorded at record
    exact (LocationState.RecordAccessResult.Recorded.inj record).symm
  subst recorded
  cases held <;> rfl

/-- Normal Read preserves the exact generator profile, including absent
permissions at every vacant sparse slot. All error outcomes are included. -/
theorem normal (tree : BorrowTree) (root : UniIndex) (node : TreeNode)
    (star : GeneralBorrowGeneratedStarShape.Star tree root node) (location : LocationTree)
    (protections : ProtectedTags) (mode : ChildrenVisitMode)
    (profile : GeneralBorrowSharedGeneratorProfile.Profile tree location root)
    (relations : ∀ event ∈ ((source_normal_projection tree location protections).topology.traverse root.toNat mode
        (sourceNormalSkipped (source_normal_projection tree location protections) .Read)).2,
      event.relatedness = if event.node = root.toNat then .LocalAccess else .ForeignAccess) :
    GeneralBorrowSharedGeneratorProfile.Profile tree
      (tree.performNormalAccessAt location root .Read protections mode).location root := by
  refine ⟨?_,?_,?_⟩
  · apply GeneralBorrowSharedProfileRead.normal_exact GeneralBorrowWildcardLeaf.unique tree location protections root root node mode star.present profile.rootStored
    intro event member same recorded held record
    have localEvent : event.relatedness = .LocalAccess := by simpa only [same,ite_true] using relations event member
    rw [localEvent] at record ⊢
    exact unique_stable recorded held record
  · intro index node present different
    apply GeneralBorrowSharedProfileRead.normal_exact sharedState tree location protections root index node mode present (profile.shared index node present different)
    intro event member same recorded held record
    have distinct : event.node ≠ root.toNat := by
      rw [same]
      exact fun equal => different (GeneralBorrowNodeUpdate.index_injective index root equal)
    have foreign : event.relatedness = .ForeignAccess := by simpa only [ite_eq_right distinct] using relations event member
    rw [foreign] at record
    change LocationState.RecordAccessResult.DebugAssertion = .Recorded recorded at record
    cases record
  · intro index vacant
    exact GeneralBorrowFreshActiveOnClean.normal_vacant tree location protections root index .Read mode (GeneralBorrowStarCertificates.depth tree root node star) (GeneralBorrowStarCertificates.children tree root node star) node star.present vacant (profile.vacant index vacant)

/-- Full-slice Read on a sparse star completes and retains the exact profile,
including every clean vacant permission. No allocator layout or operation
success premise is required. -/
theorem complete (tree : BorrowTree) (root : UniIndex) (node : TreeNode)
    (star : GeneralBorrowGeneratedStarShape.Star tree root node)
    (roots : tree.roots = #[root]) (tag : BorTag)
    (tagged : tree.indexOfTag tag = some root)
    (capacity : UInt64) (nonzero : capacity ≠ 0) (location : LocationTree)
    (initial : tree.locations = homogeneous capacity location)
    (profile : Profile tree location root) (fits : tree.nodes.size ≤ 4294967296) :
    let access := tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes 0)
      (Size.ofBytes capacity) .Read {} .VisitChildrenOfAccessed
    let postLocation := (tree.performNormalAccessAt location root .Read {} .VisitChildrenOfAccessed).location
    access.status = .Completed ∧
    access.tree = {tree with locations := homogeneous capacity postLocation} ∧
    Profile access.tree postLocation root := by
  dsimp only
  let depth := GeneralBorrowStarCertificates.depth tree root node star
  let children := GeneralBorrowStarCertificates.children tree root node star
  let covered := GeneralBorrowStarCertificates.covered tree root node star roots
  let forest := GeneralBorrowStarCertificates.forest tree root node star location {} fits
  have owned := read_owned tree root node star.present location star.parentless profile fits
  have success := GeneralBorrowSingleRoot.access_at tree location {} root root .Read
    .VisitChildrenOfAccessed ⟨0,capacity⟩ forest owned depth children node star.present roots covered
  have normalLocation := GeneralBorrowRangePreserves.single_root_location tree location {} root root .Read
    .VisitChildrenOfAccessed ⟨0,capacity⟩ forest owned depth children node star.present roots covered
  have exactRead :
      (tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes 0) (Size.ofBytes capacity)
        .Read {} .VisitChildrenOfAccessed).status = .Completed ∧
      (tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes 0) (Size.ofBytes capacity)
        .Read {} .VisitChildrenOfAccessed).tree =
        {tree with locations := homogeneous capacity (tree.performNormalAccessAt location root .Read {} .VisitChildrenOfAccessed).location} := by
    unfold BorrowTree.performBorrowAccessRange
    simp only [tagged,Option.isNone_some,Bool.false_eq_true,↓reduceIte,Id.run,bind,pure,initial]
    have zero : Size.ofBytes 0 = Size.ZERO := rfl
    rw [zero,iter_mut_homogeneous_full capacity location nonzero]
    simp only [Array.size_singleton,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
    simp only [show List.range' 0 1 = [0] from rfl,List.forIn_cons,List.forIn_nil,bind,pure]
    simp only [beq_self_eq_true,↓reduceIte,Array.getElem?_singleton]
    rw [setAtPos_exact (homogeneous capacity location) 0 (by change 0<1;decide)]
    simp only [success,normalLocation]
    exact ⟨by trivial,rfl⟩
  have preserved := normal tree root node star location {} .VisitChildrenOfAccessed profile
    (by
      intro event member
      have classified := (GeneralBorrowTraversal.traversal_data _ forest root.toNat owned.anchorValid
        .VisitChildrenOfAccessed (sourceNormalSkipped (source_normal_projection tree location {}) .Read)).2 event member
      simpa only [parent_path tree root node star.present location star.parentless,List.mem_singleton] using classified.2)
  refine ⟨exactRead.1,exactRead.2,?_⟩
  rw [exactRead.2]
  exact ⟨preserved.rootStored,preserved.shared,preserved.vacant⟩

end DuplicatePrefix.GeneralBorrowStarRead
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowStarRead.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved sparse star Read dependency {dependency}"
