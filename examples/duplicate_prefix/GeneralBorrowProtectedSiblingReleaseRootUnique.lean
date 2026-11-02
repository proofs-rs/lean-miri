import duplicate_prefix.GeneralBorrowProtectedSiblingRootRead
import duplicate_prefix.GeneralBorrowConstructorPriorPermission
import duplicate_prefix.GeneralBorrowProtectedReadRelease
import duplicate_prefix.GeneralBorrowProtectedReadPermissionMetadata
import duplicate_prefix.GeneralBorrowProtectorReleaseExposureCache
import duplicate_prefix.GeneralBorrowLocationUpdateFrame
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingReleaseRootUnique
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.GeneralBorrowFreshReleaseLoop
open DuplicatePrefix.GeneralBorrowExposureRelease DuplicatePrefix.GeneralBorrowExposureMapFrame
def Profile (query : UniIndex) (tree : BorrowTree) (protections : ProtectedTags) (location : LocationTree) : Prop :=
  GeneralBorrowProtectedReadRelease.Profile tree protections location ∧
    GeneralBorrowConstructorPriorPermission.At query (some .Unique) location
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
private theorem roots (tree : BorrowTree) (update : LocationTree → LocationTree × Except BorrowTree.TreeMutationError Unit) :
    (source_location_update tree update).tree.roots = tree.roots := by
  unfold_source_update_locations
  simp only [Id.run,bind,pure,ForIn.forIn,Std.Legacy.Range.forIn'_eq_forIn'_range',Std.Legacy.Range.size]
  name_release_exposure_scan
  let property := fun state : Option BorrowTree.TreeMutationResult × BorrowTree =>
    state.2.roots = tree.roots ∧ ∀ returned,state.1 = some returned → returned.tree.roots = tree.roots
  have step : ∀ position member state,property state → property (scan position member state).value := by
    intro position member state good
    rcases state with ⟨returned,current⟩
    dsimp only [property] at good ⊢
    simp only [scan]
    repeat' first | split | exact ⟨good.1,fun result same => by cases same;exact good.1⟩ | exact ⟨good.1,by simp⟩
  have initial : property (none,tree) := ⟨rfl,by simp⟩
  have final := GeneralBorrowLoop.list_invariant' _ scan property step _ initial
  split
  · exact final.2 _ (by assumption)
  · exact final.1

private theorem profile_nodes (before after : BorrowTree) (protections : ProtectedTags) (location : LocationTree)
    (same : after.nodes = before.nodes) (initial : Profile query before protections location) : Profile query after protections location := by
  have projection : source_normal_projection after location protections = source_normal_projection before location protections := by
    unfold_general_projection
    unfold_general_topology
    rw [same]
  refine ⟨?_,?_⟩
  · simpa only [GeneralBorrowProtectedReadRelease.Profile,GeneralBorrowProtectedReadInvariantLocation.Data,projection] using initial.1
  · exact initial.2

private theorem profile_perms (tree : BorrowTree) (protections : ProtectedTags) (before after : LocationTree)
    (same : after.perms = before.perms) (initial : Profile query tree protections before) : Profile query tree protections after := by
  have projection : source_normal_projection tree after protections = source_normal_projection tree before protections := by
    unfold_general_projection
    rw [same]
  refine ⟨?_,?_⟩
  · simpa only [GeneralBorrowProtectedReadRelease.Profile,GeneralBorrowProtectedReadInvariantLocation.Data,projection] using initial.1
  · unfold GeneralBorrowConstructorPriorPermission.At at *
    rw [same]
    exact initial.2

/-- Real cache release for an exposed protector preserves the readable profile;
permission states and held-tag metadata remain untouched by this phase. -/
theorem exposure (tree : BorrowTree) (protections : ProtectedTags) (index : UniIndex) (node : TreeNode)
    (depth : ParentDepth tree.nodes) (present : tree.nodeAt index = some node) (tagged : tree.indexOfTag node.tag = some index)
    (initial : Every (Profile query tree protections) tree.locations) :
    let result := tree.updateExposureForProtectorRelease node.tag
    result.outcome = .ok () ∧ result.tree = {tree with locations := result.tree.locations} ∧
      Every (Profile query result.tree protections) result.tree.locations := by
  cases exposed : node.isExposed with
  | false =>
    have actual : tree.updateExposureForProtectorRelease node.tag = ⟨tree,.ok ()⟩ := by
      simp [BorrowTree.updateExposureForProtectorRelease,tagged,present,exposed]
    rw [actual]
    exact ⟨rfl,rfl,initial⟩
  | true =>
    let update := GeneralBorrowProtectorReleaseExposureCache.callback tree index node
    have each : ∀ location,Profile query tree protections location →
        (update location).2 = .ok () ∧ Profile query tree protections (update location).1 := by
      intro location good
      have cacheSuccess := GeneralBorrowExposure.update_exposure_succeeds location.exposedCache tree.nodes depth index node present
        (((location.perms.get index).getD node.defaultLocationState).permission.strongestAllowedLocalAccess true)
        (((location.perms.get index).getD node.defaultLocationState).permission.strongestAllowedLocalAccess false)
      refine ⟨?_,profile_perms tree protections location (update location).1 rfl good⟩
      change (location.exposedCache.updateExposure tree.nodes index _ _).outcome.mapError _ = .ok ()
      rw [cacheSuccess];rfl
    have all := GeneralBorrowLocationUpdateProperty.every tree update (Profile query tree protections) (Profile query tree protections) initial each
    have nodes := GeneralBorrowLocationUpdateFrame.nodes tree update
    have mapping := GeneralBorrowExposureMapFrame.locations tree update
    have sameRoots := roots tree update
    have actual : tree.updateExposureForProtectorRelease node.tag = source_location_update tree update := by
      unfold BorrowTree.updateExposureForProtectorRelease
      simp only [tagged,present,exposed,Bool.not_true,Bool.false_eq_true,↓reduceIte,Id.run,pure]
      rfl
    rw [actual]
    refine ⟨all.1,?_,?_⟩
    · cases same : (source_location_update tree update).tree
      simp only [same] at nodes mapping sameRoots ⊢
      simp only [nodes,mapping,sameRoots]
    · intro position valid
      exact profile_nodes tree _ protections _ nodes (all.2 position valid)

theorem release (tree : BorrowTree) (protections : ProtectedTags) (anchor root : UniIndex)
    (node : TreeNode) (present : tree.nodeAt anchor = some node) (tagged : tree.indexOfTag node.tag = some anchor)
    (held : protections.contains node.tag = true)
    (fits : tree.nodes.data.size ≤ 4294967296) (depth : ParentDepth tree.nodes)
    (children : GeneralBorrowGraph.ChildNodes tree) (roots : tree.roots = #[root])
    (covered : GeneralBorrowGraph.RootsCover tree)
    (rootNode : TreeNode) (rootPresent : tree.nodeAt root = some rootNode)
    (initial : Every (Profile root tree protections) tree.locations) :
    let result := tree.releaseProtector node.tag protections
    result.status = .Released ∧ result.tree = {tree with locations := result.tree.locations} ∧
      Every (Profile root result.tree protections) result.tree.locations := by
  unfold BorrowTree.releaseProtector
  rw [tagged]
  simp only [Id.run,bind,pure,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  name_fresh_release_scan
  let predicate := Profile root tree protections
  let property := fun (remaining : List Nat) (state : Option BorrowTree.ProtectorReleaseResult × BorrowTree) =>
    state.1 = none ∧ ∃ map : DedupRangeMap LocationTree,
      state.2 = {tree with locations := map} ∧ map.entries.size = tree.locations.entries.size ∧ Every predicate map ∧
      ∀ position ∈ remaining,∃ valid : position < tree.locations.entries.size,∃ bounded : position < map.entries.size,
        map.entries[position] = tree.locations.entries[position]
  have step : ∀ position rest,position ∉ rest → ∀ state,property (position::rest) state →
      ∃ next,scan position state = .yield next ∧ property rest next := by
    intro position rest notMember state good
    rcases state with ⟨returned,current⟩
    rcases good with ⟨returnedEq,map,currentEq,sizeEq,mapProfile,untouched⟩
    dsimp only at returnedEq currentEq
    subst returned
    subst current
    obtain ⟨oldValid,currentValid,same⟩ := untouched position (by simp)
    have skipped : property rest (none,{tree with locations := map}) := by
      refine ⟨rfl,map,rfl,sizeEq,mapProfile,?_⟩
      intro other member
      exact untouched other (by simp [member])
    cases stored : (tree.locations.entries[position]'oldValid).data.perms.get anchor with
    | none =>
      exact ⟨(none,{tree with locations := map}),by simp only [scan,index_exact map position currentValid,same,stored],skipped⟩
    | some before =>
      cases associated : before.permission.associatedAccess with
      | none =>
        exact ⟨(none,{tree with locations := map}),by simp only [scan,index_exact map position currentValid,same,stored,associated],skipped⟩
      | some kind =>
        cases accessed : before.accessed with
        | false =>
          exact ⟨(none,{tree with locations := map}),by simp only [scan,index_exact map position currentValid,same,stored,associated,accessed,Bool.false_eq_true,↓reduceIte],skipped⟩
        | true =>
          let location := (tree.locations.entries[position]'oldValid).data
          obtain ⟨⟨⟨forest⟩,data⟩,rootUnique⟩ := initial position oldValid
          obtain ⟨anchorValid,_⟩ := array_of_node tree anchor node present
          have valid : anchor.toNat < (source_normal_projection tree location protections).locationStates.size := by
            rw [(projection_sizes tree location protections).1];exact anchorValid
          obtain ⟨effective,effectivePresent,readable⟩ := data anchor.toNat valid
          have physical : (source_normal_projection tree location protections).stateAt anchor.toNat = some before := by
            rw [projection_location_state tree location protections anchor node present]
            simp [BorrowTree.locationStateAt,present,location,stored]
          have equal : effective = before := Option.some.inj (effectivePresent.symm.trans physical)
          subst effective
          have protection := (GeneralBorrowNormalPermissionMetadata.held tree location protections anchor node present).trans held
          rw [protection] at readable
          have notUnique := (readable.2.2 rfl).1
          have read : kind = .Read := by
            cases permission : before.permission <;> simp_all [Permission.associatedAccess]
          subst kind
          have operation := GeneralBorrowProtectedReadInvariantLocation.location tree location protections anchor root .SkipChildrenOfAccessed
            (tree.locations.entries[position]'oldValid).range forest fits depth children node present roots covered data
          let access := source_tree_access_at tree location (some anchor) .Read protections .SkipChildrenOfAccessed (tree.locations.entries[position]'oldValid).range
          let mutation := map.setAtPos position (source_access_location access)
          have afterSize : mutation.state.entries.size = map.entries.size := setAtPos_length map position currentValid _
          dsimp only [location] at operation
          have actual : scan position (none,{tree with locations := map}) = .yield (none,{tree with locations := mutation.state}) := by
            simp only [scan,index_exact map position currentValid,same,stored,associated,accessed,↓reduceIte,
              access_context,setAtPos_success map position currentValid,operation.1]
            rfl
          refine ⟨(none,{tree with locations := mutation.state}),actual,rfl,mutation.state,rfl,afterSize.trans sizeEq,?_,?_⟩
          · dsimp only [mutation]
            rw [setAtPos_exact map position currentValid]
            apply replaced_every predicate map position currentValid _ mapProfile
            refine ⟨⟨⟨forest⟩,operation.2⟩,?_⟩
            have validAnchor := GeneralBorrowProtectedReadPermissionMetadata.valid_anchor tree location protections anchor node present
            have compatible := GeneralBorrowProtectedReadPermissionMetadata.compatible_initial tree location protections anchor data
            rw [GeneralBorrowProtectedReadSingleRoot.single_root_location tree location protections anchor root .SkipChildrenOfAccessed
              (tree.locations.entries[position]'oldValid).range forest validAnchor compatible depth children node present roots covered]
            change GeneralBorrowConstructorPriorPermission.At root (some .Unique) location at rootUnique
            have old : ∃ state,location.perms.get root = some state ∧ state.permission = .Unique := by
              cases stored : location.perms.get root with
              | none => simp only [GeneralBorrowConstructorPriorPermission.At,stored,Option.map_none] at rootUnique;cases rootUnique
              | some state => exact ⟨state,rfl,by simpa only [GeneralBorrowConstructorPriorPermission.At,stored,Option.map_some,Option.some.injEq] using rootUnique⟩
            obtain ⟨state,stored,permission⟩ := GeneralBorrowProtectedSiblingRootRead.normal tree location protections anchor root node rootNode
              .SkipChildrenOfAccessed present rootPresent roots covered depth forest old
            simp only [GeneralBorrowConstructorPriorPermission.At,stored,Option.map_some,permission]

          · intro other member
            obtain ⟨valid,otherValid,entryEq⟩ := untouched other (by simp [member])
            have different : position ≠ other := by intro same;subst other;exact notMember member
            refine ⟨valid,by rw [afterSize];exact otherValid,?_⟩
            dsimp only [mutation]
            simpa only [setAtPos_exact map position currentValid,replaced,Array.getElem_set,different,↓reduceIte] using entryEq
  have start : property (List.range' 0 tree.locations.entries.size) (none,tree) := by
    refine ⟨rfl,tree.locations,rfl,rfl,initial,?_⟩
    intro position member
    have valid : position < tree.locations.entries.size := by have := List.mem_range'_1.mp member;omega
    exact ⟨valid,valid,rfl⟩
  have final := list_tail (List.range' 0 tree.locations.entries.size) scan property (none,tree) start (List.nodup_range' 1) step
  obtain ⟨returnedEq,map,currentEq,sizeEq,mapProfile,_⟩ := final
  rw [returnedEq]
  simp only
  rw [currentEq]
  let stage : BorrowTree := {tree with locations := map}
  have phase := exposure stage protections anchor node depth present tagged mapProfile
  rw [phase.1]
  refine ⟨rfl,?_,phase.2.2⟩
  have frame := phase.2.1
  exact frame

end DuplicatePrefix.GeneralBorrowProtectedSiblingReleaseRootUnique
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowProtectedSiblingReleaseRootUnique.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved protected exposed Read release dependency {dependency}"
