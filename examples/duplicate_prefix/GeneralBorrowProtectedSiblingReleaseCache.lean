import duplicate_prefix.GeneralBorrowProtectedSiblingReleaseStable
import duplicate_prefix.GeneralBorrowProtectedReadReleaseExposed
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingReleaseCache
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralBorrowExposureCardinality DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.GeneralBorrowFreshReleaseLoop
open DuplicatePrefix.GeneralBorrowExposureRelease DuplicatePrefix.GeneralBorrowExposureMapFrame
open DuplicatePrefix.GeneralBorrowProtectedReadRelease (Profile)
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

private theorem stable_nodes (before after : BorrowTree) (location : LocationTree) (tags : List BorTag) (same : after.nodes = before.nodes)
    (initial : GeneralBorrowProtectedSiblingReleaseStable.ForTags tags before location) : GeneralBorrowProtectedSiblingReleaseStable.ForTags tags after location := by
  intro index node present exposed member
  change after.nodes.get index = some node at present
  rw [same] at present
  exact initial index node present exposed member

/-- The actual virtual-unprotection exposure phase changes cache counters but
retains every exposed node's already Read-stable physical permission. -/
theorem exposure_stable (tree : BorrowTree) (tags : List BorTag) (index : UniIndex) (node : TreeNode) (depth : ParentDepth tree.nodes)
    (present : tree.nodeAt index = some node) (tagged : tree.indexOfTag node.tag = some index)
    (initial : Every (GeneralBorrowProtectedSiblingReleaseStable.ForTags tags tree) tree.locations) :
    Every (GeneralBorrowProtectedSiblingReleaseStable.ForTags tags (tree.updateExposureForProtectorRelease node.tag).tree)
      (tree.updateExposureForProtectorRelease node.tag).tree.locations := by
  cases exposed : node.isExposed with
  | false =>
    have actual : tree.updateExposureForProtectorRelease node.tag = ⟨tree,.ok ()⟩ := by
      simp [BorrowTree.updateExposureForProtectorRelease,tagged,present,exposed]
    rw [actual];exact initial
  | true =>
    let update := GeneralBorrowProtectorReleaseExposureCache.callback tree index node
    have each : ∀ location,GeneralBorrowProtectedSiblingReleaseStable.ForTags tags tree location →
        (update location).2 = .ok () ∧ GeneralBorrowProtectedSiblingReleaseStable.ForTags tags tree (update location).1 := by
      intro location good
      have cacheSuccess := GeneralBorrowExposure.update_exposure_succeeds location.exposedCache tree.nodes depth index node present
        (((location.perms.get index).getD node.defaultLocationState).permission.strongestAllowedLocalAccess true)
        (((location.perms.get index).getD node.defaultLocationState).permission.strongestAllowedLocalAccess false)
      refine ⟨?_,good⟩
      change (location.exposedCache.updateExposure tree.nodes index _ _).outcome.mapError _ = .ok ()
      rw [cacheSuccess];rfl
    have all := GeneralBorrowLocationUpdateProperty.every tree update (GeneralBorrowProtectedSiblingReleaseStable.ForTags tags tree)
      (GeneralBorrowProtectedSiblingReleaseStable.ForTags tags tree) initial each
    have nodes := GeneralBorrowLocationUpdateFrame.nodes tree update
    have actual : tree.updateExposureForProtectorRelease node.tag = source_location_update tree update := by
      unfold BorrowTree.updateExposureForProtectorRelease
      simp only [tagged,present,exposed,Bool.not_true,Bool.false_eq_true,↓reduceIte,Id.run,pure]
      rfl
    rw [actual]
    intro position valid
    exact stable_nodes tree _ _ tags nodes (all.2 position valid)

/-- Actual full-table release preserves coherence under the virtual table with
this tag removed. Previously virtually-unheld exposed tags are safe because
their formed physical permissions are Read-stable. The current tag need not be
selected or Read-stable, so a last unconflicted exposed reservation is admitted; no full-table cache
coherence is substituted for this virtual invariant. -/
theorem release (tree : BorrowTree) (protections virtual : ProtectedTags) (tags : List BorTag)
    (coverage : ∀ tag,protections.contains tag ≠ virtual.contains tag → tag ∈ tags) (anchor root : UniIndex)
    (node : TreeNode) (present : tree.nodeAt anchor = some node) (tagged : tree.indexOfTag node.tag = some anchor)
    (held : protections.contains node.tag = true) (virtualHeld : virtual.contains node.tag = true)
    (nodeTags : ∀ index node,tree.nodeAt index = some node → tree.indexOfTag node.tag = some index)
    (fits : tree.nodes.data.size ≤ 4294967296) (depth : ParentDepth tree.nodes)
    (children : GeneralBorrowGraph.ChildNodes tree) (roots : tree.roots = #[root])
    (covered : GeneralBorrowGraph.RootsCover tree)
    (initial : Every (Profile tree protections) tree.locations)
    (cache : Every (fun location => LocationCoherent tree location virtual) tree.locations)
    (stable : Every (GeneralBorrowProtectedSiblingReleaseStable.ForTags tags tree) tree.locations) :
    let result := tree.releaseProtector node.tag protections
    result.status = .Released ∧ result.tree = {tree with locations := result.tree.locations} ∧
      Every (Profile result.tree protections) result.tree.locations ∧
      Every (fun location => LocationCoherent result.tree location (virtual.remove node.tag)) result.tree.locations ∧
      Every (GeneralBorrowProtectedSiblingReleaseStable.ForTags tags result.tree) result.tree.locations := by
  unfold BorrowTree.releaseProtector
  rw [tagged]
  simp only [Id.run,bind,pure,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  name_fresh_release_scan
  let predicate := Profile tree protections
  let property := fun (remaining : List Nat) (state : Option BorrowTree.ProtectorReleaseResult × BorrowTree) =>
    state.1 = none ∧ ∃ map : DedupRangeMap LocationTree,
      state.2 = {tree with locations := map} ∧ map.entries.size = tree.locations.entries.size ∧ Every predicate map ∧ Every (fun location => LocationCoherent tree location virtual) map ∧
      Every (GeneralBorrowProtectedSiblingReleaseStable.ForTags tags tree) map ∧
      ∀ position ∈ remaining,∃ valid : position < tree.locations.entries.size,∃ bounded : position < map.entries.size,
        map.entries[position] = tree.locations.entries[position]
  have step : ∀ position rest,position ∉ rest → ∀ state,property (position::rest) state →
      ∃ next,scan position state = .yield next ∧ property rest next := by
    intro position rest notMember state good
    rcases state with ⟨returned,current⟩
    rcases good with ⟨returnedEq,map,currentEq,sizeEq,mapProfile,mapCache,mapStable,untouched⟩
    dsimp only at returnedEq currentEq
    subst returned
    subst current
    obtain ⟨oldValid,currentValid,same⟩ := untouched position (by simp)
    have skipped : property rest (none,{tree with locations := map}) := by
      refine ⟨rfl,map,rfl,sizeEq,mapProfile,mapCache,mapStable,?_⟩
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
          obtain ⟨⟨forest⟩,data⟩ := initial position oldValid
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
          have coherent : LocationCoherent tree location virtual := cache position oldValid
          have stableHere : GeneralBorrowProtectedSiblingReleaseStable.ForTags tags tree location := stable position oldValid
          have virtualNormal := GeneralBorrowProtectedVirtualReadCache.access tree location protections virtual anchor .SkipChildrenOfAccessed
            depth children node present forest data coherent (GeneralBorrowProtectedSiblingReleaseStable.virtual tree location protections virtual tags coverage stableHere)
          have validAnchor := GeneralBorrowProtectedReadPermissionMetadata.valid_anchor tree location protections anchor node present
          have compatible := GeneralBorrowProtectedReadPermissionMetadata.compatible_initial tree location protections anchor data
          have coherentActual : LocationCoherent tree
              (source_access_location (source_tree_access_at tree location (some anchor) .Read protections .SkipChildrenOfAccessed
                (tree.locations.entries[position]'oldValid).range)) virtual := by
            rw [GeneralBorrowProtectedReadSingleRoot.single_root_location tree location protections anchor root .SkipChildrenOfAccessed
              (tree.locations.entries[position]'oldValid).range forest validAnchor compatible depth children node present roots covered]
            exact virtualNormal.2.2
          have stableActual := GeneralBorrowProtectedSiblingReleaseStable.location tree location protections tags anchor root .SkipChildrenOfAccessed
            (tree.locations.entries[position]'oldValid).range depth children node present roots covered forest data stableHere
          let access := source_tree_access_at tree location (some anchor) .Read protections .SkipChildrenOfAccessed (tree.locations.entries[position]'oldValid).range
          let mutation := map.setAtPos position (source_access_location access)
          have afterSize : mutation.state.entries.size = map.entries.size := setAtPos_length map position currentValid _
          dsimp only [location] at operation
          have actual : scan position (none,{tree with locations := map}) = .yield (none,{tree with locations := mutation.state}) := by
            simp only [scan,index_exact map position currentValid,same,stored,associated,accessed,↓reduceIte,
              access_context,setAtPos_success map position currentValid,operation.1]
            rfl
          refine ⟨(none,{tree with locations := mutation.state}),actual,rfl,mutation.state,rfl,afterSize.trans sizeEq,?_,?_,?_,?_⟩
          · dsimp only [mutation]
            rw [setAtPos_exact map position currentValid]
            exact replaced_every predicate map position currentValid _ mapProfile ⟨⟨forest⟩,operation.2⟩
          · dsimp only [mutation]
            rw [setAtPos_exact map position currentValid]
            exact replaced_every _ map position currentValid _ mapCache coherentActual
          · dsimp only [mutation]
            rw [setAtPos_exact map position currentValid]
            exact replaced_every _ map position currentValid _ mapStable stableActual
          · intro other member
            obtain ⟨valid,otherValid,entryEq⟩ := untouched other (by simp [member])
            have different : position ≠ other := by intro same;subst other;exact notMember member
            refine ⟨valid,by rw [afterSize];exact otherValid,?_⟩
            dsimp only [mutation]
            simpa only [setAtPos_exact map position currentValid,replaced,Array.getElem_set,different,↓reduceIte] using entryEq
  have start : property (List.range' 0 tree.locations.entries.size) (none,tree) := by
    refine ⟨rfl,tree.locations,rfl,rfl,initial,cache,stable,?_⟩
    intro position member
    have valid : position < tree.locations.entries.size := by have := List.mem_range'_1.mp member;omega
    exact ⟨valid,valid,rfl⟩
  have final := list_tail (List.range' 0 tree.locations.entries.size) scan property (none,tree) start (List.nodup_range' 1) step
  obtain ⟨returnedEq,map,currentEq,sizeEq,mapProfile,mapCache,mapStable,_⟩ := final
  rw [returnedEq]
  simp only
  rw [currentEq]
  let stage : BorrowTree := {tree with locations := map}
  have phase := GeneralBorrowProtectedReadReleaseExposed.exposure stage protections anchor node depth present tagged mapProfile
  have cachePhase := GeneralBorrowProtectorReleaseExposureCache.release stage depth virtual anchor node present tagged nodeTags virtualHeld mapCache
  have stablePhase := exposure_stable stage tags anchor node depth present tagged mapStable
  rw [phase.1]
  exact ⟨rfl,phase.2.1,phase.2.2,cachePhase.2,stablePhase⟩

end DuplicatePrefix.GeneralBorrowProtectedSiblingReleaseCache
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowProtectedSiblingReleaseCache.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved protected sibling release cache dependency {dependency}"
