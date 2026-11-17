import duplicate_prefix.GeneralBorrowProtectedReadInvariantLocation
import duplicate_prefix.GeneralBorrowFreshReleaseLoop
namespace DuplicatePrefix.GeneralBorrowProtectedReadRelease
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.GeneralBorrowFreshReleaseLoop
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

def Profile (tree : BorrowTree) (protections : ProtectedTags) (location : LocationTree) : Prop :=
  Nonempty (GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology) ∧
    GeneralBorrowProtectedReadInvariantLocation.Data tree protections location

/-- Actual full release while all other target protectors remain held. The
readable invariant admits active sibling reservations and is retained for a
second release. The source tag is unexposed; exposure-cache release is separate. -/
theorem release (tree : BorrowTree) (protections : ProtectedTags) (anchor root : UniIndex)
    (node : TreeNode) (present : tree.nodeAt anchor = some node) (tagged : tree.indexOfTag node.tag = some anchor)
    (held : protections.contains node.tag = true) (unexposed : node.isExposed = false)
    (fits : tree.nodes.data.size ≤ 4294967296) (depth : ParentDepth tree.nodes)
    (children : GeneralBorrowGraph.ChildNodes tree) (roots : tree.roots = #[root])
    (covered : GeneralBorrowGraph.RootsCover tree)
    (initial : Every (Profile tree protections) tree.locations) :
    let result := tree.releaseProtector node.tag protections
    result.status = .Released ∧ result.tree = {tree with locations := result.tree.locations} ∧
      Every (Profile result.tree protections) result.tree.locations := by
  unfold BorrowTree.releaseProtector
  rw [tagged]
  simp only [Id.run,bind,pure,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  name_fresh_release_scan
  let predicate := Profile tree protections
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
            exact replaced_every predicate map position currentValid _ mapProfile ⟨⟨forest⟩,operation.2⟩
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
  unfold BorrowTree.updateExposureForProtectorRelease
  have lookup : ({tree with locations := map} : BorrowTree).indexOfTag node.tag = some anchor := tagged
  have nodeLookup : ({tree with locations := map} : BorrowTree).nodeAt anchor = some node := present
  simp only [lookup,nodeLookup,unexposed,Bool.not_false,↓reduceIte,Id.run,pure]
  exact ⟨True.intro,True.intro,mapProfile⟩
end DuplicatePrefix.GeneralBorrowProtectedReadRelease
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowProtectedReadRelease.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved protected Read release dependency {dependency}"
