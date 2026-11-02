import duplicate_prefix.GeneralBorrowPhysicalReadableLocation
import duplicate_prefix.GeneralBorrowRootAuthorityReadLocation
import duplicate_prefix.GeneralBorrowFreshReleaseLoop
namespace DuplicatePrefix.GeneralBorrowRootAuthorityReadableRelease
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.GeneralBorrowFreshReleaseLoop
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

def Profile (tree : BorrowTree) (protections : ProtectedTags) (root : UniIndex) (location : LocationTree) : Prop :=
  Nonempty (GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology) ∧
    GeneralBorrowPhysicalReadable.Profile tree location protections ∧ GeneralBorrowStructuralHistoryRootAuthorityAt.At tree location root

/-- Every actual implicit Read in the real release scan preserves latent
owning-root authority, including held active reservation siblings and sparse
GC holes. Final authority and operation success are conclusions, not guards. -/
theorem release (tree : BorrowTree) (protections : ProtectedTags) (anchor root : UniIndex) (rootNode : TreeNode) (rootPresent : tree.nodeAt root=some rootNode)
    (node : TreeNode) (present : tree.nodeAt anchor = some node) (tagged : tree.indexOfTag node.tag = some anchor)
    (held : protections.contains node.tag = true) (unexposed : node.isExposed = false)
    (fits : tree.nodes.data.size ≤ 4294967296) (depth : ParentDepth tree.nodes)
    (children : GeneralBorrowGraph.ChildNodes tree) (roots : tree.roots = #[root])
    (covered : GeneralBorrowGraph.RootsCover tree)
    (initial : Every (Profile tree protections root) tree.locations) :
    let result := tree.releaseProtector node.tag protections
    result.status = .Released ∧ result.tree = {tree with locations := result.tree.locations} ∧
      Every (Profile result.tree protections root) result.tree.locations := by
  unfold BorrowTree.releaseProtector
  rw [tagged]
  simp only [Id.run,bind,pure,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  name_fresh_release_scan
  let predicate := Profile tree protections root
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
          obtain ⟨⟨forest⟩,data,authority⟩ := initial position oldValid
          have readable := data.present anchor node present
          change GeneralBorrowProtectedReadInvariant.Readable ((location.perms.get anchor).getD node.defaultLocationState) (protections.contains node.tag) at readable
          simp only [location,stored,Option.getD_some,held] at readable
          have notUnique := (readable.2.2 rfl).1
          have read : kind = .Read := by
            cases permission : before.permission <;> simp_all [Permission.associatedAccess]
          subst kind
          have operation := GeneralBorrowPhysicalReadableLocation.location tree location protections anchor root .SkipChildrenOfAccessed
            (tree.locations.entries[position]'oldValid).range forest fits depth children node present roots covered data
          have authorityAfter := GeneralBorrowRootAuthorityReadLocation.single_root tree location protections root anchor rootNode node rootPresent present
            .SkipChildrenOfAccessed (tree.locations.entries[position]'oldValid).range forest fits depth children roots covered data authority
          let access := source_tree_access_at tree location (some anchor) .Read protections .SkipChildrenOfAccessed (tree.locations.entries[position]'oldValid).range
          let mutation := map.setAtPos position (source_access_location access)
          have afterSize : mutation.state.entries.size = map.entries.size := setAtPos_length map position currentValid _
          dsimp only [location] at operation authorityAfter
          have actual : scan position (none,{tree with locations := map}) = .yield (none,{tree with locations := mutation.state}) := by
            simp only [scan,index_exact map position currentValid,same,stored,associated,accessed,↓reduceIte,
              access_context,setAtPos_success map position currentValid,operation.1]
            rfl
          refine ⟨(none,{tree with locations := mutation.state}),actual,rfl,mutation.state,rfl,afterSize.trans sizeEq,?_,?_⟩
          · dsimp only [mutation]
            rw [setAtPos_exact map position currentValid]
            exact replaced_every predicate map position currentValid _ mapProfile ⟨⟨forest⟩,operation.2,authorityAfter.2⟩
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
  refine ⟨True.intro,True.intro,?_⟩
  intro position valid
  obtain ⟨forest,data,authority⟩ := mapProfile position valid
  exact ⟨forest,⟨data.present,data.vacant⟩,authority.present,authority.vacant⟩
end DuplicatePrefix.GeneralBorrowRootAuthorityReadableRelease
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowRootAuthorityReadableRelease.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved protected Read release dependency {dependency}"
