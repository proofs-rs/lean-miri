import duplicate_prefix.GeneralBorrowProtectorReleaseExposureCache
import duplicate_prefix.GeneralBorrowNormalExposureCache
import duplicate_prefix.GeneralBorrowReleaseProperty
namespace DuplicatePrefix.GeneralBorrowExposedProtectorReleaseCache
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralBorrowFreshReleaseLoop
open DuplicatePrefix.GeneralBorrowExposureCardinality
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] UniValMap.insert

private theorem replaced_owned_on (predicate : LocationTree → Prop) (lower upper : UInt64)
    (map : DedupRangeMap LocationTree) (position : Nat) (valid : position < map.entries.size) (data : LocationTree)
    (owned : OwnedOn predicate lower upper map) (newOwned : predicate data) :
    OwnedOn predicate lower upper (replaced map position valid data) := by
  intro index bounded positive beforeUpper afterLower
  have oldBound : index < map.entries.size := by simpa only [replaced_length] using bounded
  rw [replaced_range map position valid data index oldBound] at beforeUpper afterLower
  by_cases same : position = index
  · subst index
    simpa [replaced] using newOwned
  · have previous := owned index oldBound positive beforeUpper afterLower
    simpa [replaced,Array.getElem_set,same] using previous

/-- Full actual protector release for either exposure flag in an arbitrary
single-root forest. Initial active-slice ownership derives every associated
access and its cache update; the final real exposure phase converts coherence
to the removed-tag table. No release or access-success premise is supplied.
The global table is removed later by endCall; bulk intermediate states require
a separate pending-release invariant when the source is exposed. -/
theorem release (tree : BorrowTree) (protections : ProtectedTags) (anchor root : UniIndex)
    (ownerKind : AccessKind) (lower upper : UInt64) (positive : lower.toNat < upper.toNat)
    (fits : tree.nodes.data.size ≤ 4294967296) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (roots : tree.roots = #[root]) (covered : GeneralBorrowGraph.RootsCover tree)
    (tagPresent : tree.indexOfTag anchorNode.tag = some anchor)
    (nodeTags : ∀ index node,tree.nodeAt index = some node → tree.indexOfTag node.tag = some index)
    (held : protections.contains anchorNode.tag = true)
    (active : ActiveOn tree anchor ownerKind lower upper)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned tree protections anchor ownerKind) lower upper tree.locations)
    (initial : Every (fun location => LocationCoherent tree location protections) tree.locations) :
    let result := tree.releaseProtector anchorNode.tag protections
    result.status = .Released ∧
      Every (fun location => LocationCoherent result.tree location (protections.remove anchorNode.tag)) result.tree.locations := by
  let tag := anchorNode.tag
  let predicate := fun location => LocationCoherent tree location protections
  have initialProperty : Every predicate tree.locations := initial
  have preserve : ∀ location range kind,predicate location → GeneralBorrowRange.LocationOwned tree protections anchor ownerKind location →
      (ownerKind = .Read → kind = .Read) →
      predicate (source_access_location (source_tree_access_at tree location (some anchor) kind protections .SkipChildrenOfAccessed range)) := by
    intro location range kind coherent permission allowed
    obtain ⟨⟨forest⟩,owner⟩ := permission
    have accessOwner := GeneralBorrowRangePreserves.owned_for_access _ anchor.toNat kind ownerKind allowed owner
    have updated := GeneralBorrowNormalExposureCache.access tree location protections anchor kind .SkipChildrenOfAccessed
      depth children anchorNode anchorPresent forest accessOwner coherent
    rw [GeneralBorrowRangePreserves.single_root_location tree location protections anchor root kind .SkipChildrenOfAccessed range
      forest accessOwner depth children anchorNode anchorPresent roots covered]
    exact updated.2.2
  dsimp only
  unfold BorrowTree.releaseProtector
  rw [tagPresent]
  simp only [Id.run,bind,pure,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  name_fresh_release_scan
  let ownership := DuplicatePrefix.GeneralBorrowRange.LocationOwned tree protections anchor ownerKind
  let property := fun (remaining : List Nat) (state : Option BorrowTree.ProtectorReleaseResult × BorrowTree) =>
    state.1 = none ∧ ∃ map : DedupRangeMap LocationTree,
      state.2 = {tree with locations := map} ∧ map.entries.size = tree.locations.entries.size ∧
      OwnedOn ownership lower upper map ∧ Every predicate map ∧
      ∀ position ∈ remaining, ∃ valid : position < tree.locations.entries.size,
        ∃ bounded : position < map.entries.size,
          map.entries[position] = tree.locations.entries[position]
  have step : ∀ position rest, position ∉ rest → ∀ state, property (position::rest) state →
      ∃ next, scan position state = .yield next ∧ property rest next := by
    intro position rest notMember state good
    rcases state with ⟨returned,current⟩
    rcases good with ⟨returnedEq,map,currentEq,sizeEq,mapOwned,mapProperty,untouched⟩
    dsimp only at returnedEq currentEq
    subst returned
    subst current
    obtain ⟨oldValid,currentValid,same⟩ := untouched position (by simp)
    have skipped : property rest (none,{tree with locations := map}) := by
      refine ⟨rfl,map,rfl,sizeEq,mapOwned,mapProperty,?_⟩
      intro other member
      exact untouched other (by simp [member])
    cases stored : (tree.locations.entries[position]'oldValid).data.perms.get anchor with
    | none =>
      refine ⟨(none,{tree with locations := map}),?_,skipped⟩
      simp only [scan,index_exact map position currentValid,same,stored]
    | some before =>
      cases associated : before.permission.associatedAccess with
      | none =>
        refine ⟨(none,{tree with locations := map}),?_,skipped⟩
        simp only [scan,index_exact map position currentValid,same,stored,associated]
      | some accessKind =>
        cases accessed : before.accessed with
        | false =>
          refine ⟨(none,{tree with locations := map}),?_,skipped⟩
          simp only [scan,index_exact map position currentValid,same,stored,associated,accessed,Bool.false_eq_true,↓reduceIte]
        | true =>
          have profile := active position oldValid before stored accessed accessKind associated
          have here := owned position oldValid positive profile.1 profile.2.1
          obtain ⟨⟨forest⟩,owner⟩ := here
          have succeeded := DuplicatePrefix.GeneralBorrowSingleRoot.access_at tree
            (tree.locations.entries[position]'oldValid).data protections anchor root accessKind .SkipChildrenOfAccessed
            (tree.locations.entries[position]'oldValid).range forest
            (DuplicatePrefix.GeneralBorrowRangePreserves.owned_for_access _ anchor.toNat accessKind ownerKind profile.2.2 owner)
            depth children anchorNode anchorPresent roots covered
          let access := source_tree_access_at tree (tree.locations.entries[position]'oldValid).data (some anchor)
            accessKind protections .SkipChildrenOfAccessed (tree.locations.entries[position]'oldValid).range
          let mutation := map.setAtPos position (source_access_location access)
          have afterSize : mutation.state.entries.size = map.entries.size :=
            setAtPos_length map position currentValid (source_access_location access)
          have actual : scan position (none,{tree with locations := map}) =
              .yield (none,{tree with locations := mutation.state}) := by
            simp only [scan,index_exact map position currentValid,same,stored,associated,accessed,↓reduceIte,
              access_context,setAtPos_success map position currentValid,succeeded]
            rfl
          refine ⟨(none,{tree with locations := mutation.state}),actual,rfl,mutation.state,rfl,
            (setAtPos_length map position currentValid _).trans sizeEq,?_,?_,?_⟩
          · have nextOwned := DuplicatePrefix.GeneralBorrowRangePreserves.location_owned tree
              (tree.locations.entries[position]'oldValid).data protections anchor root accessKind ownerKind .SkipChildrenOfAccessed
              (tree.locations.entries[position]'oldValid).range profile.2.2 fits ⟨⟨forest⟩,owner⟩
              depth children anchorNode anchorPresent roots covered
            dsimp only [mutation]
            rw [setAtPos_exact map position currentValid]
            exact replaced_owned_on ownership lower upper map position currentValid _ mapOwned nextOwned
          · dsimp only [mutation]
            rw [setAtPos_exact map position currentValid]
            apply replaced_every predicate map position currentValid _ mapProperty
            apply preserve _ _ accessKind _ ⟨⟨forest⟩,owner⟩ profile.2.2
            exact initialProperty position oldValid
          · intro other member
            obtain ⟨valid,otherValid,entryEq⟩ := untouched other (by simp [member])
            have different : position ≠ other := by intro equal;subst other;exact notMember member
            refine ⟨valid,by rw [afterSize];exact otherValid,?_⟩
            dsimp only [mutation]
            simpa only [setAtPos_exact map position currentValid,replaced,Array.getElem_set,different,↓reduceIte] using entryEq
  have initial : property (List.range' 0 tree.locations.entries.size) (none,tree) := by
    refine ⟨rfl,tree.locations,rfl,rfl,owned,initialProperty,?_⟩
    intro position member
    have valid : position < tree.locations.entries.size := by have := List.mem_range'_1.mp member;omega
    exact ⟨valid,valid,rfl⟩
  have final := list_tail (List.range' 0 tree.locations.entries.size) scan property (none,tree) initial
    (List.nodup_range' 1) step
  obtain ⟨returnedEq,map,currentEq,sizeEq,mapOwned,mapProperty,_⟩ := final
  rw [returnedEq]
  simp only
  rw [currentEq]
  let stage : BorrowTree := {tree with locations := map}
  have afterAccess : Every (fun location => LocationCoherent stage location protections) stage.locations := mapProperty
  have exposure := GeneralBorrowProtectorReleaseExposureCache.release stage depth protections anchor anchorNode
    anchorPresent tagPresent (fun index node present => nodeTags index node present) held afterAccess
  rw [exposure.1]
  exact ⟨rfl,exposure.2⟩

end DuplicatePrefix.GeneralBorrowExposedProtectorReleaseCache
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowExposedProtectorReleaseCache.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved exposed full protector-release cache dependency {dependency}"
