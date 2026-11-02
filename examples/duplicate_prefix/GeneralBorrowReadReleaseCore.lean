import duplicate_prefix.GeneralBorrowReadRowRange
import duplicate_prefix.GeneralBorrowFreshActiveWithin
namespace DuplicatePrefix.GeneralBorrowReadReleaseCore
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralBorrowFreshReleaseLoop
open DuplicatePrefix.GeneralBorrowFreshActiveWithin
set_option maxRecDepth 65536
set_option maxHeartbeats 600000

private theorem row_within (map : DedupRangeMap LocationTree) (anchor : UniIndex) (ownerKind : AccessKind)
    (lower upper : UInt64) (well : map.WellFormed) (active : Profile map anchor ownerKind lower upper)
    (position : Nat) (valid : position < map.entries.size) (state : LocationState)
    (stored : map.entries[position].data.perms.get anchor = some state) (accessed : state.accessed = true)
    (kind : AccessKind) (associated : state.permission.associatedAccess = some kind) :
    lower.toNat ≤ map.entries[position].range.start.toNat ∧ map.entries[position].range.stop.toNat ≤ upper.toNat := by
  have positive := (GeneralRangeMapGeometry.facts map well (by omega)).2.1 position valid
  have first := active map.entries[position].range.start map.entries[position].data
    ⟨position,valid,Nat.le_refl _,positive,rfl⟩ state stored accessed kind associated
  refine ⟨first.1,?_⟩
  by_cases outside : map.entries[position].range.stop.toNat ≤ upper.toNat
  · exact outside
  · have last := active upper map.entries[position].data
      ⟨position,valid,by omega,by omega,rfl⟩ state stored accessed kind associated
    omega

private theorem replace_write (map : DedupRangeMap LocationTree) (position : Nat)
    (valid : position < map.entries.size) (location : LocationTree) (anchor : UniIndex) (lower upper : UInt64)
    (active : Profile map anchor .Write lower upper)
    (inside : lower.toNat ≤ map.entries[position].range.start.toNat ∧ map.entries[position].range.stop.toNat ≤ upper.toNat) :
    Profile (replaced map position valid location) anchor .Write lower upper := by
  intro point value atPoint state stored accessed kind associated
  obtain ⟨query,bounded,startPoint,pointStop,dataEq⟩ := atPoint
  have oldBound : query < map.entries.size := by simpa only [replaced_length] using bounded
  rw [replaced_range map position valid location query oldBound] at startPoint pointStop
  by_cases same : position = query
  · subst query
    exact ⟨Nat.le_trans inside.1 startPoint,Nat.lt_of_lt_of_le pointStop inside.2,by intro h;cases h⟩
  · have dataSame : (replaced map position valid location).entries[query].data = map.entries[query].data := by
      simp [replaced,Array.getElem_set,same]
    rw [dataSame] at dataEq
    exact active point value ⟨query,oldBound,startPoint,pointStop,dataEq⟩ state stored accessed kind associated

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

/-- The real release scan executes only Read callbacks confined by the fresh
child's current activity window. Every row visitor is derived from ReadRow. -/
theorem release (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag) (anchor : UniIndex)
    (lower upper : UInt64) (positive : lower.toNat < upper.toNat)
    (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode) (notExposed : anchorNode.isExposed = false)
    (tagPresent : tree.indexOfTag tag = some anchor)
    (P : BorrowTree → LocationTree → Prop)
    (context : ∀ map location,P tree location → P {tree with locations := map} location)
    (callback : ∀ location,P tree location → GeneralBorrowSnapshotWildcardRangeBoth.Runtime tree protections location →
      ∀ range : ByteRange,
      let accessed := source_tree_access_at tree location (some anchor) .Read protections .SkipChildrenOfAccessed range
      source_access_status accessed = none ∧ P tree (source_access_location accessed) ∧
        GeneralBorrowSnapshotWildcardRangeBoth.Runtime tree protections (source_access_location accessed))
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree anchor .Read lower upper)
    (well : tree.locations.WellFormed)
    (runtime : Every (GeneralBorrowSnapshotWildcardRangeBoth.Runtime tree protections) tree.locations)
    (owned : OwnedOn (P tree) lower upper tree.locations) :
    let result := tree.releaseProtector tag protections
    result.status = .Released ∧ result.tree = {tree with locations := result.tree.locations} ∧
      OwnedOn (P result.tree) lower upper result.tree.locations ∧
      Every (GeneralBorrowSnapshotWildcardRangeBoth.Runtime result.tree protections) result.tree.locations ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin result.tree anchor .Write lower upper ∧
      result.tree.locations.WellFormed ∧ result.tree.locations.size = tree.locations.size := by
  have activeRows := GeneralBorrowFreshActiveWithin.active_on tree anchor .Read lower upper well active
  unfold BorrowTree.releaseProtector
  rw [tagPresent]
  simp only [Id.run,bind,pure,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  name_fresh_release_scan
  let predicate := P tree
  let property := fun (remaining : List Nat) (state : Option BorrowTree.ProtectorReleaseResult × BorrowTree) =>
    state.1 = none ∧ ∃ map : DedupRangeMap LocationTree,
      state.2 = {tree with locations := map} ∧ map.entries.size = tree.locations.entries.size ∧
      OwnedOn predicate lower upper map ∧
      Every (GeneralBorrowSnapshotWildcardRangeBoth.Runtime tree protections) map ∧ GeneralBorrowFreshActiveWithin.Profile map anchor .Write lower upper ∧ map.WellFormed ∧
      map.entries.map (·.range) = tree.locations.entries.map (·.range) ∧
      ∀ position ∈ remaining, ∃ valid : position < tree.locations.entries.size,
        ∃ bounded : position < map.entries.size,
          map.entries[position] = tree.locations.entries[position]
  have step : ∀ position rest, position ∉ rest → ∀ state, property (position::rest) state →
      ∃ next, scan position state = .yield next ∧ property rest next := by
    intro position rest notMember state good
    rcases state with ⟨returned,current⟩
    rcases good with ⟨returnedEq,map,currentEq,sizeEq,mapOwned,mapRuntime,mapActive,mapWell,mapRanges,untouched⟩
    dsimp only at returnedEq currentEq
    subst returned
    subst current
    obtain ⟨oldValid,currentValid,same⟩ := untouched position (by simp)
    have skipped : property rest (none,{tree with locations := map}) := by
      refine ⟨rfl,map,rfl,sizeEq,mapOwned,mapRuntime,mapActive,mapWell,mapRanges,?_⟩
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
          have profile := activeRows position oldValid before stored accessed accessKind associated
          have here := owned position oldValid positive profile.1 profile.2.1
          have kindEq : accessKind = .Read := profile.2.2 rfl
          subst accessKind
          have succeeded := callback (tree.locations.entries[position]'oldValid).data here
            (runtime position oldValid) (tree.locations.entries[position]'oldValid).range
          let access := source_tree_access_at tree (tree.locations.entries[position]'oldValid).data (some anchor)
            .Read protections .SkipChildrenOfAccessed (tree.locations.entries[position]'oldValid).range
          let mutation := map.setAtPos position (source_access_location access)
          have afterSize : mutation.state.entries.size = map.entries.size :=
            setAtPos_length map position currentValid (source_access_location access)
          have actual : scan position (none,{tree with locations := map}) =
              .yield (none,{tree with locations := mutation.state}) := by
            simp only [scan,index_exact map position currentValid,same,stored,associated,accessed,↓reduceIte,
              access_context,setAtPos_success map position currentValid,succeeded.1]
            rfl
          refine ⟨(none,{tree with locations := mutation.state}),actual,rfl,mutation.state,rfl,
            (setAtPos_length map position currentValid _).trans sizeEq,?_,?_,?_,?_,?_,?_⟩
          · dsimp only [mutation]
            rw [setAtPos_exact map position currentValid]
            exact replaced_owned_on predicate lower upper map position currentValid _ mapOwned succeeded.2.1
          · dsimp only [mutation]
            rw [setAtPos_exact map position currentValid]
            exact replaced_every _ map position currentValid _ mapRuntime succeeded.2.2
          · have inside := row_within tree.locations anchor .Read lower upper well active position oldValid before stored accessed .Read associated
            have currentInside : lower.toNat ≤ map.entries[position].range.start.toNat ∧ map.entries[position].range.stop.toNat ≤ upper.toNat := by
              rw [same]
              exact inside
            dsimp only [mutation]
            rw [setAtPos_exact map position currentValid]
            exact replace_write map position currentValid _ anchor lower upper mapActive currentInside
          · dsimp only [mutation]
            rw [setAtPos_exact map position currentValid]
            exact replaced_wellFormed map position currentValid _ mapWell
          · dsimp only [mutation]
            rw [setAtPos_exact map position currentValid]
            exact (replaced_ranges map position currentValid _).trans mapRanges
          · intro other member
            obtain ⟨valid,otherValid,entryEq⟩ := untouched other (by simp [member])
            have different : position ≠ other := by intro equal;subst other;exact notMember member
            refine ⟨valid,by rw [afterSize];exact otherValid,?_⟩
            dsimp only [mutation]
            simpa only [setAtPos_exact map position currentValid,replaced,Array.getElem_set,different,↓reduceIte] using entryEq
  have initial : property (List.range' 0 tree.locations.entries.size) (none,tree) := by
    refine ⟨rfl,tree.locations,rfl,rfl,owned,runtime,GeneralBorrowFreshActiveWithin.to_write tree anchor lower upper active,well,rfl,?_⟩
    intro position member
    have valid : position < tree.locations.entries.size := by have := List.mem_range'_1.mp member;omega
    exact ⟨valid,valid,rfl⟩
  have final := list_tail (List.range' 0 tree.locations.entries.size) scan property (none,tree) initial
    (List.nodup_range' 1) step
  obtain ⟨returnedEq,map,currentEq,sizeEq,mapOwned,mapRuntime,mapActive,mapWell,mapRanges,_⟩ := final
  rw [returnedEq]
  simp only
  rw [currentEq]
  unfold BorrowTree.updateExposureForProtectorRelease
  have lookup : ({tree with locations := map} : BorrowTree).indexOfTag tag = some anchor := tagPresent
  have nodeLookup : ({tree with locations := map} : BorrowTree).nodeAt anchor = some anchorNode := anchorPresent
  simp only [lookup,nodeLookup,notExposed,Bool.not_false,↓reduceIte,Id.run,pure]
  have capacity : map.size = tree.locations.size := by
    rw [size_from_ranges,mapRanges,←size_from_ranges]
  refine ⟨True.intro,True.intro,?_,?_,mapActive,mapWell,capacity⟩
  · intro position valid positive start stop
    exact context map _ (mapOwned position valid positive start stop)
  · intro position valid
    exact GeneralBorrowSnapshotWildcardRangeBoth.runtime_locations tree map _ protections (mapRuntime position valid)

end DuplicatePrefix.GeneralBorrowReadReleaseCore
