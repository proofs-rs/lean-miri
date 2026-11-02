import duplicate_prefix.GeneralBorrowFreshActiveWithinAccess
import duplicate_prefix.GeneralBorrowForestMutableSlice
namespace DuplicatePrefix.GeneralBorrowForestAsMutReleaseData
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralBorrowFreshActiveWithin
open DuplicatePrefix.GeneralBorrowFreshReleaseLoop
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- A strong bytewise activity profile bounds both endpoints of every active
positive segment, including segments later visited by a protector release. -/
theorem row_within (map : DedupRangeMap LocationTree) (anchor : UniIndex) (ownerKind : AccessKind)
    (lower upper : UInt64) (well : map.WellFormed) (active : Profile map anchor ownerKind lower upper)
    (position : Nat) (valid : position < map.entries.size) (state : LocationState)
    (stored : map.entries[position].data.perms.get anchor = some state) (accessed : state.accessed = true)
    (kind : AccessKind) (associated : state.permission.associatedAccess = some kind) :
    lower.toNat ≤ map.entries[position].range.start.toNat ∧ map.entries[position].range.stop.toNat ≤ upper.toNat := by
  have positive := (GeneralRangeMapGeometry.facts map well (by omega)).2.1 position valid
  have first := active map.entries[position].range.start map.entries[position].data
    ⟨position,valid,Nat.le_refl _,positive,rfl⟩ state stored accessed kind associated
  let last := UInt64.ofNat (map.entries[position].range.stop.toNat-1)
  have lastNat : last.toNat = map.entries[position].range.stop.toNat-1 := by
    simp only [last,UInt64.toNat_ofNat']
    apply Nat.mod_eq_of_lt
    have bound := map.entries[position].range.stop.toNat_lt
    omega
  have final := active last map.entries[position].data ⟨position,valid,by rw [lastNat];omega,by rw [lastNat];omega,rfl⟩
    state stored accessed kind associated
  rw [lastNat] at final
  exact ⟨first.1,by omega⟩

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

/-- Completion, structural metadata, range-map geometry and an older mutable
anchor's strong activity profile follow from the actual helper release loop. -/
theorem release (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag) (anchor root : UniIndex) (extras : List UniIndex)
     (lower upper : UInt64) (positive : lower.toNat < upper.toNat)
    (fits : tree.nodes.data.size ≤ 4294967296)
    (context : DuplicatePrefix.GeneralBorrowForestAccessData.Context tree anchor root extras)
    (tagPresent : tree.indexOfTag tag = some anchor)
    (within : ActiveWithin tree anchor .Write lower upper)
    (owned : OwnedOn (fun location => Nonempty (DuplicatePrefix.GeneralBorrowForestMutableAccess.Data tree location protections anchor root extras)) lower upper tree.locations)
    (well : tree.locations.WellFormed) (target : UniIndex) (targetLower targetUpper : UInt64)
    (lowerInside : targetLower.toNat ≤ lower.toNat) (upperInside : upper.toNat ≤ targetUpper.toNat)
    (targetWithin : ActiveWithin tree target .Write targetLower targetUpper) :
    let result := tree.releaseProtector tag protections
    result.status = .Released ∧
      (∃ map, result.tree = {tree with locations := map} ∧ map.WellFormed ∧ map.size = tree.locations.size) ∧
      ActiveWithin result.tree target .Write targetLower targetUpper ∧
      OwnedOn (fun location => Nonempty (DuplicatePrefix.GeneralBorrowForestMutableAccess.Data result.tree location protections anchor root extras)) lower upper result.tree.locations := by
  have active := GeneralBorrowFreshActiveWithin.active_on tree anchor .Write lower upper well within
  unfold BorrowTree.releaseProtector
  rw [tagPresent]
  simp only [Id.run,bind,pure,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  name_fresh_release_scan
  let predicate := fun location => Nonempty (DuplicatePrefix.GeneralBorrowForestMutableAccess.Data tree location protections anchor root extras)
  let property := fun (remaining : List Nat) (state : Option BorrowTree.ProtectorReleaseResult × BorrowTree) =>
    state.1 = none ∧ ∃ map : DedupRangeMap LocationTree,
      state.2 = {tree with locations := map} ∧ map.entries.size = tree.locations.entries.size ∧
      OwnedOn predicate lower upper map ∧ map.WellFormed ∧ map.size = tree.locations.size ∧
      Profile map target .Write targetLower targetUpper ∧
      ∀ position ∈ remaining, ∃ valid : position < tree.locations.entries.size,
        ∃ bounded : position < map.entries.size,
          map.entries[position] = tree.locations.entries[position]
  have step : ∀ position rest, position ∉ rest → ∀ state, property (position::rest) state →
      ∃ next, scan position state = .yield next ∧ property rest next := by
    intro position rest notMember state good
    rcases state with ⟨returned,current⟩
    rcases good with ⟨returnedEq,map,currentEq,sizeEq,mapOwned,mapWell,mapCapacity,mapActive,untouched⟩
    dsimp only at returnedEq currentEq
    subst returned
    subst current
    obtain ⟨oldValid,currentValid,same⟩ := untouched position (by simp)
    have skipped : property rest (none,{tree with locations := map}) := by
      refine ⟨rfl,map,rfl,sizeEq,mapOwned,mapWell,mapCapacity,mapActive,?_⟩
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
          obtain ⟨localData⟩ := here
          have localGood := DuplicatePrefix.GeneralBorrowForestMutableAccess.access tree
            (tree.locations.entries[position]'oldValid).data protections anchor root extras accessKind .SkipChildrenOfAccessed
            (tree.locations.entries[position]'oldValid).range context localData fits
          have succeeded := localGood.1
          have childBounds := row_within tree.locations anchor .Write lower upper well within position oldValid before stored accessed accessKind associated
          have currentBounds : targetLower.toNat ≤ map.entries[position].range.start.toNat ∧
              map.entries[position].range.stop.toNat ≤ targetUpper.toNat := by
            rw [same]
            exact ⟨Nat.le_trans lowerInside childBounds.1,Nat.le_trans childBounds.2 upperInside⟩
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
            (setAtPos_length map position currentValid _).trans sizeEq,?_,?_,?_,?_,?_⟩
          · have nextOwned := localGood.2
            dsimp only [mutation]
            rw [setAtPos_exact map position currentValid]
            exact replaced_owned_on predicate lower upper map position currentValid _ mapOwned nextOwned
          · dsimp only [mutation]
            rw [setAtPos_exact map position currentValid]
            exact replaced_wellFormed map position currentValid _ mapWell
          · dsimp only [mutation]
            rw [setAtPos_exact map position currentValid]
            exact (replaced_size map position currentValid _).trans mapCapacity
          · dsimp only [mutation]
            rw [setAtPos_exact map position currentValid]
            exact replace_write map position currentValid _ target targetLower targetUpper mapActive currentBounds
          · intro other member
            obtain ⟨valid,otherValid,entryEq⟩ := untouched other (by simp [member])
            have different : position ≠ other := by intro equal;subst other;exact notMember member
            refine ⟨valid,by rw [afterSize];exact otherValid,?_⟩
            dsimp only [mutation]
            simpa only [setAtPos_exact map position currentValid,replaced,Array.getElem_set,different,↓reduceIte] using entryEq
  have initial : property (List.range' 0 tree.locations.entries.size) (none,tree) := by
    refine ⟨rfl,tree.locations,rfl,rfl,owned,well,rfl,targetWithin,?_⟩
    intro position member
    have valid : position < tree.locations.entries.size := by have := List.mem_range'_1.mp member;omega
    exact ⟨valid,valid,rfl⟩
  have final := list_tail (List.range' 0 tree.locations.entries.size) scan property (none,tree) initial
    (List.nodup_range' 1) step
  obtain ⟨returnedEq,map,currentEq,sizeEq,mapOwned,mapWell,mapCapacity,mapActive,_⟩ := final
  rw [returnedEq]
  simp only
  rw [currentEq]
  unfold BorrowTree.updateExposureForProtectorRelease
  have lookup : ({tree with locations := map} : BorrowTree).indexOfTag tag = some anchor := tagPresent
  have nodeLookup : ({tree with locations := map} : BorrowTree).nodeAt anchor = some context.anchorNode := context.anchorPresent
  simp only [lookup,nodeLookup,(context.unexposed anchor context.anchorNode context.anchorPresent),Bool.not_false,↓reduceIte,Id.run,pure]
  refine ⟨True.intro,⟨map,rfl,mapWell,mapCapacity⟩,mapActive,?_⟩
  intro position valid positive start stop
  obtain ⟨data⟩ := mapOwned position valid positive start stop
  exact ⟨DuplicatePrefix.GeneralBorrowForestMutableSlice.on_map tree map _ protections anchor root extras data⟩
end DuplicatePrefix.GeneralBorrowForestAsMutReleaseData
