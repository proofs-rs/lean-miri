import duplicate_prefix.GeneralBorrowForestMixedSlice
import duplicate_prefix.GeneralBorrowForestMixedReleaseFrame
import duplicate_prefix.GeneralBorrowForestForeignClean
import duplicate_prefix.GeneralBorrowGcVacantClean
import duplicate_prefix.GeneralBorrowFreshActiveWithin
import duplicate_prefix.GeneralBorrowFreshReleaseLoop

namespace DuplicatePrefix.GeneralBorrowForestReleaseVacantClean
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.GeneralRangeMapOrigins
open GeneralBorrowFreshReleaseLoop (list_tail access_context ActiveOn)
open GeneralBorrowForestAccessData (Context)
open GeneralBorrowForestMixedAccess (Data)
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

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

/-- The REAL implicit protector-end access loop completes on a general
multiple-root forest and retains all shared Read next-input records. Activity must
be confined to the owned slice; constructor/Clean stages derive that fact.
ActiveOn is permission/range DATA, not operation success. Read associated permissions and the actual SkipChildrenOfAccessed mode are handled. -/
theorem release_query (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag)
    (anchor primary : UniIndex) (extras : List UniIndex) (writable : Nat → Bool)
    (lower upper : UInt64) (positive : lower.toNat < upper.toNat)
    (fits : tree.nodes.data.size ≤ 4294967296) (context : Context tree anchor primary extras)
    (tagPresent : tree.indexOfTag tag = some anchor)
    (active : ActiveOn tree anchor .Read lower upper)
    (owned : OwnedOn (fun location => Nonempty (Data tree location protections anchor primary extras writable)) lower upper tree.locations)
    (query : UniIndex) (vacant : tree.nodes.get query = none)
    (clean : Every (fun location : LocationTree => location.perms.get query = none) tree.locations) :
    let result := tree.releaseProtector tag protections
    result.status = .Released ∧
      result.tree = {tree with locations := result.tree.locations} ∧
      OwnedOn (fun location => Nonempty (Data result.tree location protections anchor primary extras writable)) lower upper result.tree.locations ∧
      Every (fun location : LocationTree => location.perms.get query = none) result.tree.locations := by
  unfold BorrowTree.releaseProtector
  rw [tagPresent]
  simp only [Id.run,bind,pure,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  name_fresh_release_scan
  let predicate := fun location => Nonempty (GeneralBorrowForestMixedAccess.Data tree location protections anchor primary extras writable)
  let property := fun (remaining : List Nat) (state : Option BorrowTree.ProtectorReleaseResult × BorrowTree) =>
    state.1 = none ∧ ∃ map : DedupRangeMap LocationTree,
      state.2 = {tree with locations := map} ∧ map.entries.size = tree.locations.entries.size ∧
      OwnedOn predicate lower upper map ∧ Every (fun location : LocationTree => location.perms.get query = none) map ∧
      ∀ position ∈ remaining, ∃ valid : position < tree.locations.entries.size,
        ∃ bounded : position < map.entries.size,
          map.entries[position] = tree.locations.entries[position]
  have step : ∀ position rest, position ∉ rest → ∀ state, property (position::rest) state →
      ∃ next, scan position state = .yield next ∧ property rest next := by
    intro position rest notMember state good
    rcases state with ⟨returned,current⟩
    rcases good with ⟨returnedEq,map,currentEq,sizeEq,mapOwned,mapClean,untouched⟩
    dsimp only at returnedEq currentEq
    subst returned
    subst current
    obtain ⟨oldValid,currentValid,same⟩ := untouched position (by simp)
    have skipped : property rest (none,{tree with locations := map}) := by
      refine ⟨rfl,map,rfl,sizeEq,mapOwned,mapClean,?_⟩
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
          obtain ⟨data⟩ := here
          have localFacts :
              source_access_status (source_tree_access_at tree (tree.locations.entries[position]'oldValid).data (some anchor)
                accessKind protections .SkipChildrenOfAccessed (tree.locations.entries[position]'oldValid).range) = none ∧
              Nonempty (Data tree
                (source_access_location (source_tree_access_at tree (tree.locations.entries[position]'oldValid).data (some anchor)
                  accessKind protections .SkipChildrenOfAccessed (tree.locations.entries[position]'oldValid).range))
                protections anchor primary extras writable) := by
            have readKind : accessKind = .Read := profile.2.2 rfl
            cases readKind
            exact GeneralBorrowForestMixedAccess.access tree (tree.locations.entries[position]'oldValid).data protections
              anchor primary extras writable .SkipChildrenOfAccessed (tree.locations.entries[position]'oldValid).range context data fits
          have succeeded := localFacts.1
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
          · have nextOwned := localFacts.2
            dsimp only [mutation]
            rw [setAtPos_exact map position currentValid]
            exact replaced_owned_on predicate lower upper map position currentValid _ mapOwned nextOwned
          · have cleanActual : (source_access_location access).perms.get query = none := by
              have readKind : accessKind = .Read := profile.2.2 rfl
              cases readKind
              exact GeneralBorrowForestForeignClean.local_clean tree (tree.locations.entries[position]'oldValid).data protections
                anchor primary query extras .SkipChildrenOfAccessed (tree.locations.entries[position]'oldValid).range
                context data.base fits vacant (by rw [←same];exact mapClean position currentValid)
            dsimp only [mutation]
            rw [setAtPos_exact map position currentValid]
            exact replaced_every _ map position currentValid _ mapClean cleanActual
          · intro other member
            obtain ⟨valid,otherValid,entryEq⟩ := untouched other (by simp [member])
            have different : position ≠ other := by intro equal;subst other;exact notMember member
            refine ⟨valid,by rw [afterSize];exact otherValid,?_⟩
            dsimp only [mutation]
            simpa only [setAtPos_exact map position currentValid,replaced,Array.getElem_set,different,↓reduceIte] using entryEq
  have initial : property (List.range' 0 tree.locations.entries.size) (none,tree) := by
    refine ⟨rfl,tree.locations,rfl,rfl,owned,clean,?_⟩
    intro position member
    have valid : position < tree.locations.entries.size := by have := List.mem_range'_1.mp member;omega
    exact ⟨valid,valid,rfl⟩
  have final := list_tail (List.range' 0 tree.locations.entries.size) scan property (none,tree) initial
    (List.nodup_range' 1) step
  obtain ⟨returnedEq,map,currentEq,sizeEq,mapOwned,mapClean,_⟩ := final
  rw [returnedEq]
  simp only
  rw [currentEq]
  unfold BorrowTree.updateExposureForProtectorRelease
  have lookup : ({tree with locations := map} : BorrowTree).indexOfTag tag = some anchor := tagPresent
  have nodeLookup : ({tree with locations := map} : BorrowTree).nodeAt anchor = some context.anchorNode := context.anchorPresent
  simp only [lookup,nodeLookup,(context.unexposed anchor context.anchorNode context.anchorPresent),Bool.not_false,↓reduceIte,Id.run,pure]
  refine ⟨True.intro,True.intro,?_,mapClean⟩
  intro position valid positive start stop
  obtain ⟨data⟩ := mapOwned position valid positive start stop
  exact ⟨GeneralBorrowForestMixedSlice.on_map tree map _ protections anchor primary extras writable data⟩
/-- Actual multiple-root mixed protector release preserves every physically
vacant permission slot from initial Clean data. No complete SIFA profile,
poststate Clean assertion or successful release is supplied. -/
theorem release (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag)
    (anchor primary : UniIndex) (extras : List UniIndex) (writable : Nat → Bool)
    (lower upper : UInt64) (positive : lower.toNat < upper.toNat)
    (fits : tree.nodes.data.size ≤ 4294967296) (context : Context tree anchor primary extras)
    (tagPresent : tree.indexOfTag tag = some anchor)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree anchor .Read lower upper)
    (well : tree.locations.WellFormed)
    (owned : OwnedOn (fun location => Nonempty (Data tree location protections anchor primary extras writable)) lower upper tree.locations)
    (clean : GeneralBorrowGcVacantClean.VacantClean tree) :
    GeneralBorrowGcVacantClean.VacantClean (tree.releaseProtector tag protections).tree := by
  have activity := GeneralBorrowFreshActiveWithin.active_on tree anchor .Read lower upper well active
  have framed := GeneralBorrowForestMixedReleaseFrame.release tree protections tag anchor primary extras writable lower upper positive fits context
    tagPresent activity owned
  intro query vacant
  have oldVacant : tree.nodes.get query = none := by
    change (tree.releaseProtector tag protections).tree.nodes.get query = none at vacant
    rw [framed.2.1] at vacant
    exact vacant
  have result := release_query tree protections tag anchor primary extras writable lower upper positive fits context
    tagPresent activity owned query oldVacant (clean query oldVacant)
  exact result.2.2.2

end DuplicatePrefix.GeneralBorrowForestReleaseVacantClean

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowForestReleaseVacantClean.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved forest release VacantClean dependency {dependency}"
