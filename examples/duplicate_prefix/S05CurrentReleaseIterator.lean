import duplicate_prefix.GeneralBorrowFreshReleaseLoop
namespace DuplicatePrefix.S05CurrentReleaseIterator
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralBorrowProjection GeneralRangeMapState GeneralRangeMapOrigins GeneralBorrowFreshReleaseLoop
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def Rows (P : ByteRange → LocationTree → Prop) (map : DedupRangeMap LocationTree) : Prop :=
  ∀ position (valid : position < map.entries.size), P map.entries[position].range map.entries[position].data

private theorem replaced_rows (P : ByteRange → LocationTree → Prop) (map : DedupRangeMap LocationTree)
    (position : Nat) (valid : position < map.entries.size) (data : LocationTree)
    (rows : Rows P map) (updated : P map.entries[position].range data) :
    Rows P (replaced map position valid data) := by
  intro index bounded
  have oldBound : index < map.entries.size := by simpa only [replaced_length] using bounded
  by_cases same : position = index
  · subst index
    simpa [replaced] using updated
  · simpa [replaced,Array.getElem_set,same] using rows index oldBound

/-- Actual hidden-protector release over every stored row. The internal row certificate
provides the real implicit access and its scalar invariant; roots are unrestricted.
The final exposure update is inert because the stored anchor is not exposed. -/
theorem release (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag) (anchor : UniIndex)
    (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (notExposed : anchorNode.isExposed = false) (tagPresent : tree.indexOfTag tag = some anchor)
    (P : ByteRange → LocationTree → Prop) (initialRows : Rows P tree.locations)
    (well : tree.locations.WellFormed)
    (row : ∀ position (valid : position < tree.locations.entries.size) state,
      tree.locations.entries[position].data.perms.get anchor = some state → state.accessed = true →
      ∀ kind, state.permission.associatedAccess = some kind →
      let access := source_tree_access_at tree tree.locations.entries[position].data (some anchor)
        kind protections .SkipChildrenOfAccessed tree.locations.entries[position].range
      source_access_status access = none ∧ P tree.locations.entries[position].range (source_access_location access)) :
    let result := tree.releaseProtector tag protections
    result.status = .Released ∧ result.tree = {tree with locations := result.tree.locations} ∧
      Rows P result.tree.locations ∧ result.tree.locations.WellFormed ∧
      result.tree.locations.entries.map (·.range) = tree.locations.entries.map (·.range) ∧
      result.tree.locations.size = tree.locations.size := by
  unfold BorrowTree.releaseProtector
  rw [tagPresent]
  simp only [Id.run,bind,pure,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  name_fresh_release_scan
  let property := fun (remaining : List Nat) (state : Option BorrowTree.ProtectorReleaseResult × BorrowTree) =>
    state.1 = none ∧ ∃ map : DedupRangeMap LocationTree,
      state.2 = {tree with locations := map} ∧ map.entries.size = tree.locations.entries.size ∧
      Rows P map ∧ map.WellFormed ∧ map.entries.map (·.range) = tree.locations.entries.map (·.range) ∧
      ∀ position ∈ remaining, ∃ valid : position < tree.locations.entries.size,
        ∃ bounded : position < map.entries.size,
          map.entries[position] = tree.locations.entries[position]
  have step : ∀ position rest, position ∉ rest → ∀ state, property (position::rest) state →
      ∃ next, scan position state = .yield next ∧ property rest next := by
    intro position rest notMember state good
    rcases state with ⟨returned,current⟩
    rcases good with ⟨returnedEq,map,currentEq,sizeEq,mapRows,mapWell,mapRanges,untouched⟩
    dsimp only at returnedEq currentEq
    subst returned
    subst current
    obtain ⟨oldValid,currentValid,same⟩ := untouched position (by simp)
    have skipped : property rest (none,{tree with locations := map}) := by
      refine ⟨rfl,map,rfl,sizeEq,mapRows,mapWell,mapRanges,?_⟩
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
          have succeeded := row position oldValid before stored accessed accessKind associated
          let access := source_tree_access_at tree (tree.locations.entries[position]'oldValid).data (some anchor)
            accessKind protections .SkipChildrenOfAccessed (tree.locations.entries[position]'oldValid).range
          let mutation := map.setAtPos position (source_access_location access)
          have afterSize : mutation.state.entries.size = map.entries.size :=
            setAtPos_length map position currentValid (source_access_location access)
          have actual : scan position (none,{tree with locations := map}) =
              .yield (none,{tree with locations := mutation.state}) := by
            simp only [scan,index_exact map position currentValid,same,stored,associated,accessed,↓reduceIte,
              access_context,setAtPos_success map position currentValid,succeeded.1]
            rfl
          refine ⟨(none,{tree with locations := mutation.state}),actual,rfl,mutation.state,rfl,
            (setAtPos_length map position currentValid _).trans sizeEq,?_,?_,?_,?_⟩
          · dsimp only [mutation]
            rw [setAtPos_exact map position currentValid]
            exact replaced_rows P map position currentValid _ mapRows (by simpa only [same] using succeeded.2)
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
    refine ⟨rfl,tree.locations,rfl,rfl,initialRows,well,rfl,?_⟩
    intro position member
    have valid : position < tree.locations.entries.size := by have := List.mem_range'_1.mp member;omega
    exact ⟨valid,valid,rfl⟩
  have final := list_tail (List.range' 0 tree.locations.entries.size) scan property (none,tree) initial
    (List.nodup_range' 1) step
  obtain ⟨returnedEq,map,currentEq,sizeEq,mapRows,mapWell,mapRanges,_⟩ := final
  rw [returnedEq]
  simp only
  rw [currentEq]
  unfold BorrowTree.updateExposureForProtectorRelease
  have lookup : ({tree with locations := map} : BorrowTree).indexOfTag tag = some anchor := tagPresent
  have nodeLookup : ({tree with locations := map} : BorrowTree).nodeAt anchor = some anchorNode := anchorPresent
  simp only [lookup,nodeLookup,notExposed,Bool.not_false,↓reduceIte,Id.run,pure]
  have capacity : map.size = tree.locations.size := by
    rw [size_from_ranges,mapRanges,←size_from_ranges]
  exact ⟨True.intro,True.intro,mapRows,mapWell,mapRanges,capacity⟩
end DuplicatePrefix.S05CurrentReleaseIterator
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05CurrentReleaseIterator." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved current release iterator dependency {dependency}"
