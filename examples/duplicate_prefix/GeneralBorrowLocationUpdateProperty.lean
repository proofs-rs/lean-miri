import duplicate_prefix.GeneralBorrowExposureMapFrame
namespace DuplicatePrefix.GeneralBorrowLocationUpdateProperty
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposureRelease DuplicatePrefix.GeneralBorrowExposureMapFrame
open DuplicatePrefix.GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Lift a per-location semantic transformation through the actual source
updateEveryLocation loop. Distinct real positions ensure each old invariant is
consumed exactly once, including arbitrary partitioned range maps. -/
theorem every (tree : BorrowTree) (update : LocationTree → LocationTree × Except BorrowTree.TreeMutationError Unit)
    (before after : LocationTree → Prop) (initial : Every before tree.locations)
    (step : ∀ location,before location → (update location).2 = .ok () ∧ after (update location).1) :
    (source_location_update tree update).outcome = .ok () ∧
      Every after (source_location_update tree update).tree.locations := by
  unfold_source_update_locations
  simp only [Id.run,bind,pure,ForIn.forIn,Std.Legacy.Range.forIn'_eq_forIn'_range',Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  name_release_exposure_scan
  let positions := List.range' 0 tree.locations.entries.size
  let invariant := fun todo : List Nat => fun current : BorrowTree =>
    current.locations.entries.size = tree.locations.entries.size ∧
      ∀ query (valid : query < current.locations.entries.size),
        if query ∈ todo then before current.locations.entries[query].data else after current.locations.entries[query].data
  have go : ∀ todo (included : ∀ position ∈ todo,position ∈ positions) (current : BorrowTree),
      todo.Nodup → invariant todo current →
      let result := forIn' todo (none,current) (fun position member => scan position (included position member))
      result.1 = none ∧ Every after result.2.locations := by
    intro todo
    induction todo with
    | nil =>
      intro included current unique good
      simp only [List.forIn'_nil,pure]
      refine ⟨trivial,?_⟩
      intro query valid
      simpa only [List.not_mem_nil,ite_false] using good.2 query valid
    | cons position rest ih =>
      intro included current unique good
      have valid : position < current.locations.entries.size := by
        have member := included position (by simp)
        have bound : position < tree.locations.entries.size := by simpa only [positions,List.mem_range'_1,Nat.zero_le,true_and,Nat.zero_add] using member
        rw [good.1];exact bound
      have oldGood : before current.locations.entries[position].data := by
        simpa only [List.mem_cons_self,ite_true] using good.2 position valid
      have updateGood := step current.locations.entries[position].data oldGood
      let nextLocation := (update current.locations.entries[position].data).1
      let nextTree := {current with locations := (current.locations.setAtPos position nextLocation).state}
      have nextSize : nextTree.locations.entries.size = current.locations.entries.size := setAtPos_length current.locations position valid nextLocation
      have actual : scan position (included position (by simp)) (none,current) = .yield (none,nextTree) := by
        simp only [scan,index_exact current.locations position valid,updateGood.1,setAtPos_success current.locations position valid]
        rfl
      have nextGood : invariant rest nextTree := by
        refine ⟨nextSize.trans good.1,?_⟩
        intro query nextValid
        have oldValid : query < current.locations.entries.size := by rw [←nextSize];exact nextValid
        have dataEq : nextTree.locations.entries[query].data =
            if position = query then nextLocation else current.locations.entries[query].data := by
          simp only [nextTree,setAtPos_exact current.locations position valid,replaced,Array.getElem_set]
          split <;> rfl
        rw [dataEq]
        by_cases same : position = query
        · subst query
          have absent : position ∉ rest := (List.nodup_cons.mp unique).1
          simpa only [absent,ite_false,ite_true] using updateGood.2
        · have original := good.2 query oldValid
          have different : query ≠ position := Ne.symm same
          simpa only [List.mem_cons,different,false_or,ite_eq_right same] using original
      rw [List.forIn'_cons,actual]
      simp only [bind]
      exact ih (fun other member => included other (by simp [member])) nextTree (List.nodup_cons.mp unique).2 nextGood
  have good : invariant positions tree := by
    refine ⟨rfl,?_⟩
    intro query valid
    have member : query ∈ positions := by simp only [positions,List.mem_range'_1];omega
    rw [ite_eq_left member]
    exact initial query valid
  have result := go positions (fun _ member => member) tree List.nodup_range' good
  rw [result.1]
  exact ⟨rfl,result.2⟩
end DuplicatePrefix.GeneralBorrowLocationUpdateProperty
