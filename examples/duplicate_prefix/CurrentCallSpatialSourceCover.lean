import duplicate_prefix.CurrentCallSpatialRows

/-! Pure source-only cover assembly. Every retained output cell carries an
explicit original index; only cells disjoint from the request are omitted. -/
namespace DuplicatePrefix.CurrentCallSpatialSourceCover
open Miri Miri.ABI Miri.Memory Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization CurrentCallSpatialCover CandidateFreezeContentResources
set_option autoImplicit false
noncomputable section
variable {before tracker ctx mode offset length}
    (role : RoleCover before tracker ctx mode offset length)

def Active (i : Fin role.backing.cells.size) : Prop :=
  ∃ byte, Window role.backing.id offset length byte ∧
    Window role.backing.id role.backing.cells[i].offset role.backing.cells[i].length byte

def indices : List (Fin role.backing.cells.size) := by
  classical
  exact (List.ofFn (fun i : Fin role.backing.cells.size => i)).filter (fun i => decide (Active role i))

theorem mem_indices (i : Fin role.backing.cells.size) : i ∈ indices role ↔ Active role i := by
  classical
  simp [indices,List.mem_ofFn]

def activeIndices : Array {i : Fin role.backing.cells.size // Active role i} :=
  ((indices role).attachWith (Active role) (fun i member => (mem_indices role i).mp member)).toArray

theorem active_values : (activeIndices role).toList.map Subtype.val = indices role := by
  simp [activeIndices]

theorem indices_unique : (indices role).Nodup := by
  classical
  apply List.filter_sublist.nodup
  apply List.nodup_iff_eq_of_getElem_eq.mpr
  intro i j hi hj same
  simpa using congrArg Fin.val same

theorem active_unique : ((activeIndices role).toList.map Subtype.val).Nodup := by
  rw [active_values]
  exact indices_unique role

theorem active_complete (i : Fin role.backing.cells.size) (overlap : Active role i) :
    ∃ j : Fin (activeIndices role).size, ((activeIndices role)[j]).val = i := by
  have member : i ∈ (activeIndices role).toList.map Subtype.val := by
    rw [active_values]
    exact (mem_indices role i).mpr overlap
  obtain ⟨item,member,same⟩ := List.mem_map.mp member
  obtain ⟨j,valid,atIndex⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
  exact ⟨⟨j,valid⟩,(congrArg Subtype.val atIndex).trans same⟩

theorem active_injective (i j : Fin (activeIndices role).size)
    (same : ((activeIndices role)[i]).val = ((activeIndices role)[j]).val) : i=j := by
  have hi : i.val<((activeIndices role).toList.map Subtype.val).length := by simp
  have hj : j.val<((activeIndices role).toList.map Subtype.val).length := by simp
  apply Fin.ext
  apply ((active_unique role).getElem_inj (hi:=hi) (hj:=hj)).mp
  rw [List.getElem_map,List.getElem_map,Array.getElem_toList,Array.getElem_toList]
  exact same

/-- Actual operation producers supply the fixed updated completion and its
resources separately for every retained original cell. -/
structure Update (after : Before) (next : MachineHooks.BorrowState)
    (allocation : Allocation Provenance BorrowTree) (family : Family) (grant : UniIndex)
    (i : Fin role.backing.cells.size) (overlap : Active role i) where
  cell : Cell allocation.extra
  offsetEq : cell.offset = role.backing.cells[i].offset
  lengthEq : cell.length = role.backing.cells[i].length
  binding : PointerBinds allocation (family.at grant)
  issued : SpatialDelegation after next role.backing.id allocation cell.completion grant
  available : ∀ byte, Window role.backing.id offset length byte →
    Window role.backing.id role.backing.cells[i].offset role.backing.cells[i].length byte →
    byte.2 < allocation.len ∧ Embeds allocation next.global.protectedTags cell.completion grant byte.2 (demandOf mode)

variable {after next allocation family grant}
    (live : Present (ActualWorld after) role.backing.id allocation)
    (updates : ∀ i overlap, Update role after next allocation family grant i overlap)

def backing : AllocationCover after where
  id := role.backing.id
  allocation := allocation
  live := live
  cells := (activeIndices role).map (fun i => (updates i.val i.property).cell)
  disjoint := by
    intro i j different byte first second
    let oi : Fin (activeIndices role).size := ⟨i.val,by simpa only [Array.size_map] using i.isLt⟩
    let oj : Fin (activeIndices role).size := ⟨j.val,by simpa only [Array.size_map] using j.isLt⟩
    have originalDifferent : ((activeIndices role)[i]).val ≠ ((activeIndices role)[j]).val := by
      intro same
      have equal := active_injective role oi oj same
      have equalValues : i.val=j.val := congrArg (fun k : Fin (activeIndices role).size => k.val) equal
      exact different (Fin.ext equalValues)
    apply role.backing.disjoint _ _ originalDifferent byte
    · simpa only [Fin.getElem_fin,Array.getElem_map,(updates _ _).offsetEq,(updates _ _).lengthEq] using first
    · simpa only [Fin.getElem_fin,Array.getElem_map,(updates _ _).offsetEq,(updates _ _).lengthEq] using second

def context : Context after where
  allocations := #[backing role live updates]
  unique := by simp

def originalIndex (j : Fin (backing role live updates).cells.size) :
    {i : Fin role.backing.cells.size // Active role i} :=
  (activeIndices role)[j.val]'(by simpa only [backing,Array.size_map] using j.isLt)

/-- Literal original-index correspondence, including the entire chosen
completion. No completed origin is selected after an update. -/
theorem backing_cell_original (j : Fin (backing role live updates).cells.size) :
    (backing role live updates).cells[j] =
      (updates (originalIndex role live updates j).val (originalIndex role live updates j).property).cell := by
  have bound : j.val<((activeIndices role).map (fun k => (updates k.val k.property).cell)).size := by
    simpa only [backing] using j.isLt
  change ((activeIndices role).map (fun k => (updates k.val k.property).cell))[j.val]'bound = _
  rw [Array.getElem_map]
  rfl

def assemble (sameId : family.allocation = role.backing.id) :
    RoleCover after next (context role live updates) mode offset length where
  family := family
  backing := backing role live updates
  backingAt := by simp [context]
  id := sameId
  covered := by
    intro byte hit
    obtain ⟨i,cell⟩ := role.covered byte hit
    obtain ⟨j,same⟩ := active_complete role i ⟨byte,hit,cell⟩
    refine ⟨⟨j.val,by simpa only [backing,Array.size_map] using j.isLt⟩,?_⟩
    change Window role.backing.id ((activeIndices role).map (fun k => (updates k.val k.property).cell))[j].offset
      ((activeIndices role).map (fun k => (updates k.val k.property).cell))[j].length byte
    have values : ((activeIndices role)[j.val]).val.val=i.val := congrArg (fun k : Fin role.backing.cells.size => k.val) same
    simpa only [Fin.getElem_fin,Array.getElem_map,(updates _ _).offsetEq,(updates _ _).lengthEq,values] using cell
  roles := by
    intro i _
    let old := (activeIndices role)[i.val]'(by simpa only [backing,Array.size_map] using i.isLt)
    let update := updates old.val old.property
    have selected : (backing role live updates).cells[i] = update.cell := by
      have bound : i.val<((activeIndices role).map (fun k => (updates k.val k.property).cell)).size := by
        simpa only [backing] using i.isLt
      change ((activeIndices role).map (fun k => (updates k.val k.property).cell))[i.val]'bound = update.cell
      rw [Array.getElem_map]
    rw [selected]
    refine ⟨grant,update.binding,update.issued,?_⟩
    intro byte hit cell
    apply update.available byte hit
    simpa only [backing,update.offsetEq,update.lengthEq] using cell

end
end DuplicatePrefix.CurrentCallSpatialSourceCover
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallSpatialSourceCover" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved spatial source-cover dependency {dependency}"
