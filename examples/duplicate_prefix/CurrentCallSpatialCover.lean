import duplicate_prefix.CurrentCallResourceNormalization

/-! Bounded common spatial origins. Cells describe proof footprints only; they
do not change the interpreter's location partition or its actual rows. -/
namespace DuplicatePrefix.CurrentCallSpatialCover
open Miri Miri.ABI Miri.Memory Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization CandidateFreezeContentResources
set_option autoImplicit false
noncomputable section

structure Cell (tree : BorrowTree) where
  offset : Nat
  length : Nat
  completion : Completion
  parents : ParentInterpretation tree completion

structure AllocationCover (before : Before) where
  id : AllocId
  allocation : Allocation Provenance BorrowTree
  live : Present (ActualWorld before) id allocation
  cells : Array (Cell allocation.extra)
  disjoint : ∀ (i j : Fin cells.size), i ≠ j → ∀ byte,
    Window id cells[i].offset cells[i].length byte →
    Window id cells[j].offset cells[j].length byte → False

/-- Source and return roles use this same fixed cover assignment. -/
structure Context (before : Before) where
  allocations : Array (AllocationCover before)
  unique : (allocations.toList.map AllocationCover.id).Nodup

/-- Same-allocation roles cannot silently choose different cell assignments. -/
theorem Context.same_backing {before} (ctx : Context before)
    {first second : AllocationCover before}
    (firstAt : first ∈ ctx.allocations.toList) (secondAt : second ∈ ctx.allocations.toList)
    (same : first.id = second.id) : first = second := by
  apply CandidateCurrentUniformOwnerWindow.same_id
    (ctx.allocations.toList.map (fun backing => (backing.id,backing)))
    (by simpa only [List.map_map,Function.comp_def] using ctx.unique) first.id first second
  · exact List.mem_map.mpr ⟨first,firstAt,rfl⟩
  · exact List.mem_map.mpr ⟨second,secondAt,by simp only [same]⟩

/-- A family label carries actual pointer bits; grants belong to cells. -/
structure Family where
  slot : Nat
  allocation : AllocId
  value : Pointer Provenance

def Family.at (family : Family) (grant : UniIndex) : PointerInstance :=
  ⟨family.allocation, family.value, grant⟩

structure CellRole (before : Before) (tracker : MachineHooks.BorrowState)
    (backing : AllocationCover before) (cell : Cell backing.allocation.extra)
    (family : Family) (mode : Mode) (offset length : Nat) where
  grant : UniIndex
  binding : PointerBinds backing.allocation (family.at grant)
  issued : SpatialDelegation before tracker backing.id backing.allocation cell.completion grant
  available : ∀ byte, Window backing.id offset length byte →
    Window backing.id cell.offset cell.length byte → byte.2 < backing.allocation.len ∧
    Embeds backing.allocation tracker.global.protectedTags cell.completion grant byte.2 (demandOf mode)

/-- The request may cross several cells. All overlapping certificates coexist;
no callback, copy, or byte selects a fresh cover. -/
structure RoleCover (before : Before) (tracker : MachineHooks.BorrowState)
    (ctx : Context before) (mode : Mode) (offset length : Nat) where
  family : Family
  backing : AllocationCover before
  backingAt : backing ∈ ctx.allocations.toList
  id : family.allocation = backing.id
  covered : ∀ byte, Window backing.id offset length byte →
    ∃ i : Fin backing.cells.size, Window backing.id backing.cells[i].offset backing.cells[i].length byte
  roles : ∀ i : Fin backing.cells.size,
    (∃ byte, Window backing.id offset length byte ∧
      Window backing.id backing.cells[i].offset backing.cells[i].length byte) →
    CellRole before tracker backing backing.cells[i] family mode offset length

/-- Whole-role traversal of all intersecting proof cells, with no saved-row
range restriction. Actual saved-row splitting uses SpatialRows.Frame/recover. -/
def RoleCover.Origins {before tracker ctx mode offset length}
    (role : RoleCover before tracker ctx mode offset length)
    (P : Cell role.backing.allocation.extra → UniIndex → Prop) : Prop :=
  ∀ (i : Fin role.backing.cells.size)
    (overlap : ∃ byte, Window role.backing.id offset length byte ∧
      Window role.backing.id role.backing.cells[i].offset role.backing.cells[i].length byte),
    P role.backing.cells[i] (role.roles i overlap).grant

theorem RoleCover.origins_map {before tracker ctx mode offset length}
    (role : RoleCover before tracker ctx mode offset length)
    {P Q : Cell role.backing.allocation.extra → UniIndex → Prop}
    (saved : role.Origins P) (frame : ∀ cell grant, P cell grant → Q cell grant) :
    role.Origins Q := fun i overlap => frame _ _ (saved i overlap)

/-- Technical indices for reusing local UniformWindow row lemmas. This is not
an actual new family/copy and has no CurrentDenotation claim. -/
def CellRole.identities {before tracker backing cell family mode offset length}
    (role : CellRole before tracker backing cell family mode offset length) : Identities :=
  ⟨⟨#[(backing.id,⟨cell.completion,#[]⟩)],#[family.at role.grant],#[⟨0,none,0⟩],
      fun _ _ => none⟩,#[⟨0,family.value⟩],#[]⟩

/-- Only a subwindow contained in BOTH the request and the proof cell is
projected. Actual pointer bits and actual allocation are unchanged. -/
def CellRole.uniform {before tracker backing cell family mode offset length}
    (role : CellRole before tracker backing cell family mode offset length)
    (sameId : family.allocation = backing.id) (start size : Nat)
    (request : ∀ byte, Window backing.id start size byte → Window backing.id offset length byte)
    (inside : ∀ byte, Window backing.id start size byte → Window backing.id cell.offset cell.length byte) :
    UniformWindow before tracker role.identities 0 backing.id start size mode where
  loan := ⟨0,none,0⟩
  pointer := family.at role.grant
  allocation := backing.allocation
  precise := ⟨cell.completion,#[]⟩
  loanAt := rfl
  pointerAt := rfl
  pointerId := sameId
  present := backing.live
  preciseAt := by simp [identities]
  binding := role.binding
  issued := role.issued
  parents := cell.parents
  window := fun byte hit => role.available byte (request byte hit) (inside byte hit)

theorem concrete_grant_eq {allocation : Allocation Provenance BorrowTree}
    {first second : PointerInstance} {id : AllocId} {tag : BorTag}
    (firstBinds : PointerBinds allocation first) (secondBinds : PointerBinds allocation second)
    (firstValue : first.value.provenance = .concrete id tag)
    (secondValue : second.value.provenance = .concrete id tag) : first.grant = second.grant := by
  obtain ⟨a,_,aMap,aValue⟩ := firstBinds
  obtain ⟨b,_,bMap,bValue⟩ := secondBinds
  rw [firstValue] at aValue
  rw [secondValue] at bValue
  rw [←aValue.2] at aMap
  rw [←bValue.2] at bMap
  exact Option.some.inj (aMap.symm.trans bMap)

def uniformBacking {before tracker data owner id offset length mode}
    (window : UniformWindow before tracker data owner id offset length mode) : AllocationCover before where
  id := id
  allocation := window.allocation
  live := window.present
  cells := #[⟨offset,length,window.precise.completion,window.parents⟩]
  disjoint := by
    intro i j different
    apply False.elim
    apply different
    apply Fin.ext
    have hi : i.val < 1 := i.isLt
    have hj : j.val < 1 := j.isLt
    omega

def uniformContext {before tracker data owner id offset length mode}
    (window : UniformWindow before tracker data owner id offset length mode) : Context before where
  allocations := #[uniformBacking window]
  unique := by simp

/-- The old uniform-origin interface is the one-cell specialization. This
direction does not assert ordinary callers admit a uniform origin. -/
def ofUniform {before tracker data owner id offset length mode}
    (window : UniformWindow before tracker data owner id offset length mode) :
    RoleCover before tracker (uniformContext window) mode offset length where
  family := ⟨window.loan.pointer,id,window.pointer.value⟩
  backing := uniformBacking window
  backingAt := by simp [uniformContext]
  id := rfl
  covered := by
    intro byte inside
    exact ⟨⟨0,by simp [uniformBacking]⟩,inside⟩
  roles := by
    intro i _
    have zero : i.val = 0 := by have := i.isLt; simp [uniformBacking] at this; omega
    have eq : i = ⟨0,by simp [uniformBacking]⟩ := Fin.ext zero
    subst i
    refine ⟨window.pointer.grant,?_,window.issued,?_⟩
    · have same : (Family.at ⟨window.loan.pointer,id,window.pointer.value⟩ window.pointer.grant) = window.pointer := by
        change (⟨id,window.pointer.value,window.pointer.grant⟩ : PointerInstance) = window.pointer
        exact congrArg (fun a => (⟨a,window.pointer.value,window.pointer.grant⟩ : PointerInstance)) window.pointerId.symm
      rw [same]
      exact window.binding
    · intro byte inside _
      exact window.window byte inside

end
end DuplicatePrefix.CurrentCallSpatialCover
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallSpatialCover" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved spatial-cover dependency {dependency}"
