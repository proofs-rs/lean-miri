import duplicate_prefix.CurrentCallSpatialCover
import duplicate_prefix.CurrentCallResourceRead
import duplicate_prefix.GeneralBorrowConcreteRangeEntry

/-! Shared saved-original-row interfaces for spatial range producers. These
predicates do not perform an access or split interpreter rows at proof cells. -/
namespace DuplicatePrefix.CurrentCallSpatialRows
open Miri Miri.ABI Miri.Memory Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization CurrentCallSpatialCover CandidateFreezeContentResources
open GeneralRangeMapOrigins GeneralBorrowExposedConditionalRangeFrames
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
variable {before tracker ctx mode offset length}
    (role : RoleCover before tracker ctx mode offset length)

def provenance : ProvenanceExtra := match role.family.value.provenance with
  | .concrete _ tag => .concrete tag
  | .wildcard => .wildcard

def source : Option UniIndex := match role.family.value.provenance with
  | .concrete _ tag => role.backing.allocation.extra.indexOfTag tag
  | .wildcard => none

theorem source_at (i : Fin role.backing.cells.size)
    (overlap : ∃ byte, Window role.backing.id offset length byte ∧
      Window role.backing.id role.backing.cells[i].offset role.backing.cells[i].length byte) :
    match role.family.value.provenance with
    | .concrete _ _ => source role = some (role.roles i overlap).grant
    | .wildcard => source role = none := by
  obtain ⟨node,_,mapping,binding⟩ := (role.roles i overlap).binding
  cases value : role.family.value.provenance with
  | wildcard => simp [source,value]
  | concrete id tag =>
    change (match role.family.value.provenance with
      | .concrete id tag => id = role.family.allocation ∧ tag = node.tag
      | .wildcard => node.isExposed = true) at binding
    rw [value] at binding
    simpa only [source,value,BorrowTree.indexOfTag,binding.2,Family.at] using mapping

theorem resolved (positive : 0 < length) :
    match provenance role with
    | .concrete tag => ∃ anchor, role.backing.allocation.extra.indexOfTag tag = some anchor ∧ source role = some anchor
    | .wildcard => source role = none := by
  have request : Window role.backing.id offset length (role.backing.id,offset) := ⟨rfl,by omega,by omega⟩
  obtain ⟨i,cell⟩ := role.covered _ request
  have overlap : ∃ byte, Window role.backing.id offset length byte ∧
      Window role.backing.id role.backing.cells[i].offset role.backing.cells[i].length byte :=
    ⟨(role.backing.id,offset),request,cell⟩
  have sourceAt := source_at role i overlap
  cases value : role.family.value.provenance with
  | wildcard => simp only [provenance,source,value]
  | concrete id tag =>
    simp only [value] at sourceAt
    simp only [provenance,value]
    exact ⟨(role.roles i overlap).grant,by simpa only [source,value] using sourceAt,sourceAt⟩

def Saved (old : LocationTree) : Prop :=
  ∃ segment ∈ role.backing.allocation.extra.locations.entries.toList,
    segment.data = old ∧ ∃ byte, Window role.backing.id offset length byte ∧
      segment.range.start.toNat ≤ byte.2 ∧ byte.2 < segment.range.stop.toNat

/-- All matching ORIGINAL rows and all intersecting cells are retained. The
old-row equality is saved through actual preparation, callbacks, and splits. -/
def Frame (old next : LocationTree) : Prop :=
  ∀ segment ∈ role.backing.allocation.extra.locations.entries.toList, segment.data = old →
    ∀ (i : Fin role.backing.cells.size)
      (overlap : ∃ byte, Window role.backing.id offset length byte ∧
        Window role.backing.id role.backing.cells[i].offset role.backing.cells[i].length byte),
    (∃ byte, Window role.backing.id offset length byte ∧
      Window role.backing.id role.backing.cells[i].offset role.backing.cells[i].length byte ∧
      segment.range.start.toNat ≤ byte.2 ∧ byte.2 < segment.range.stop.toNat) →
    S05CompletedAncestryReadMutable.Authority role.backing.allocation.extra role.backing.cells[i].completion
      tracker.global.protectedTags (role.roles i overlap).grant next

def singleByte (i : Fin role.backing.cells.size)
    (overlap : ∃ byte, Window role.backing.id offset length byte ∧
      Window role.backing.id role.backing.cells[i].offset role.backing.cells[i].length byte)
    (byte : AllocId × Nat) (request : Window role.backing.id offset length byte)
    (cell : Window role.backing.id role.backing.cells[i].offset role.backing.cells[i].length byte) :
    UniformWindow before tracker (role.roles i overlap).identities 0 role.backing.id byte.2 1 mode :=
  (role.roles i overlap).uniform role.id byte.2 1
    (by intro other hit; obtain ⟨id,lo,hi⟩ := hit; exact ⟨id,by have := request.2.1; omega,by have := request.2.2; omega⟩)
    (by intro other hit; obtain ⟨id,lo,hi⟩ := hit; exact ⟨id,by have := cell.2.1; omega,by have := cell.2.2; omega⟩)

theorem singleByte_inside (i : Fin role.backing.cells.size)
    (overlap : ∃ byte, Window role.backing.id offset length byte ∧
      Window role.backing.id role.backing.cells[i].offset role.backing.cells[i].length byte)
    (byte : AllocId × Nat) (request : Window role.backing.id offset length byte)
    (cell : Window role.backing.id role.backing.cells[i].offset role.backing.cells[i].length byte) :
    Window role.backing.id byte.2 1 byte := ⟨request.1,by omega,by omega⟩

theorem initial_authority (exclusive : demandOf mode = .exclusive)
    (profiles : ∀ segment ∈ role.backing.allocation.extra.locations.entries.toList,
      GeneralBorrowLocationSifaConsistency.Profile role.backing.allocation.extra segment.data tracker.global.protectedTags)
    (possibles : ∀ segment ∈ role.backing.allocation.extra.locations.entries.toList,
      GeneralBorrowSnapshotReadRuntime.GlobalPossible role.backing.allocation.extra segment.data) :
    ∀ old, Frame role old old := by
  intro old segment member same i overlap hit
  obtain ⟨byte,request,cell,lower,upper⟩ := hit
  have rights := CurrentCallResourceAccess.row_authority
    (singleByte role i overlap byte request cell) exclusive byte
    (singleByte_inside role i overlap byte request cell) segment member lower upper
    (profiles segment member) (possibles segment member)
  change S05CompletedAncestryReadMutable.Authority role.backing.allocation.extra role.backing.cells[i].completion
    tracker.global.protectedTags (role.roles i overlap).grant segment.data at rights
  rw [same] at rights
  exact rights

theorem saved_owned (lower upper : UInt64)
    (lowerEq : lower.toNat = offset) (upperEq : upper.toNat = offset + length)
    (well : role.backing.allocation.extra.locations.WellFormed) :
    OwnedOn (Saved role) lower upper role.backing.allocation.extra.locations := by
  intro position valid positive starts stops
  let segment := role.backing.allocation.extra.locations.entries[position]
  have member : segment ∈ role.backing.allocation.extra.locations.entries.toList :=
    Array.mem_toList_iff.mpr (Array.getElem_mem valid)
  refine ⟨segment,member,rfl,(role.backing.id,max offset segment.range.start.toNat),?_,?_,?_⟩
  · exact ⟨rfl,by omega,by dsimp only [segment] at *; omega⟩
  · omega
  · have nonempty := (GeneralRangeMapGeometry.facts role.backing.allocation.extra.locations
        well (by omega)).2.1 position valid
    dsimp only [segment]
    omega

theorem recover (afterMap : DedupRangeMap LocationTree)
    (origins : Origins (Frame role) role.backing.allocation.extra.locations afterMap)
    (point : UInt64) (next : LocationTree) (atPoint : ValueAt afterMap point next)
    (request : Window role.backing.id offset length (role.backing.id,point.toNat))
    (i : Fin role.backing.cells.size)
    (overlap : ∃ byte, Window role.backing.id offset length byte ∧
      Window role.backing.id role.backing.cells[i].offset role.backing.cells[i].length byte)
    (cell : Window role.backing.id role.backing.cells[i].offset role.backing.cells[i].length
      (role.backing.id,point.toNat)) :
    S05CompletedAncestryReadMutable.Authority role.backing.allocation.extra role.backing.cells[i].completion
      tracker.global.protectedTags (role.roles i overlap).grant next := by
  obtain ⟨old,⟨position,valid,lower,upper,same⟩,frame⟩ := origins point next atPoint
  exact frame _ (Array.mem_toList_iff.mpr (Array.getElem_mem valid)) same i overlap
    ⟨(role.backing.id,point.toNat),request,cell,lower,upper⟩

end
end DuplicatePrefix.CurrentCallSpatialRows
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallSpatialRows" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved spatial-row dependency {dependency}"
