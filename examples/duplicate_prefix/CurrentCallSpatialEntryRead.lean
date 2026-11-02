import duplicate_prefix.CurrentCallSpatialRead
import duplicate_prefix.CurrentCallResourceFnEntry

/-! Actual FnEntry registration followed by one spatial associated Read.
The current world, backing tree, family and fixed cell maps remain unchanged
at registration. Only the actual global/frame registration is advanced. -/
namespace DuplicatePrefix.CurrentCallSpatialEntryRead
open Miri Miri.ABI Miri.Memory Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization CurrentCallSpatialCover CurrentCallSpatialRows
open GeneralBorrowFnEntryRegistration GeneralRangeMapState
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

variable {before tracker ctx mode offset length}
    (role : RoleCover before tracker ctx mode offset length)

def registeredTracker (frame : FrameState)
    (room : tracker.global.nextPointerTag.value<18446744073709551615) : MachineHooks.BorrowState :=
  {tracker with global := (registered tracker.global frame role.backing.id room).1}

private theorem registered_window_fields {data owner id start size}
    (W : UniformWindow before tracker data owner id start size mode)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (frame : FrameState) (room : tracker.global.nextPointerTag.value<18446744073709551615) :
    let current := CurrentCallResourceFnEntry.registered_window W runtime frame room
    current.allocation=W.allocation ∧ current.precise=W.precise ∧ current.pointer=W.pointer := by
  unfold CurrentCallResourceFnEntry.registered_window
  rcases GeneralBorrowFnEntryRegistrationRuntime.prepare W.allocation.extra tracker.global frame id room runtime with ⟨a,b,c,d,e,f⟩
  exact ⟨rfl,rfl,rfl⟩

def registeredRole
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (frame : FrameState) (room : tracker.global.nextPointerTag.value<18446744073709551615) :
    RoleCover before (registeredTracker role frame room) ctx mode offset length where
  family := role.family
  backing := role.backing
  backingAt := role.backingAt
  id := role.id
  covered := role.covered
  roles := by
    intro i overlap
    let old := role.roles i overlap
    let lower := max offset role.backing.cells[i].offset
    let upper := min (offset+length) (role.backing.cells[i].offset+role.backing.cells[i].length)
    let window := old.uniform role.id lower (upper-lower)
      (by
        intro byte hit
        obtain ⟨same,lo,hi⟩ := hit
        refine ⟨same,?_,?_⟩ <;> dsimp only [lower,upper] at lo hi ⊢ <;> omega)
      (by
        intro byte hit
        obtain ⟨same,lo,hi⟩ := hit
        refine ⟨same,?_,?_⟩ <;> dsimp only [lower,upper] at lo hi ⊢ <;> omega)
    let current := CurrentCallResourceFnEntry.registered_window window runtime frame room
    have currentFields := registered_window_fields window runtime frame room
    refine ⟨old.grant,old.binding,?_,?_⟩
    · have issued := current.issued
      rw [currentFields.1,currentFields.2.1,currentFields.2.2] at issued
      exact issued
    · intro byte request cell
      let atByte := CurrentCallResourceFnEntry.registered_window
        (singleByte role i overlap byte request cell) runtime frame room
      have atFields := registered_window_fields (singleByte role i overlap byte request cell) runtime frame room
      have available := atByte.window byte (singleByte_inside role i overlap byte request cell)
      rw [atFields.1,atFields.2.1,atFields.2.2] at available
      exact available
theorem grant
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (frame : FrameState) (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (i : Fin role.backing.cells.size)
    (overlap : ∃ byte,Window role.backing.id offset length byte ∧
      Window role.backing.id role.backing.cells[i].offset role.backing.cells[i].length byte) :
    ((registeredRole role runtime frame room).roles i overlap).grant=(role.roles i overlap).grant := rfl

theorem rootTag (frame : FrameState) (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (id : AllocId) : (registeredTracker role frame room).global.rootTag? id=tracker.global.rootTag? id := rfl

def read (frame : FrameState) (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (start amount : UInt64) :=
  role.backing.allocation.extra.performBorrowAccessRange (provenance role) (Size.ofBytes start) (Size.ofBytes amount)
    .Read (registeredTracker role frame room).global.protectedTags .VisitChildrenOfAccessed

def output (frame : FrameState) (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (start amount : UInt64) : GeneralBorrowForestFnEntry.Output :=
  ⟨(registered tracker.global frame role.backing.id room).1,
    (registered tracker.global frame role.backing.id room).2,tracker.global.nextPointerTag,
    read role frame room start amount,
    (read role frame room start amount).tree.newChild (Size.ofBytes start) (provenance role) tracker.global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes amount) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true⟩

/-- This normalizes the actual operation record, without asserting that its
child constructor has succeeded. The constructor consumer proves that next. -/
theorem literal_operation (frame : FrameState) (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (start amount : UInt64) :
    CandidateCurrentFnEntryRaw.operation role.backing.allocation.extra tracker.global frame role.backing.id
      role.family.value.provenance start amount=.ok (output role frame room start amount) := by
  cases value : role.family.value.provenance with
  | concrete id tag =>
    simp only [output,read,registeredTracker,provenance,value,CandidateCurrentFnEntryRaw.operation,GeneralBorrowForestFnEntry.operation,
      TypedRetagEmpty.allocate_tag tracker.global room,Except.bind,Except.pure,bind,pure]
    rfl
  | wildcard =>
    simp only [output,read,registeredTracker,provenance,value,CandidateCurrentFnEntryRaw.operation,GeneralBorrowRawWildcardFnEntryRuntime.operation,
      TypedRetagEmpty.allocate_tag tracker.global room,Except.bind,Except.pure,bind,pure]
    rfl

/-- All old cell authorities are registered on the SAME fixed cover, then
ONE actual spatial ranged Read retains every saved-row/cell certificate. -/
theorem invoke
    (exclusive : demandOf mode=.exclusive)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup)
    (short : role.backing.allocation.extra.nodes.size<65536)
    (frame : FrameState) (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
    (nonzero : amount≠0)
    (bounds : start.toNat+amount.toNat≤role.backing.allocation.extra.locations.size.bytes.toNat) :
    let current := registeredRole role runtime frame room
    let accessed := read role frame room start amount
    GeneralBorrowConcreteRangeInvariant.Contract role.backing.allocation.extra (fun _ => True)
      (fun location => GeneralBorrowExposureCardinality.LocationCoherent role.backing.allocation.extra location
          (registeredTracker role frame room).global.protectedTags ∧
        GeneralBorrowLocationSifaConsistency.Profile role.backing.allocation.extra location
          (registeredTracker role frame room).global.protectedTags ∧
        GeneralBorrowSnapshotReadRuntime.GlobalPossible role.backing.allocation.extra location)
      (Frame current) start (start+amount) accessed ∧
    DuplicatePrefixBorrowContract.RuntimeFacts accessed.tree (registeredTracker role frame room).global ∧
    ∀ i : Fin role.backing.cells.size,ParentInterpretation accessed.tree role.backing.cells[i].completion := by
  have registeredRuntime := (GeneralBorrowFnEntryRegistrationRuntime.prepare role.backing.allocation.extra tracker.global
    frame role.backing.id room runtime).2.2.2.1
  exact CurrentCallSpatialRead.access_runtime (registeredRole role runtime frame room) exclusive registeredRuntime
    distinct short start amount startEq amountEq nonzero bounds .VisitChildrenOfAccessed

end
end DuplicatePrefix.CurrentCallSpatialEntryRead
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallSpatialEntryRead.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved spatial entry Read dependency {dependency}"
