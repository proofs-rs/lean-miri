import duplicate_prefix.GenericFunctionEntryNumerics

namespace DuplicatePrefix.GenericFunctionTagFormation
open Miri Miri.Interpreter Miri.Memory Miri.TreeBorrows
open GenericFunctionEntryState
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

set_option autoImplicit false in
/-- A source-data high-water invariant, explicitly assumed here. This module
neither classifies valid Rust histories nor derives this invariant from them. -/
structure Below (tree : BorrowTree) (protections : ProtectedTags) (counter : BorTag) : Prop where
  mapping : ∀ row ∈ tree.tagMapping.mapping, row.1.value.toNat < counter.value.toNat
  nodes : ∀ row ∈ tree.nodes.entries, row.2.tag.value.toNat < counter.value.toNat
  protectors : ∀ row ∈ protections.entries, row.1.value.toNat < counter.value.toNat

set_option autoImplicit false in
/-- Freshness bounds for exactly the six real counter allocations: ROOT
FnEntry, return slot, shared expression, len FnEntry, mutable expression and
as_mut_ptr FnEntry. Registration/endCall do not alter their counter values. -/
structure Chain (tracker : MachineHooks.BorrowState) where
  fresh : tracker.global.nextPointerTag.value < 18446744073709551615
  slotFresh : (next tracker fresh).global.nextPointerTag.value < 18446744073709551615
  exprFresh : (held tracker fresh slotFresh).global.nextPointerTag.value < 18446744073709551615
  helperFresh : (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) exprFresh).global.nextPointerTag.value < 18446744073709551615
  mutFresh : (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) exprFresh) helperFresh).global.nextPointerTag.value < 18446744073709551615
  mutEntryFresh : (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker (held tracker fresh slotFresh) exprFresh) helperFresh) mutFresh).global.nextPointerTag.value < 18446744073709551615

set_option autoImplicit false in
/-- One numeric capacity condition derives every per-allocation overflow bound. -/
theorem from_room (tracker : MachineHooks.BorrowState)
    (room : tracker.global.nextPointerTag.value.toNat+6 ≤ 18446744073709551615) : Chain tracker := by
  have fresh : tracker.global.nextPointerTag.value < 18446744073709551615 :=
    by
      apply UInt64.lt_iff_toNat_lt.mpr
      have h : tracker.global.nextPointerTag.value.toNat < 18446744073709551615 := by omega
      simpa using h
  have first := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag fresh
  change (next tracker fresh).global.nextPointerTag.value.toNat = tracker.global.nextPointerTag.value.toNat+1 at first
  have slotFresh : (next tracker fresh).global.nextPointerTag.value < 18446744073709551615 :=
    by
      apply UInt64.lt_iff_toNat_lt.mpr
      have h : (next tracker fresh).global.nextPointerTag.value.toNat < 18446744073709551615 := by omega
      simpa using h
  have second := GenericFunctionEntryNumerics.successor_value (next tracker fresh).global.nextPointerTag slotFresh
  change (held tracker fresh slotFresh).global.nextPointerTag.value.toNat = (next tracker fresh).global.nextPointerTag.value.toNat+1 at second
  let expr := held tracker fresh slotFresh
  change expr.global.nextPointerTag.value.toNat = (next tracker fresh).global.nextPointerTag.value.toNat+1 at second
  have exprFresh : expr.global.nextPointerTag.value < 18446744073709551615 :=
    by
      apply UInt64.lt_iff_toNat_lt.mpr
      have h : expr.global.nextPointerTag.value.toNat < 18446744073709551615 := by omega
      simpa using h
  have third := GenericFunctionEntryNumerics.successor_value expr.global.nextPointerTag exprFresh
  let helper := ReferenceBorrowDriver.allocatedTracker expr exprFresh
  change helper.global.nextPointerTag.value.toNat = expr.global.nextPointerTag.value.toNat+1 at third
  have helperFresh : helper.global.nextPointerTag.value < 18446744073709551615 :=
    by
      apply UInt64.lt_iff_toNat_lt.mpr
      have h : helper.global.nextPointerTag.value.toNat < 18446744073709551615 := by omega
      simpa using h
  have fourth := GenericFunctionEntryNumerics.successor_value helper.global.nextPointerTag helperFresh
  let mutable := ReferenceBorrowDriver.allocatedTracker helper helperFresh
  change mutable.global.nextPointerTag.value.toNat = helper.global.nextPointerTag.value.toNat+1 at fourth
  have mutFresh : mutable.global.nextPointerTag.value < 18446744073709551615 :=
    by
      apply UInt64.lt_iff_toNat_lt.mpr
      have h : mutable.global.nextPointerTag.value.toNat < 18446744073709551615 := by omega
      simpa using h
  have fifth := GenericFunctionEntryNumerics.successor_value mutable.global.nextPointerTag mutFresh
  let entry := ReferenceBorrowDriver.allocatedTracker mutable mutFresh
  change entry.global.nextPointerTag.value.toNat = mutable.global.nextPointerTag.value.toNat+1 at fifth
  have mutEntryFresh : entry.global.nextPointerTag.value < 18446744073709551615 :=
    by
      apply UInt64.lt_iff_toNat_lt.mpr
      have h : entry.global.nextPointerTag.value.toNat < 18446744073709551615 := by omega
      simpa using h
  exact ⟨fresh,slotFresh,exprFresh,helperFresh,mutFresh,mutEntryFresh⟩

abbrev expr (tracker : MachineHooks.BorrowState) (r : Chain tracker) := held tracker r.fresh r.slotFresh
abbrev helper (tracker : MachineHooks.BorrowState) (r : Chain tracker) := ReferenceBorrowDriver.allocatedTracker (expr tracker r) r.exprFresh
abbrev mutable (tracker : MachineHooks.BorrowState) (r : Chain tracker) := ReferenceBorrowDriver.allocatedTracker (helper tracker r) r.helperFresh
abbrev entry (tracker : MachineHooks.BorrowState) (r : Chain tracker) := ReferenceBorrowDriver.allocatedTracker (mutable tracker r) r.mutFresh

def future (tracker : MachineHooks.BorrowState) (r : Chain tracker) (index : Fin 4) : BorTag :=
  if index.val=0 then (expr tracker r).global.nextPointerTag
  else if index.val=1 then (helper tracker r).global.nextPointerTag
  else if index.val=2 then (mutable tracker r).global.nextPointerTag
  else (entry tracker r).global.nextPointerTag

set_option autoImplicit false in
theorem future_value (tracker : MachineHooks.BorrowState) (r : Chain tracker) (index : Fin 4) :
    (future tracker r index).value.toNat = tracker.global.nextPointerTag.value.toNat+(index.val+2) := by
  have first := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag r.fresh
  have second := GenericFunctionEntryNumerics.successor_value (next tracker r.fresh).global.nextPointerTag r.slotFresh
  have third := GenericFunctionEntryNumerics.successor_value (expr tracker r).global.nextPointerTag r.exprFresh
  have fourth := GenericFunctionEntryNumerics.successor_value (helper tracker r).global.nextPointerTag r.helperFresh
  have fifth := GenericFunctionEntryNumerics.successor_value (mutable tracker r).global.nextPointerTag r.mutFresh
  change (next tracker r.fresh).global.nextPointerTag.value.toNat = tracker.global.nextPointerTag.value.toNat+1 at first
  change (expr tracker r).global.nextPointerTag.value.toNat = (next tracker r.fresh).global.nextPointerTag.value.toNat+1 at second
  change (helper tracker r).global.nextPointerTag.value.toNat = (expr tracker r).global.nextPointerTag.value.toNat+1 at third
  change (mutable tracker r).global.nextPointerTag.value.toNat = (helper tracker r).global.nextPointerTag.value.toNat+1 at fourth
  change (entry tracker r).global.nextPointerTag.value.toNat = (mutable tracker r).global.nextPointerTag.value.toNat+1 at fifth
  have cases : index.val=0 ∨ index.val=1 ∨ index.val=2 ∨ index.val=3 := by have h:=index.isLt;omega
  rcases cases with h | h | h | h
  · simp only [future,h,ite_true];omega
  · simp only [future,h,Nat.reduceEqDiff,ite_false,ite_true];omega
  · simp only [future,h,Nat.reduceEqDiff,ite_false,ite_true];omega
  · simp only [future,h,Nat.reduceEqDiff,ite_false,ite_true];omega

set_option autoImplicit false in
theorem fresh_above (tree : BorrowTree) (protections : ProtectedTags) (counter tag : BorTag)
    (below : Below tree protections counter) (above : counter.value.toNat ≤ tag.value.toNat) :
    GeneralBorrowTagMap.Fresh tree.tagMapping tag ∧ GeneralBorrowProtector.Fresh tree tag ∧ protections.contains tag=false := by
  have mapFresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag := by
    intro row member same
    have lower := below.mapping row member
    have eq := congrArg (fun tag : BorTag => tag.value.toNat) same
    omega
  have nodeFresh : GeneralBorrowProtector.Fresh tree tag := by
    intro row member same
    have lower := below.nodes row member
    have eq := congrArg (fun tag : BorTag => tag.value.toNat) same
    omega
  have absent : protections.entries.find? (fun row => row.1 == tag) = none := by
    apply Array.find?_eq_none.mpr
    intro row member
    have lower := below.protectors row member
    simp only [beq_iff_eq]
    intro same
    have eq := congrArg (fun tag : BorTag => tag.value.toNat) same
    omega
  exact ⟨mapFresh,nodeFresh,by simp only [ProtectedTags.contains,ProtectedTags.get,absent,Option.map_none,Option.isSome_none]⟩

set_option autoImplicit false in
/-- All four initial future resources, plus absence after the two actual ROOT
protector registrations, follow from the single high-water invariant. -/
theorem formed (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (r : Chain tracker)
    (below : Below tree tracker.global.protectedTags tracker.global.nextPointerTag) :
    (∀ index : Fin 4, GeneralBorrowTagMap.Fresh tree.tagMapping (future tracker r index) ∧
      GeneralBorrowProtector.Fresh tree (future tracker r index) ∧
      tracker.global.protectedTags.contains (future tracker r index)=false ∧
      (expr tracker r).global.protectedTags.contains (future tracker r index)=false) ∧
    Function.Injective (future tracker r) := by
  have fields (index : Fin 4) := fresh_above tree tracker.global.protectedTags tracker.global.nextPointerTag
    (future tracker r index) below (by have h:=future_value tracker r index;omega)
  constructor
  · intro index
    have initial := fields index
    have current : future tracker r index ≠ tracker.global.nextPointerTag := by
      intro same
      have eq := congrArg (fun tag : BorTag => tag.value.toNat) same
      have h := future_value tracker r index
      omega
    have successor : future tracker r index ≠ (next tracker r.fresh).global.nextPointerTag := by
      intro same
      have eq := congrArg (fun tag : BorTag => tag.value.toNat) same
      have h := future_value tracker r index
      have first := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag r.fresh
      change (next tracker r.fresh).global.nextPointerTag.value.toNat=tracker.global.nextPointerTag.value.toNat+1 at first
      omega
    exact ⟨initial.1,initial.2.1,initial.2.2,buffer_root_free tracker r.fresh r.slotFresh _ current successor initial.2.2⟩
  · intro left right same
    have eq := congrArg (fun tag : BorTag => tag.value.toNat) same
    have l := future_value tracker r left
    have rr := future_value tracker r right
    exact Fin.ext (by omega)

set_option autoImplicit false in
theorem slot_root_future (tracker : MachineHooks.BorrowState) (r : Chain tracker) (slotRoot : BorTag)
    (old : slotRoot.value.toNat < tracker.global.nextPointerTag.value.toNat) :
    ∀ index : Fin 4, future tracker r index ≠ slotRoot := by
  intro index same
  have eq := congrArg (fun tag : BorTag => tag.value.toNat) same
  have value := future_value tracker r index
  omega

/-- Actual GlobalState counter operations, with no retag/body replacement. -/
def allocate_six (global : GlobalState) : Except GlobalStateError (GlobalState × Array BorTag) := do
  let (g1,t0) ← global.newPointerTag
  let (g2,t1) ← g1.newPointerTag
  let (g3,t2) ← g2.newPointerTag
  let (g4,t3) ← g3.newPointerTag
  let (g5,t4) ← g4.newPointerTag
  let (g6,t5) ← g5.newPointerTag
  pure (g6,#[t0,t1,t2,t3,t4,t5])

set_option autoImplicit false in
/-- The six allocation effects themselves succeed, with the same generated tags
as the counter projections used above. Intervening protector changes are outside
this pure allocation projection; they preserve nextPointerTag. -/
theorem allocate_six_ok (tracker : MachineHooks.BorrowState) (r : Chain tracker) :
    let t1 := ReferenceBorrowDriver.allocatedTracker tracker r.fresh
    let t2 := ReferenceBorrowDriver.allocatedTracker t1 r.slotFresh
    let t3 := ReferenceBorrowDriver.allocatedTracker t2 r.exprFresh
    let t4 := ReferenceBorrowDriver.allocatedTracker t3 r.helperFresh
    let t5 := ReferenceBorrowDriver.allocatedTracker t4 r.mutFresh
    let t6 := ReferenceBorrowDriver.allocatedTracker t5 r.mutEntryFresh
    allocate_six tracker.global = .ok (t6.global,#[tracker.global.nextPointerTag,t1.global.nextPointerTag,
      t2.global.nextPointerTag,t3.global.nextPointerTag,t4.global.nextPointerTag,t5.global.nextPointerTag]) := by
  dsimp only
  let t1 := ReferenceBorrowDriver.allocatedTracker tracker r.fresh
  let t2 := ReferenceBorrowDriver.allocatedTracker t1 r.slotFresh
  let t3 := ReferenceBorrowDriver.allocatedTracker t2 r.exprFresh
  let t4 := ReferenceBorrowDriver.allocatedTracker t3 r.helperFresh
  let t5 := ReferenceBorrowDriver.allocatedTracker t4 r.mutFresh
  unfold allocate_six
  erw [TypedRetagEmpty.allocate_tag tracker.global r.fresh]
  simp only [bind,Except.bind]
  erw [TypedRetagEmpty.allocate_tag t1.global r.slotFresh]
  simp only [bind,Except.bind]
  erw [TypedRetagEmpty.allocate_tag t2.global r.exprFresh]
  simp only [bind,Except.bind]
  erw [TypedRetagEmpty.allocate_tag t3.global r.helperFresh]
  simp only [bind,Except.bind]
  erw [TypedRetagEmpty.allocate_tag t4.global r.mutFresh]
  simp only [bind,Except.bind]
  erw [TypedRetagEmpty.allocate_tag t5.global r.mutEntryFresh]
  rfl

end DuplicatePrefix.GenericFunctionTagFormation

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GenericFunctionTagFormation." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved tag formation dependency {name}: {dependency}"
