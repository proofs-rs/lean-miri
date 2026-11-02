import empty_function.TreeRuntimeInput
import Lean
namespace EmptyFunction.RootTagPost
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536

/-- Checked root-tag construction is monotone, costs at most one tag and
retains every pre-existing root lookup and protector. This is a postcondition
of the source operation, not a validity/success field. -/
theorem root (global : GlobalState) (id : AllocId) (after : GlobalState) (tag : BorTag)
    (actual : global.rootPointerTag id = .ok (after,tag)) :
    after.rootTag? id = some tag ∧
      (∀ other old, global.rootTag? other = some old → after.rootTag? other = some old) ∧
      after.protectedTags = global.protectedTags ∧ after.trackedPointerTags = global.trackedPointerTags ∧
      global.nextPointerTag.value.toNat ≤ after.nextPointerTag.value.toNat ∧
      after.nextPointerTag.value.toNat ≤ global.nextPointerTag.value.toNat + 1 ∧
      (after.rootPointerTags = global.rootPointerTags ∨
        (after.rootPointerTags = global.rootPointerTags.push (id,global.nextPointerTag) ∧
          global.nextPointerTag.value.toNat < after.nextPointerTag.value.toNat)) := by
  cases cached : global.rootTag? id with
  | some old =>
    simp only [GlobalState.rootPointerTag,cached,pure,Except.pure] at actual
    cases actual
    exact ⟨cached,by intro other old present;exact present,rfl,rfl,Nat.le_refl _,by omega,Or.inl rfl⟩
  | none =>
    unfold GlobalState.rootPointerTag at actual
    simp only [cached,GlobalState.newPointerTag,BorTag.succ] at actual
    split at actual
    · simp [bind,Except.bind] at actual
    · rename_i next successor
      have notMax : global.nextPointerTag.value ≠ 18446744073709551615 := by
        intro maximum
        simp only [maximum,↓reduceIte] at successor
        cases successor
      have room : global.nextPointerTag.value.toNat+1 < 2^64 := by
        have bounded := UInt64.toNat_lt global.nextPointerTag.value
        have different : global.nextPointerTag.value.toNat ≠ 18446744073709551615 := by
          intro equal
          exact notMax (UInt64.toNat_inj.mp equal)
        omega
      have nextNonzero : global.nextPointerTag.value+1 ≠ 0 := by
        intro zero
        have sum : (global.nextPointerTag.value+1).toNat = global.nextPointerTag.value.toNat+1 := by
          rw [UInt64.toNat_add]
          change (global.nextPointerTag.value.toNat+1) % 2^64 = _
          exact Nat.mod_eq_of_lt room
        rw [zero] at sum
        change 0 = _ at sum
        omega
      have nextEq : next = (⟨global.nextPointerTag.value+1,nextNonzero⟩ : BorTag) := by
        simp only [notMax,↓reduceIte,BorTag.ofUInt64,nextNonzero,↓reduceDIte] at successor
        exact (Option.some.inj successor).symm
      cases nextEq
      simp only [bind,Except.bind,pure,Except.pure] at actual
      cases actual
      have missing : global.rootPointerTags.find? (fun entry => entry.1 == id) = none := by
        simpa only [GlobalState.rootTag?,Option.map_eq_none_iff] using cached
      have lookup : ({global with rootPointerTags := global.rootPointerTags.push (id,global.nextPointerTag)} : GlobalState).rootTag? id =
          some global.nextPointerTag := by
        simp [GlobalState.rootTag?,Array.find?_push,missing]
      refine ⟨lookup,?_,rfl,rfl,?_,?_,?_⟩
      · intro other old present
        unfold GlobalState.rootTag? at present ⊢
        simp only [Array.find?_push]
        cases prior : global.rootPointerTags.find? (fun entry => entry.1 == other) with
        | none => simp only [prior,Option.map_none] at present;cases present
        | some entry => simpa [prior] using present
      · change global.nextPointerTag.value.toNat ≤ (global.nextPointerTag.value+1).toNat
        rw [UInt64.toNat_add]
        change _ ≤ (global.nextPointerTag.value.toNat+1) % 2^64
        rw [Nat.mod_eq_of_lt room]
        omega
      · change (global.nextPointerTag.value+1).toNat ≤ global.nextPointerTag.value.toNat+1
        rw [UInt64.toNat_add]
        change (global.nextPointerTag.value.toNat+1) % 2^64 ≤ _
        rw [Nat.mod_eq_of_lt room]
        omega
      · refine Or.inr ⟨rfl,?_⟩
        change global.nextPointerTag.value.toNat < (global.nextPointerTag.value+1).toNat
        rw [UInt64.toNat_add]
        change _ < (global.nextPointerTag.value.toNat+1) % 2^64
        rw [Nat.mod_eq_of_lt room]
        omega

/-- Existing live tree shape/permissions are unchanged when the shared tag
counter advances. Only the high-water inequality needs strengthening. -/
def tree_mono (tree : BorrowTree) (old next : BorTag)
    (formed : TreeRuntimeInput.TreeFormed tree old) (increasing : old.value.toNat ≤ next.value.toNat) :
    TreeRuntimeInput.TreeFormed tree next := by
  rcases formed with ⟨rank,free,unique,accounting,clean,mapped,nodes,tags,below⟩
  refine ⟨rank,free,unique,accounting,clean,mapped,nodes,tags,?_⟩
  intro row member
  have prior := below row member
  omega
/-- Current global bookkeeping remains formed after the actual tag operation. -/
theorem formed (global : GlobalState) (id : AllocId) (after : GlobalState) (tag : BorTag)
    (before : TreeRuntimeInput.GlobalFormed global)
    (actual : global.rootPointerTag id = .ok (after,tag)) : TreeRuntimeInput.GlobalFormed after := by
  obtain ⟨_lookup,_stable,protectors,_tracked,increasing,_cost,shape⟩ := root global id after tag actual
  constructor
  · intro row member
    rw [protectors] at member
    have prior := before.protectedBelow row member
    omega
  · intro row member
    rcases shape with same | ⟨append,strict⟩
    · rw [same] at member
      have prior := before.rootsBelow row member
      omega
    · rw [append] at member
      rcases Array.mem_push.mp member with old | same
      · have prior := before.rootsBelow row old
        omega
      · cases same
        exact strict

/-- All arbitrary old live trees survive the root/cache update, using only
physical-memory equality and the checked monotone global tag counter. -/
theorem world {K U : Type} (before after : Interpreter.MachineHooks.MachineState K U)
    (tracker : Interpreter.MachineHooks.BorrowState) (global : GlobalState) (id : AllocId) (tag : BorTag)
    (prior : TreeRuntimeInput.World before tracker)
    (memory : after.memory = before.memory)
    (enabled : after.borrowTracker = some {tracker with global})
    (actual : tracker.global.rootPointerTag id = .ok (global,tag)) :
    TreeRuntimeInput.World after {tracker with global} := by
  have post := root tracker.global id global tag actual
  refine ⟨enabled,formed tracker.global id global tag prior.globals actual,?_⟩
  intro row member
  rw [memory] at member
  obtain ⟨tree⟩ := prior.liveTrees row member
  exact ⟨tree_mono row.2.allocation.extra tracker.global.nextPointerTag global.nextPointerTag tree post.2.2.2.2.1⟩
end EmptyFunction.RootTagPost
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.RootTagPost.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved root tag post axiom {dependency} in {name}"
