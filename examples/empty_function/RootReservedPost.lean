import empty_function.RootTagPost
namespace EmptyFunction.RootReservedPost
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows
set_option autoImplicit false
set_option maxHeartbeats 4000000
/-- A child tag reserved before lazy conversion is below all subsequently
fresh tags and absent from the old root cache. -/
def Fence (global : GlobalState) (reserved : BorTag) : Prop :=
  reserved.value.toNat < global.nextPointerTag.value.toNat ∧
    ∀ row ∈ global.rootPointerTags, row.2 ≠ reserved

private theorem member (global : GlobalState) (id : AllocId) (tag : BorTag)
    (lookup : global.rootTag? id = some tag) :
    ∃ row ∈ global.rootPointerTags, row.2 = tag := by
  unfold GlobalState.rootTag? at lookup
  cases prior : global.rootPointerTags.find? (fun row => row.1 == id) with
  | none => simp only [prior,Option.map_none] at lookup; cases lookup
  | some row =>
    simp only [prior,Option.map_some] at lookup
    exact ⟨row,Array.mem_of_find?_eq_some prior,Option.some.inj lookup⟩

/-- Root construction preserves the reservation fence in its original source
order, even if the source root is allocated after the child tag. -/
theorem root (global after : GlobalState) (id : AllocId) (tag reserved : BorTag)
    (fence : Fence global reserved)
    (actual : global.rootPointerTag id = .ok (after,tag)) :
    Fence after reserved ∧ tag ≠ reserved := by
  obtain ⟨lookup,_stable,_protected,_tracked,increasing,_cost,shape⟩ := RootTagPost.root global id after tag actual
  have avoids : ∀ row ∈ after.rootPointerTags, row.2 ≠ reserved := by
    intro row member
    rcases shape with same | ⟨append,_strict⟩
    · rw [same] at member
      exact fence.2 row member
    · rw [append] at member
      rcases Array.mem_push.mp member with old | same
      · exact fence.2 row old
      · cases same
        intro equal
        change global.nextPointerTag = reserved at equal
        have prior := fence.1
        rw [equal] at prior
        exact Nat.lt_irrefl _ prior
  refine ⟨⟨by have prior := fence.1;omega,avoids⟩,?_⟩
  obtain ⟨row,present,equal⟩ := member after id tag lookup
  simpa only [equal] using avoids row present

/-- Ordinary pre-call root high water gives the initial exclusion; no empty
root cache or pre-materialization order is imposed. -/
theorem initial (before after : GlobalState) (reserved : BorTag)
    (old : ∀ row ∈ before.rootPointerTags, row.2.value.toNat < reserved.value.toNat)
    (same : after.rootPointerTags = before.rootPointerTags)
    (above : reserved.value.toNat < after.nextPointerTag.value.toNat) : Fence after reserved := by
  refine ⟨above,?_⟩
  intro row present equal
  rw [same] at present
  have bound := old row present
  rw [equal] at bound
  exact Nat.lt_irrefl _ bound
end EmptyFunction.RootReservedPost
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.RootReservedPost.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved reserved root post axiom {dependency} in {name}"
