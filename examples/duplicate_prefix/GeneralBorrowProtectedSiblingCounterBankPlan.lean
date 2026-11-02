import duplicate_prefix.GeneralBorrowProtectedSiblingCounterBank
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingCounterBankPlan
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProtectedSiblingCounterBank GeneralBorrowProtectedSiblingGenerationBounds
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- Generate actual newPointerTag calls and all fresh-tag inequalities from the
initial counter bound, rather than supplying an action-tag sequence. -/
def generate (initial : GlobalState) (instructions : List Instruction)
    (room : initial.nextPointerTag.value.toNat+allocations instructions ≤ 4294967295) : Planned initial instructions := by
  induction instructions generalizing initial with
  | nil => exact ⟨[],initial,.nil initial,rfl,by simp [allocations],rfl,by simp [GeneralBorrowSharedBankMutableAction.tags],by simp [GeneralBorrowSharedBankMutableAction.tags],.nil,fun _ h => h⟩
  | cons instruction rest ih =>
    cases instruction with
    | borrow position =>
      have fresh : initial.nextPointerTag.value < 18446744073709551615 := by
        apply UInt64.lt_iff_toNat_lt.mpr
        change initial.nextPointerTag.value.toNat < 18446744073709551615
        have bound := room
        simp only [allocations] at bound
        omega
      let advanced := {initial with nextPointerTag := TypedRetagEmpty.successorTag initial.nextPointerTag fresh}
      have successor : advanced.nextPointerTag.value.toNat = initial.nextPointerTag.value.toNat+1 := successor_nat _ fresh
      have actual : initial.newPointerTag = .ok (advanced,initial.nextPointerTag) := TypedRetagEmpty.allocate_tag initial fresh
      let tail := ih advanced (by change advanced.nextPointerTag.value.toNat+allocations rest ≤ 4294967295;rw [successor];simp only [allocations] at room;omega)
      have nextNat : tail.global.nextPointerTag.value.toNat = initial.nextPointerTag.value.toNat+allocations (.borrow position::rest) := by
        have later := tail.nextNat
        rw [successor] at later
        simp only [allocations]
        omega
      have different : initial.nextPointerTag ∉ GeneralBorrowSharedBankMutableAction.tags tail.actions := by
        intro member
        have later := tail.above initial.nextPointerTag member
        rw [successor] at later
        omega
      exact {
        actions := .borrow initial.nextPointerTag position::tail.actions,global := tail.global,allocated := .borrow actual tail.allocated,
        unchanged := tail.unchanged,nextNat := nextNat,count := by simp only [GeneralBorrowSharedBankMutableAction.tags,List.length_cons,allocations,tail.count],
        above := by
          intro tag member
          simp only [GeneralBorrowSharedBankMutableAction.tags,List.mem_cons] at member
          rcases member with same | later
          · subst tag;exact Nat.le_refl _
          · have bounded := tail.above tag later;rw [successor] at bounded;omega,
        below := by
          intro tag member
          simp only [GeneralBorrowSharedBankMutableAction.tags,List.mem_cons] at member
          rcases member with same | later
          · subst tag;rw [nextNat];simp only [allocations];omega
          · exact tail.below tag later,
        unique := List.nodup_cons.mpr ⟨different,tail.unique⟩,
        choices := by intro count choices;exact ⟨choices.1,tail.choices (count+1) choices.2⟩ }
    | mutable =>
      have fresh : initial.nextPointerTag.value < 18446744073709551615 := by
        apply UInt64.lt_iff_toNat_lt.mpr
        change initial.nextPointerTag.value.toNat < 18446744073709551615
        have bound := room
        simp only [allocations] at bound
        omega
      let advanced := {initial with nextPointerTag := TypedRetagEmpty.successorTag initial.nextPointerTag fresh}
      have successor : advanced.nextPointerTag.value.toNat = initial.nextPointerTag.value.toNat+1 := successor_nat _ fresh
      have actual : initial.newPointerTag = .ok (advanced,initial.nextPointerTag) := TypedRetagEmpty.allocate_tag initial fresh
      let tail := ih advanced (by change advanced.nextPointerTag.value.toNat+allocations rest ≤ 4294967295;rw [successor];simp only [allocations] at room;omega)
      have nextNat : tail.global.nextPointerTag.value.toNat = initial.nextPointerTag.value.toNat+allocations (.mutable::rest) := by
        have later := tail.nextNat
        rw [successor] at later
        simp only [allocations]
        omega
      have different : initial.nextPointerTag ∉ GeneralBorrowSharedBankMutableAction.tags tail.actions := by
        intro member
        have later := tail.above initial.nextPointerTag member
        rw [successor] at later
        omega
      exact {
        actions := .mutable initial.nextPointerTag::tail.actions,global := tail.global,allocated := .mutable actual tail.allocated,
        unchanged := tail.unchanged,nextNat := nextNat,count := by simp only [GeneralBorrowSharedBankMutableAction.tags,List.length_cons,allocations,tail.count],
        above := by
          intro tag member
          simp only [GeneralBorrowSharedBankMutableAction.tags,List.mem_cons] at member
          rcases member with same | later
          · subst tag;exact Nat.le_refl _
          · have bounded := tail.above tag later;rw [successor] at bounded;omega,
        below := by
          intro tag member
          simp only [GeneralBorrowSharedBankMutableAction.tags,List.mem_cons] at member
          rcases member with same | later
          · subst tag;rw [nextNat];simp only [allocations];omega
          · exact tail.below tag later,
        unique := List.nodup_cons.mpr ⟨different,tail.unique⟩,
        choices := by intro count choices;exact tail.choices 1 choices }
    | gc extra =>
      let tail := ih initial room
      exact {
        actions := .gc extra::tail.actions,global := tail.global,allocated := .gc tail.allocated,
        unchanged := tail.unchanged,nextNat := tail.nextNat,count := tail.count,above := tail.above,below := tail.below,unique := tail.unique,
        choices := by intro count choices;exact tail.choices count choices }
    | exposeRoot =>
      let tail := ih initial room
      exact {
        actions := .exposeRoot::tail.actions,global := tail.global,allocated := .exposeRoot tail.allocated,
        unchanged := tail.unchanged,nextNat := tail.nextNat,count := tail.count,above := tail.above,below := tail.below,unique := tail.unique,
        choices := by intro count choices;exact tail.choices count choices }
    | rootAccess kind =>
      let tail := ih initial room
      exact {
        actions := .rootAccess kind::tail.actions,global := tail.global,allocated := .rootAccess tail.allocated,
        unchanged := tail.unchanged,nextNat := tail.nextNat,count := tail.count,above := tail.above,below := tail.below,unique := tail.unique,
        choices := by intro count choices;exact tail.choices (GeneralBorrowSharedRootAccess.count kind count) choices }
end
end DuplicatePrefix.GeneralBorrowProtectedSiblingCounterBankPlan
