import duplicate_prefix.GeneralBorrowProtectedSiblingCounterBankRun
import duplicate_prefix.GeneralBorrowProtectedSiblingPartialCounter
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingCounterBankGeneration
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProtectedSiblingPartialFunctionHistory GeneralBorrowProtectedSiblingCounterBank
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

structure Generated {bytes windows} (h : History bytes windows) (offset len : UInt64) (positive : len ≠ 0)
    (instructions : List Instruction) (reserve : Fin 5 → BorTag) where
  initial : GeneralBorrowSharedRootBankState.State GeneralBorrowFullSharedSeed.root h.rootNode.tag offset len
  sameTree : initial.bank.tree = h.output.tree
  global : GlobalState
  state : GeneralBorrowSharedRootBankState.State GeneralBorrowFullSharedSeed.root h.rootNode.tag offset len
  history : GeneralBorrowProtectedSiblingCounterBankRun.Run positive global.nextPointerTag h.output.ended initial instructions global state
  unchanged : global = {h.output.ended with nextPointerTag := global.nextPointerTag}
  counter : global.nextPointerTag.value.toNat = windows.length+allocations instructions+2
  below : GeneralBorrowProtectedSiblingGenerationBounds.KeysBelow state.bank.tree.tagMapping global.nextPointerTag.value.toNat
  fresh : GeneralBorrowTagMap.Fresh state.bank.tree.tagMapping global.nextPointerTag
  reserved : ∀ i,GeneralBorrowTagMap.Fresh state.bank.tree.tagMapping (reserve i)
  empty : global.protectedTags = {}

/-- Every new bank tag is obtained from real checked global allocation. Aligned
allocation and tree traces are interleaved step by step, and the final advanced
global, rather than the earlier ended counter, supplies the function's new tag. -/
def generate {bytes windows} (h : History bytes windows) (nonzero : bytes ≠ 0) (offset len : UInt64)
    (positive : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ bytes.toNat)
    (instructions : List Instruction) (choices : Choices 1 instructions) (reserve : Fin 5 → BorTag)
    (reserveAbove : ∀ i,windows.length+allocations instructions+2 ≤ (reserve i).value.toNat)
    (room : windows.length+allocations instructions+10 ≤ 4294967295) :
    Generated h offset len positive instructions reserve := by
  have counter := GeneralBorrowProtectedSiblingPartialCounter.completed bytes windows h.output h.actual
  let plan := GeneralBorrowProtectedSiblingCounterBankPlan.generate h.output.ended instructions (by rw [counter];omega)
  have endNat : plan.global.nextPointerTag.value.toNat = windows.length+allocations instructions+2 := by
    have equation := plan.nextNat
    rw [counter] at equation
    omega
  have monotone : h.output.ended.nextPointerTag.value.toNat ≤ plan.global.nextPointerTag.value.toNat := by rw [plan.nextNat];omega
  have initialRoom : h.output.tree.nodes.size+4 ≤ 4294967295 := by rw [h.nodes];omega
  let initial := GeneralBorrowProtectedSiblingBankSeed.of_history h nonzero offset len bounds initialRoom
  have handles : initial.bank.handles.length = 1 := rfl
  have fresh : ∀ tag ∈ GeneralBorrowSharedBankMutableAction.tags plan.actions,
      GeneralBorrowTagMap.Fresh initial.bank.tree.tagMapping tag := by
    intro tag member
    exact GeneralBorrowProtectedSiblingGenerationBounds.map_fresh _ _ h.below tag (plan.above tag member)
  have terminalFresh : GeneralBorrowTagMap.Fresh initial.bank.tree.tagMapping plan.global.nextPointerTag :=
    GeneralBorrowProtectedSiblingGenerationBounds.map_fresh _ _ h.below _ monotone
  have terminalUnused : plan.global.nextPointerTag ∉ GeneralBorrowSharedBankMutableAction.tags plan.actions := by
    intro member
    have impossible := plan.below _ member
    omega
  have available := GeneralBorrowSharedBankMutableHistory.generate initial positive plan.global.nextPointerTag terminalFresh plan.actions
    (by rw [handles];exact plan.choices 1 choices) plan.unique terminalUnused fresh
    (by change h.output.tree.nodes.size+(GeneralBorrowSharedBankMutableAction.tags plan.actions).length+4 ≤ _;rw [h.nodes,plan.count];omega)
  let final := Classical.choose available
  have output := Classical.choose_spec available
  have future : ∀ tag,plan.global.nextPointerTag.value.toNat ≤ tag.value.toNat → GeneralBorrowTagMap.Fresh final.bank.tree.tagMapping tag := by
    intro tag above
    have unused : tag ∉ GeneralBorrowSharedBankMutableAction.tags plan.actions := by
      intro member
      have smaller := plan.below tag member
      omega
    exact output.2.2.2 tag unused (GeneralBorrowProtectedSiblingGenerationBounds.map_fresh _ _ h.below tag (Nat.le_trans monotone above))
  have below : GeneralBorrowProtectedSiblingGenerationBounds.KeysBelow final.bank.tree.tagMapping plan.global.nextPointerTag.value.toNat := by
    intro row member
    by_cases smaller : row.1.value.toNat < plan.global.nextPointerTag.value.toNat
    · exact smaller
    · have available := future row.1 (by omega)
      exact False.elim (available row member rfl)
  exact {
    initial := initial,sameTree := rfl,global := plan.global,state := final,
    history := GeneralBorrowProtectedSiblingCounterBankRun.interleave plan.allocated output.1 h.empty,
    unchanged := plan.unchanged,counter := endNat,below := below,fresh := future _ (Nat.le_refl _),
    reserved := fun i => future _ (by rw [endNat];exact reserveAbove i),
    empty := (congrArg GlobalState.protectedTags plan.unchanged).trans h.empty }
end
end DuplicatePrefix.GeneralBorrowProtectedSiblingCounterBankGeneration
