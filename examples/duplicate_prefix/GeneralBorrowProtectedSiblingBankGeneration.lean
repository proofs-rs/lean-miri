import duplicate_prefix.GeneralBorrowProtectedSiblingBankSeed
import duplicate_prefix.GeneralBorrowSharedBankMutableHistory
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingBankGeneration
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProtectedSiblingPartialFunctionHistory GeneralBorrowSharedBankMutableAction
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
noncomputable section

structure Generated {bytes windows} (h : History bytes windows) (offset len : UInt64)
    (positive : len ≠ 0) (actions : List Action) (reserve : Fin 5 → BorTag) where
  initial : GeneralBorrowSharedRootBankState.State GeneralBorrowFullSharedSeed.root h.rootNode.tag offset len
  sameTree : initial.bank.tree = h.output.tree
  initialHandles : initial.bank.handles = [GeneralBorrowFullSharedSeed.root]
  state : GeneralBorrowSharedRootBankState.State GeneralBorrowFullSharedSeed.root h.rootNode.tag offset len
  history : GeneralBorrowSharedBankMutableHistory.Run positive h.output.ended.nextPointerTag initial actions state
  length : state.bank.handles.length = handlesAfter 1 actions
  fresh : GeneralBorrowTagMap.Fresh state.bank.tree.tagMapping h.output.ended.nextPointerTag
  reserved : ∀ i,GeneralBorrowTagMap.Fresh state.bank.tree.tagMapping (reserve i)
  globalEmpty : h.output.ended.protectedTags = {}

/-- BorrowTree-component continuation with externally supplied fresh bank tags;
no GlobalState.newPointerTag allocation history is claimed here. Continue on the
exact tree and actual ended global of the protected partial
history. Initial old reservations may remain Reserved and unheld. The root-only
bank then supports shared branching, exposures, full GC, root Read/Write, and
unprotected mutable episodes without replacing or resetting that tree. -/
def generate {bytes windows} (h : History bytes windows) (nonzero : bytes ≠ 0) (offset len : UInt64)
    (positive : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ bytes.toNat)
    (actions : List Action) (choices : Choices 1 actions) (unique : (tags actions).Nodup)
    (terminalUnused : h.output.ended.nextPointerTag ∉ tags actions)
    (above : ∀ tag ∈ tags actions,h.output.ended.nextPointerTag.value.toNat ≤ tag.value.toNat)
    (reserve : Fin 5 → BorTag)
    (reserveAbove : ∀ i,h.output.ended.nextPointerTag.value.toNat ≤ (reserve i).value.toNat)
    (reserveUnused : ∀ i,reserve i ∉ tags actions)
    (room : windows.length+(tags actions).length+10 ≤ 4294967295) :
    Generated h offset len positive actions reserve := by
  have initialRoom : h.output.tree.nodes.size+4 ≤ 4294967295 := by rw [h.nodes];omega
  let initial := GeneralBorrowProtectedSiblingBankSeed.of_history h nonzero offset len bounds initialRoom
  have handles : initial.bank.handles.length = 1 := rfl
  have fresh : ∀ tag ∈ tags actions,GeneralBorrowTagMap.Fresh initial.bank.tree.tagMapping tag := by
    intro tag member
    exact GeneralBorrowProtectedSiblingGenerationBounds.map_fresh _ _ h.below tag (above tag member)
  have terminalFresh : GeneralBorrowTagMap.Fresh initial.bank.tree.tagMapping h.output.ended.nextPointerTag :=
    GeneralBorrowProtectedSiblingGenerationBounds.map_fresh _ _ h.below _ (Nat.le_refl _)
  have available := GeneralBorrowSharedBankMutableHistory.generate initial positive h.output.ended.nextPointerTag terminalFresh actions
    (by rw [handles];exact choices) unique terminalUnused fresh (by change h.output.tree.nodes.size+(tags actions).length+4 ≤ _;rw [h.nodes];omega)
  let final := Classical.choose available
  have output := Classical.choose_spec available
  have future : ∀ tag,tag ∉ tags actions → h.output.ended.nextPointerTag.value.toNat ≤ tag.value.toNat →
      GeneralBorrowTagMap.Fresh final.bank.tree.tagMapping tag := by
    intro tag unused above
    exact output.2.2.2 tag unused (GeneralBorrowProtectedSiblingGenerationBounds.map_fresh _ _ h.below tag above)
  have length : final.bank.handles.length = handlesAfter initial.bank.handles.length actions := output.2.1
  rw [handles] at length
  exact {
    initial := initial,sameTree := rfl,initialHandles := rfl,state := final,history := output.1,
    length := length,
    fresh := future _ terminalUnused (Nat.le_refl _),reserved := fun i => future _ (reserveUnused i) (reserveAbove i),globalEmpty := h.empty }
end
end DuplicatePrefix.GeneralBorrowProtectedSiblingBankGeneration
