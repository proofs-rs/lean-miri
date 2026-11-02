import duplicate_prefix.GeneralBorrowProtectedSiblingCounterBankGeneration
import duplicate_prefix.GeneralBorrowRetainedMutableAccessFacts
namespace DuplicatePrefix.GeneralBorrowRetainedMutableGlobal
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

structure Output {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len) (global : GlobalState)
    (kinds : List AccessKind) (reserve : Fin 5 → BorTag) where
  advanced : GlobalState
  child : UniIndex
  initial : GeneralBorrowRetainedMutableAccess.State root child global.nextPointerTag offset len
  state : GeneralBorrowRetainedMutableAccess.State root child global.nextPointerTag offset len
  allocated : global.newPointerTag = .ok (advanced,global.nextPointerTag)
  episode : GeneralBorrowRetainedMutableEpisode.Completed s global.nextPointerTag
  actual : initial.tree = (GeneralBorrowRetainedMutableEpisode.operation s global.nextPointerTag).tree
  history : GeneralBorrowRetainedMutableAccess.History initial kinds state
  empty : advanced.protectedTags = {}
  fresh : GeneralBorrowTagMap.Fresh state.tree.tagMapping advanced.nextPointerTag
  reserved : ∀ i,GeneralBorrowTagMap.Fresh state.tree.tagMapping (reserve i)

def generate {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len) (global : GlobalState)
    (empty : global.protectedTags = {})
    (below : GeneralBorrowProtectedSiblingGenerationBounds.KeysBelow s.bank.tree.tagMapping global.nextPointerTag.value.toNat)
    (positive : len ≠ 0) (room : s.bank.tree.nodes.size+5 ≤ 4294967295)
    (counterRoom : global.nextPointerTag.value.toNat+1 ≤ 4294967295)
    (kinds : List AccessKind) (reserve : Fin 5 → BorTag)
    (reserveAbove : ∀ i,global.nextPointerTag.value.toNat+1 ≤ (reserve i).value.toNat) :
    Output s global kinds reserve := by
  have allocFits : global.nextPointerTag.value < 18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    change global.nextPointerTag.value.toNat < 18446744073709551615
    omega
  let advanced : GlobalState := {global with nextPointerTag := TypedRetagEmpty.successorTag global.nextPointerTag allocFits}
  have successor : advanced.nextPointerTag.value.toNat = global.nextPointerTag.value.toNat+1 :=
    GeneralBorrowProtectedSiblingGenerationBounds.successor_nat _ allocFits
  have tagFresh := GeneralBorrowProtectedSiblingGenerationBounds.map_fresh _ _ below global.nextPointerTag (Nat.le_refl _)
  let episode := GeneralBorrowRetainedMutableEpisode.build s global.nextPointerTag tagFresh positive room
  let initial := GeneralBorrowRetainedMutableAccess.ofEpisode s global.nextPointerTag tagFresh positive room
  let final := GeneralBorrowRetainedMutableAccess.run initial kinds
  have future : ∀ tag,global.nextPointerTag.value.toNat+1 ≤ tag.value.toNat → GeneralBorrowTagMap.Fresh final.tree.tagMapping tag := by
    intro tag above
    have before := GeneralBorrowProtectedSiblingGenerationBounds.map_fresh _ _ below tag (by omega)
    have different : global.nextPointerTag ≠ tag := by intro equal;rw [←equal] at above;omega
    have retained := episode.fresh tag before different
    change GeneralBorrowTagMap.Fresh final.tree.tagMapping tag
    rw [GeneralBorrowRetainedMutableAccessFacts.run_mapping]
    change GeneralBorrowTagMap.Fresh initial.tree.tagMapping tag
    rw [GeneralBorrowRetainedMutableAccessFacts.ofEpisode_tree]
    exact retained
  exact {
    advanced := advanced,child := episode.childIndex,initial := initial,state := final,
    allocated := TypedRetagEmpty.allocate_tag global allocFits,
    episode := episode.completed,actual := GeneralBorrowRetainedMutableAccessFacts.ofEpisode_tree s global.nextPointerTag tagFresh positive room,
    history := GeneralBorrowRetainedMutableAccess.run_history initial kinds,
    empty := empty,fresh := future _ (by rw [successor];exact Nat.le_refl _),reserved := fun i => future _ (reserveAbove i) }
end
end DuplicatePrefix.GeneralBorrowRetainedMutableGlobal
