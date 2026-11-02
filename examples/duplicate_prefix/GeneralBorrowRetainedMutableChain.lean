import duplicate_prefix.GeneralBorrowRetainedMutableActivate
import duplicate_prefix.GeneralBorrowProtectedSiblingGenerationBounds
namespace DuplicatePrefix.GeneralBorrowRetainedMutableChain
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowRetainedMutableAccess
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
structure Current (root : UniIndex) (offset len : UInt64) where
  index : UniIndex
  tag : BorTag
  state : State root index tag offset len

structure Stage {root : UniIndex} {offset len : UInt64} (s : Current root offset len)
    (global : GlobalState) (positive : len≠0) (kinds : List AccessKind) where
  fresh : GeneralBorrowTagMap.Fresh s.state.tree.tagMapping global.nextPointerTag
  activation : GeneralBorrowRetainedMutableActivate.Output s.state global.nextPointerTag fresh positive
  final : State root activation.index global.nextPointerTag offset len
  accesses : History activation.state kinds final
  advanced : GlobalState
  allocated : global.newPointerTag=.ok (advanced,global.nextPointerTag)
  empty : advanced.protectedTags={}
  below : GeneralBorrowProtectedSiblingGenerationBounds.KeysBelow final.tree.tagMapping advanced.nextPointerTag.value.toNat
  growth : final.tree.nodes.size≤s.state.tree.nodes.size+1
  counter : advanced.nextPointerTag.value.toNat=global.nextPointerTag.value.toNat+1

def Stage.current {root offset len s global positive kinds} (stage : @Stage root offset len s global positive kinds) : Current root offset len :=
  ⟨stage.activation.index,global.nextPointerTag,stage.final⟩

def stage {root : UniIndex} {offset len : UInt64} (s : Current root offset len)
    (global : GlobalState) (positive : len≠0) (kinds : List AccessKind)
    (empty : global.protectedTags={})
    (below : GeneralBorrowProtectedSiblingGenerationBounds.KeysBelow s.state.tree.tagMapping global.nextPointerTag.value.toNat)
    (room : s.state.tree.nodes.size+5≤4294967295)
    (counterRoom : global.nextPointerTag.value.toNat+1≤4294967295) : Stage s global positive kinds := by
  have allocFits : global.nextPointerTag.value < 18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    change global.nextPointerTag.value.toNat<18446744073709551615
    omega
  let advanced : GlobalState := {global with nextPointerTag:=TypedRetagEmpty.successorTag global.nextPointerTag allocFits}
  have successor : advanced.nextPointerTag.value.toNat=global.nextPointerTag.value.toNat+1 := GeneralBorrowProtectedSiblingGenerationBounds.successor_nat _ allocFits
  have fresh := GeneralBorrowProtectedSiblingGenerationBounds.map_fresh _ _ below global.nextPointerTag (Nat.le_refl _)
  let activated := GeneralBorrowRetainedMutableActivate.build s.state global.nextPointerTag fresh positive room
  let final := run activated.state kinds
  have future : ∀ tag,advanced.nextPointerTag.value.toNat≤tag.value.toNat→GeneralBorrowTagMap.Fresh final.tree.tagMapping tag := by
    intro tag above
    have before := GeneralBorrowProtectedSiblingGenerationBounds.map_fresh _ _ below tag (by rw [successor] at above;omega)
    have different : global.nextPointerTag≠tag := by intro equal;rw [←equal,successor] at above;omega
    rw [GeneralBorrowRetainedMutableAccessFacts.run_mapping]
    exact activated.future tag before different
  have finalBelow : GeneralBorrowProtectedSiblingGenerationBounds.KeysBelow final.tree.tagMapping advanced.nextPointerTag.value.toNat := by
    intro row member
    by_cases smaller : row.1.value.toNat<advanced.nextPointerTag.value.toNat
    · exact smaller
    · exact False.elim ((future row.1 (by omega)) row member rfl)
  exact {
    fresh:=fresh,activation:=activated,final:=final,accesses:=run_history activated.state kinds,
    advanced:=advanced,allocated:=TypedRetagEmpty.allocate_tag global allocFits,empty:=empty,below:=finalBelow,
    growth:=by rw [show final.tree.nodes=activated.state.tree.nodes from GeneralBorrowRetainedMutableAccessFacts.run_nodes _ _];exact activated.growth,
    counter:=successor }

inductive Trace {root : UniIndex} {offset len : UInt64} (positive : len≠0) :
    Current root offset len→GlobalState→List (List AccessKind)→Current root offset len→GlobalState→Prop where
  | nil (s global) : Trace positive s global [] s global
  | cons {s global kinds rest final finalGlobal} (one : Stage s global positive kinds)
      (tail : Trace positive one.current one.advanced rest final finalGlobal) :
      Trace positive s global (kinds::rest) final finalGlobal

structure Output {root : UniIndex} {offset len : UInt64} (s : Current root offset len)
    (global : GlobalState) (positive : len≠0) (rounds : List (List AccessKind)) where
  current : Current root offset len
  advanced : GlobalState
  actual : Trace positive s global rounds current advanced
  empty : advanced.protectedTags={}
  below : GeneralBorrowProtectedSiblingGenerationBounds.KeysBelow current.state.tree.tagMapping advanced.nextPointerTag.value.toNat
  growth : current.state.tree.nodes.size≤s.state.tree.nodes.size+rounds.length
  counter : advanced.nextPointerTag.value.toNat=global.nextPointerTag.value.toNat+rounds.length

def generate {root : UniIndex} {offset len : UInt64} (s : Current root offset len)
    (global : GlobalState) (positive : len≠0) (rounds : List (List AccessKind))
    (empty : global.protectedTags={})
    (below : GeneralBorrowProtectedSiblingGenerationBounds.KeysBelow s.state.tree.tagMapping global.nextPointerTag.value.toNat)
    (room : s.state.tree.nodes.size+rounds.length+4≤4294967295)
    (counterRoom : global.nextPointerTag.value.toNat+rounds.length≤4294967295) : Output s global positive rounds := by
  induction rounds generalizing s global with
  | nil => exact ⟨s,global,.nil s global,empty,below,by simp,by simp⟩
  | cons kinds rest ih =>
    let one := stage s global positive kinds empty below (by simp only [List.length_cons] at room;omega)
      (by simp only [List.length_cons] at counterRoom;omega)
    have laterRoom : one.current.state.tree.nodes.size+rest.length+4≤4294967295 := by
      have growth:=one.growth
      change one.final.tree.nodes.size+rest.length+4≤_
      simp only [List.length_cons] at room
      omega
    have laterCounter : one.advanced.nextPointerTag.value.toNat+rest.length≤4294967295 := by
      rw [one.counter]
      simp only [List.length_cons] at counterRoom
      omega
    let tail := ih one.current one.advanced one.empty one.below laterRoom laterCounter
    exact ⟨tail.current,tail.advanced,.cons one tail.actual,tail.empty,tail.below,
      by have first:=one.growth;have later:=tail.growth;change tail.current.state.tree.nodes.size≤s.state.tree.nodes.size+(kinds::rest).length;simp only [List.length_cons];change tail.current.state.tree.nodes.size≤one.final.tree.nodes.size+rest.length at later;omega,
      by rw [tail.counter,one.counter];simp only [List.length_cons];omega⟩
end
end DuplicatePrefix.GeneralBorrowRetainedMutableChain
