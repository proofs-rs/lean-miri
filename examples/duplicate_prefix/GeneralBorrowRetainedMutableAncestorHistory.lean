import duplicate_prefix.GeneralBorrowRetainedMutableAncestorStack
namespace DuplicatePrefix.GeneralBorrowRetainedMutableAncestorHistory
open Miri.DataStructures Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowRetainedMutableAncestorStack
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
inductive Instruction where
  | access (kind : AccessKind)
  | reborrow
  | up

def allocations : List Instruction→Nat
  | []=>0
  | .reborrow::rest=>allocations rest+1
  | _::rest=>allocations rest

def Choices : Nat→List Instruction→Prop
  | _,[]=>True
  | depth,.access _::rest=>Choices depth rest
  | depth,.reborrow::rest=>Choices (depth+1) rest
  | depth,.up::rest=>0<depth ∧ Choices (depth-1) rest

inductive Trace {root offset len} (positive : len≠0) : Stack root offset len→GlobalState→List Instruction→Stack root offset len→GlobalState→Prop where
  | nil (s global) : Trace positive s global [] s global
  | access {s global kind rest final advanced}
      (completed : (GeneralBorrowRetainedMutableAccess.operation s.current.state kind).status=.Completed)
      (tail : Trace positive (access s kind) global rest final advanced) :
      Trace positive s global (.access kind::rest) final advanced
  | up {s global rest final advanced} (valid : 0<s.ancestors.length)
      (tail : Trace positive (pop s valid) global rest final advanced) :
      Trace positive s global (.up::rest) final advanced
  | reborrow {s global rest final advanced}
      (one : GeneralBorrowRetainedMutableChain.Stage s.current global positive [])
      (room : s.current.state.tree.nodes.size+5≤4294967295)
      (tail : Trace positive (activate s global.nextPointerTag one.fresh positive room) one.advanced rest final advanced) :
      Trace positive s global (.reborrow::rest) final advanced

structure Output {root offset len} (s : Stack root offset len) (global : GlobalState)
    (positive : len≠0) (instructions : List Instruction) where
  final : Stack root offset len
  advanced : GlobalState
  actual : Trace positive s global instructions final advanced
  empty : advanced.protectedTags={}
  below : GeneralBorrowProtectedSiblingGenerationBounds.KeysBelow final.current.state.tree.tagMapping advanced.nextPointerTag.value.toNat
  counter : advanced.nextPointerTag.value.toNat=global.nextPointerTag.value.toNat+allocations instructions

def generate {root offset len} (s : Stack root offset len) (global : GlobalState)
    (positive : len≠0) (instructions : List Instruction) (choices : Choices s.ancestors.length instructions)
    (empty : global.protectedTags={})
    (below : GeneralBorrowProtectedSiblingGenerationBounds.KeysBelow s.current.state.tree.tagMapping global.nextPointerTag.value.toNat)
    (room : s.current.state.tree.nodes.size+allocations instructions+4≤4294967295)
    (counterRoom : global.nextPointerTag.value.toNat+allocations instructions≤4294967295) : Output s global positive instructions := by
  induction instructions generalizing s global with
  | nil => exact ⟨s,global,.nil s global,empty,below,by simp [allocations]⟩
  | cons instruction rest ih =>
    cases instruction with
    | access kind =>
      let next:=access s kind
      have nodes:=GeneralBorrowRetainedMutableAccessFacts.build_nodes s.current.state kind
      have mapping:=GeneralBorrowRetainedMutableAccessFacts.build_mapping s.current.state kind
      have nextBelow : GeneralBorrowProtectedSiblingGenerationBounds.KeysBelow next.current.state.tree.tagMapping global.nextPointerTag.value.toNat := by
        change GeneralBorrowProtectedSiblingGenerationBounds.KeysBelow (GeneralBorrowRetainedMutableAccess.build s.current.state kind).state.tree.tagMapping _
        rw [mapping];exact below
      have nextRoom : next.current.state.tree.nodes.size+allocations rest+4≤4294967295 := by
        change (GeneralBorrowRetainedMutableAccess.build s.current.state kind).state.tree.nodes.size+allocations rest+4≤_
        rw [show (GeneralBorrowRetainedMutableAccess.build s.current.state kind).state.tree.nodes.size=s.current.state.tree.nodes.size from congrArg UniValMap.size nodes]
        exact room
      let tail:=ih next global (by rw [access_length];exact choices) empty nextBelow nextRoom counterRoom
      exact ⟨tail.final,tail.advanced,.access (GeneralBorrowRetainedMutableAccess.build s.current.state kind).completed tail.actual,tail.empty,tail.below,tail.counter⟩
    | up =>
      have valid : 0<s.ancestors.length:=choices.1
      let next:=pop s valid
      have same : next.current.state.tree=s.current.state.tree:=pop_tree s valid
      have nextChoices : Choices next.ancestors.length rest := by
        have length:=pop_length s valid
        change next.ancestors.length+1=s.ancestors.length at length
        have chosen:=choices.2
        have equal : next.ancestors.length=s.ancestors.length-1:=by omega
        rw [equal];exact chosen
      let tail:=ih next global nextChoices empty (by rw [same];exact below) (by rw [same];exact room) counterRoom
      exact ⟨tail.final,tail.advanced,.up valid tail.actual,tail.empty,tail.below,tail.counter⟩
    | reborrow =>
      have nodeRoom : s.current.state.tree.nodes.size+5≤4294967295 := by simp only [allocations] at room;omega
      have allocRoom : global.nextPointerTag.value.toNat+1≤4294967295 := by simp only [allocations] at counterRoom;omega
      let one:=GeneralBorrowRetainedMutableChain.stage s.current global positive [] empty below nodeRoom allocRoom
      let next:=activate s global.nextPointerTag one.fresh positive nodeRoom
      have same : next.current=one.current:=rfl
      have nextRoom : next.current.state.tree.nodes.size+allocations rest+4≤4294967295 := by
        rw [same]
        have growth:=one.growth
        change one.final.tree.nodes.size+allocations rest+4≤_
        simp only [allocations] at room
        omega
      have nextCounter : one.advanced.nextPointerTag.value.toNat+allocations rest≤4294967295 := by
        rw [one.counter]
        simp only [allocations] at counterRoom
        omega
      let tail:=ih next one.advanced (by rw [activate_length];exact choices) one.empty
        (by rw [same];exact one.below) nextRoom nextCounter
      exact ⟨tail.final,tail.advanced,.reborrow one nodeRoom tail.actual,tail.empty,tail.below,
        by rw [tail.counter,one.counter];simp only [allocations];omega⟩
end
end DuplicatePrefix.GeneralBorrowRetainedMutableAncestorHistory
