import Miri.Interpreter.ProvenanceGC
import Std.Tactic.Do

/-! The production exposure and GC paths use the allocation-local mutation
rules, then commit or classify their exact machine outcomes. -/
namespace Miri.Verification.TreeEffectsWP

open Miri.Interpreter Miri.Memory Miri.TreeBorrows Std.WP
open BorrowTree.MutationVerification

variable {K U Error : Type}
local notation "State" => MachineHooks.State K U
local notation "TreeAllocation" => Allocation Provenance BorrowTree

/-- Commit the tree first, then report the Tree Borrows outcome if the memory
update succeeded. A failed update takes precedence. -/
def commitPre [DecidableEq K] (before : State) (id : AllocId) (allocation : TreeAllocation)
    (tree : BorrowTree) (outcome : Except Error Unit) (updateError : AllocationLookupError → StepError)
    (treeError : Error → StepError) (post : Unit → State → Prop) (failure : StepError → State → Prop) : Prop :=
  match before.machine.memory.setLiveAllocation id (allocation.setExtra tree) with
  | .error error => failure (updateError error) before
  | .ok memory =>
    let after := { before with machine := { before.machine with memory } }
    match outcome with
    | .ok () => post () after
    | .error error => failure (treeError error) after

def exposeTreePre [DecidableEq K] (id : AllocId) (allocation : TreeAllocation)
    (tags : ProtectedTags) (tag : BorTag) (post : Unit → PointerMachine.State K U → Prop)
    (failure : StepError → PointerMachine.State K U → Prop) (before : PointerMachine.State K U) : Prop :=
  let commit := fun tree outcome => commitPre before id allocation tree outcome
    (fun error => .invalidProgram s!"exposure tree update: {reprStr error}")
    (fun error => .invalidProgram s!"Tree Borrows exposure invariant: {reprStr error}") post failure
  exposePre allocation.extra tags tag (fun tree => commit tree (.ok ())) (fun error tree => commit tree (.error error))

def collectTreePre [DecidableEq K] (id : AllocId) (allocation : TreeAllocation)
    (live : Array BorTag) (post : Unit → State → Prop) (failure : StepError → State → Prop) (before : State) : Prop :=
  let commit := fun tree outcome => commitPre before id allocation tree outcome
    (fun error => .invalidProgram s!"GC tree replacement: {reprStr error}")
    (fun error => .invalidProgram s!"GC tree invariant: {reprStr error}") post failure
  collectPre allocation.extra live (fun tree => commit tree (.ok ())) (fun error tree => commit tree (.error error))

theorem exposeTree_iff [DecidableEq K] (id : AllocId) (allocation : TreeAllocation)
    (tags : ProtectedTags) (tag : BorTag) (post : Unit → PointerMachine.State K U → Prop)
    (failure : StepError → PointerMachine.State K U → Prop) (before : PointerMachine.State K U) :
    wp (PointerMachine.exposeTree id allocation tags tag) post failure before ↔ exposeTreePre id allocation tags tag post failure before := by
  simp only [exposeTreePre, exposePre_iff, wp, WP.wpTrans, PointerMachine.exposeTree]
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind]
  cases outcome : (allocation.extra.exposeTag tags tag).outcome
  case' ok value => cases value
  all_goals
    cases updated : before.machine.memory.setLiveAllocation id
      (allocation.setExtra (allocation.extra.exposeTag tags tag).tree) <;>
      simp only [updated, commitPre, EStateM.bind, pure, Pure.pure, EStateM.pure,
        throw, throwThe, MonadExceptOf.throw, EStateM.throw,
        modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

@[spec high] theorem spec_exposeTree [DecidableEq K] (id : AllocId) (allocation : TreeAllocation)
    (tags : ProtectedTags) (tag : BorTag) (post : Unit → PointerMachine.State K U → Prop)
    (failure : StepError → PointerMachine.State K U → Prop) :
    Triple (PointerMachine.exposeTree id allocation tags tag) (exposeTreePre id allocation tags tag post failure) post failure :=
  Triple.iff.mpr (fun before => (exposeTree_iff id allocation tags tag post failure before).mpr)

theorem collectTree_iff [DecidableEq K] (id : AllocId) (allocation : TreeAllocation)
    (live : Array BorTag) (post : Unit → State → Prop)
    (failure : StepError → State → Prop) (before : State) :
    wp (ProvenanceGC.collectTree id allocation live) post failure before ↔ collectTreePre id allocation live post failure before := by
  simp only [collectTreePre, collectPre_iff, wp, WP.wpTrans, ProvenanceGC.collectTree]
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind]
  cases outcome : (allocation.extra.removeUnreachableTags live).outcome
  case' ok value => cases value
  all_goals
    cases updated : before.machine.memory.setLiveAllocation id
      (allocation.setExtra (allocation.extra.removeUnreachableTags live).tree) <;>
      simp only [updated, commitPre, EStateM.bind, pure, Pure.pure, EStateM.pure,
        throw, throwThe, MonadExceptOf.throw, EStateM.throw,
        modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

@[spec high] theorem spec_collectTree [DecidableEq K] (id : AllocId) (allocation : TreeAllocation)
    (live : Array BorTag) (post : Unit → State → Prop)
    (failure : StepError → State → Prop) :
    Triple (ProvenanceGC.collectTree id allocation live) (collectTreePre id allocation live post failure) post failure :=
  Triple.iff.mpr (fun before => (collectTree_iff id allocation live post failure before).mpr)

end Miri.Verification.TreeEffectsWP
