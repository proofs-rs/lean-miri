import empty_function.GlobalErrorAware
import empty_function.RootTreePost
import empty_function.ProtectionOutcome
import empty_function.FootprintAfter
import empty_function.CanonicalDictionaries
import empty_function.RelocationContext
namespace EmptyFunction.MaterializationPreservation
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.WholeCall
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

abbrev leaves (s : Static) := Configuration.leaves s.prepared s.options.place.debugAssertions
abbrev source (s : Static) := CanonicalDictionaries.pointerSource s.prepared.compiler s.prepared.image (leaves s)
abbrev globalLeaves (s : Static) := CanonicalDictionaries.globalLeaves s.prepared.compiler s.prepared.image (leaves s)
abbrev extras (s : Static) := EvalCoreMachine.extras (leaves s).sync ConcurrencyErrors.storeBuffer

private theorem rights_refl (tree : BorrowTree) : Preservation.OldNodeRights tree tree := by
  refine ⟨fun _ _ present => present,fun _ present => present,?_⟩
  intro index node present
  refine ⟨node,present,rfl,rfl,rfl,rfl,rfl,fun _ member => member,?_⟩
  intro byte segment member contains
  exact ⟨segment,member,contains,rfl,rfl⟩

/-- The initial source ID is not live. Its materialization and child-tree
write-back therefore preserve every original live allocation and old node's
observable rights by exact row retention, without constraining the new root. -/
theorem original_live (before after : WholeCall.State) (id : AllocId)
    (entry : InputDraft.Entry)
    (absent : before.machine.memory.live.find? (fun row => row.1 == id) = none)
    (installed : after.machine.memory.live =
      (before.machine.memory.live.filter fun row => row.1 != id).push (id,entry)) :
    Preservation.OriginalLiveAllocations before after := by
  intro oldId old prior
  have different : oldId ≠ id := by
    intro same
    subst oldId
    rw [absent] at prior
    cases prior
  have clean : (before.machine.memory.live.filter fun row => row.1 != id).find? (fun row => row.1 == oldId) = some (oldId,old) := by
    rw [Array.find?_filter]
    have test : (fun row : AllocId × InputDraft.Entry => (row.1 != id) && (row.1 == oldId)) =
        (fun row => row.1 == oldId) := by
      funext row
      by_cases equal : row.1 = oldId <;> simp [equal,different]
    change before.machine.memory.live.find? (fun row => (row.1 != id) && (row.1 == oldId)) = _
    rw [test]
    exact prior
  refine ⟨old,?_,rfl,rfl,rights_refl old.allocation.extra⟩
  simp only [installed,Array.find?_push,clean,Option.or]

/-- Canonical extras registration and live insertion change no field read
by the fixed unit body/terminator, beyond the separately tracked addresses. -/
theorem stable (s : Static) (before middle : ChoiceExecution.S)
    (tracker : MachineHooks.BorrowState) (global : GlobalState) (id : AllocId)
    (allocation : Allocation Provenance BorrowTree)
    (threads : middle.threads = before.threads) (race : middle.dataRace = before.dataRace)
    (context : RelocationContext.view middle.user.payload = RelocationContext.view before.user.payload) :
    ProtectionOutcome.Stable before
      (GlobalErrorAware.installed
        (MemoryExtras.putAllocation (extras s) {middle with borrowTracker := some {tracker with global}} id ⟨none,#[]⟩)
        id .global allocation) := by
  refine ⟨threads,race,?_,?_,?_⟩
  · exact congrArg (fun view => view.2.1) context
  · exact congrArg (fun view => view.2.2.1) context
  · exact congrArg (fun view => view.2.2.2.2) context

/-- Installing a lazy source retains the fold's completed address tables. -/
theorem addresses (s : Static) (middle : ChoiceExecution.S)
    (tracker : MachineHooks.BorrowState) (global : GlobalState) (id : AllocId)
    (allocation : Allocation Provenance BorrowTree) :
    (GlobalErrorAware.installed
      (MemoryExtras.putAllocation (extras s) {middle with borrowTracker := some {tracker with global}} id ⟨none,#[]⟩)
      id .global allocation).user.addresses = middle.user.addresses := rfl

/-- Ordinary owned source insertion preserves all current live tree witnesses. -/
theorem installed_world {K U : Type} (machine : MachineHooks.MachineState K U) (tracker : MachineHooks.BorrowState)
    (id : AllocId) (kind : K) (allocation : Allocation Provenance BorrowTree)
    (prior : TreeRuntimeInput.World machine tracker)
    (formed : TreeRuntimeInput.TreeFormed allocation.extra tracker.global.nextPointerTag) :
    TreeRuntimeInput.World (GlobalErrorAware.installed machine id kind allocation) tracker := by
  refine ⟨prior.enabled,prior.globals,?_⟩
  intro row member
  change row ∈ (machine.memory.live.filter fun entry => entry.1 != id).push (id,⟨.machine kind,allocation⟩) at member
  rcases Array.mem_push.mp member with old | same
  · exact prior.liveTrees row (Array.mem_filter.mp old).1
  · subst row
    exact ⟨formed⟩
end EmptyFunction.MaterializationPreservation

open Lean in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.MaterializationPreservation.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved common-ensure axiom {dependency} in {name}"
