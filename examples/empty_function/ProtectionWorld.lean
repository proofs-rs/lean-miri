import empty_function.ProtectionOutcome
import empty_function.ResourceFailures
import empty_function.RootTagPost
namespace EmptyFunction.ProtectionWorld
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open EmptyFunction.WholeCall EmptyFunction.Specification EmptyFunction.UnitRetag
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem anchor (s : Static) (p : Packet) (input : InputDraft.CurrentInputDraft s p)
    (machine : ProtectionOutcome.Machine)
    (enabled : machine.borrowTracker = some input.tracker)
    (memory : machine.memory = p.before.machine.memory) :
    TreeRuntimeInput.World machine input.tracker := by
  refine ⟨enabled,input.world.globals,?_⟩
  intro row member
  rw [memory] at member
  exact input.world.liveTrees row member

/-- A successful checked tag allocation supplies the exact counter increment
needed for current-tree formation; no spare counter interval is assumed. -/
theorem allocated (machine : ProtectionOutcome.Machine) (tracker : MachineHooks.BorrowState)
    (world : TreeRuntimeInput.World machine tracker) (global : GlobalState) (tag : BorTag)
    (actual : tracker.global.newPointerTag = .ok (global,tag)) :
    TreeRuntimeInput.World {machine with borrowTracker := some {tracker with global}} {tracker with global} := by
  obtain ⟨room,tagEq,next,roots,protectors,tracked⟩ := ResourceFailures.tag_success tracker.global global tag actual
  refine ⟨rfl,⟨?_,?_⟩,?_⟩
  · intro row member
    rw [protectors] at member
    have bound := world.globals.protectedBelow row member
    change row.1.value.toNat < global.nextPointerTag.value.toNat
    rw [next]
    omega
  · intro row member
    rw [roots] at member
    have bound := world.globals.rootsBelow row member
    change row.2.value.toNat < global.nextPointerTag.value.toNat
    rw [next]
    omega
  · intro row member
    obtain ⟨formed⟩ := world.liveTrees row member
    exact ⟨RootTagPost.tree_mono row.2.allocation.extra tracker.global.nextPointerTag global.nextPointerTag
      formed (by rw [next];omega)⟩

theorem registered (machine : ProtectionOutcome.Machine) (tracker : MachineHooks.BorrowState)
    (world : TreeRuntimeInput.World machine tracker) (tag : BorTag)
    (below : tag.value.toNat < tracker.global.nextPointerTag.value.toNat) :
    TreeRuntimeInput.World (registeredMachine machine tracker tag) (registeredTracker tracker tag) := by
  refine ⟨rfl,⟨?_,world.globals.rootsBelow⟩,world.liveTrees⟩
  intro row member
  change row ∈ (tracker.global.protectedTags.entries.filter fun entry => entry.1 != tag).push (tag,.StrongProtector) at member
  rcases Array.mem_push.mp member with prior | same
  · exact world.globals.protectedBelow row (Array.mem_filter.mp prior).1
  · subst row
    exact below

end EmptyFunction.ProtectionWorld
