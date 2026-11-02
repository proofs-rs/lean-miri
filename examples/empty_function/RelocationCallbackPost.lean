import empty_function.RootAddressOutcome
import empty_function.NoDrawBasicRootTotal
import empty_function.ForeignSelectionPartial
import empty_function.LiveMetadata
namespace EmptyFunction.RelocationCallbackPost
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 65536
abbrev S := ChoiceExecution.S

/-- The common actual-callback post. Generation coherence is needed only in
the branch where an initial uncached non-TypeId target exists. -/
structure Post (before : WholeCall.State) (tracker : MachineHooks.BorrowState)
    (needed : Prop) (final : S) where
  global : GlobalState
  world : TreeRuntimeInput.World final {tracker with global}
  frame : RootFramePost.Frame tracker.global global
  memory : final.memory = before.machine.memory
  threads : final.threads = before.machine.threads
  runtime : final.user.payload.payload.user.runtime = before.machine.user.payload.payload.user.runtime
  context : RelocationContext.view final.user.payload = RelocationContext.view before.machine.user.payload
  race : final.dataRace = before.machine.dataRace
  bases : ∀ id row, before.machine.user.addresses.baseAddr.find? (fun old => old.allocId == id) = some row →
    final.user.addresses.baseAddr.find? (fun old => old.allocId == id) = some row
  static : AddressStaticPost.view final.user.addresses = AddressStaticPost.view before.machine.user.addresses
  tables : InputDraft.AddressTables {before with machine := final}
  addresses : Preservation.ExistingAddressFacts before {before with machine := final}
  generation : needed → ∃ next, InputDraft.GenerationRepresentation {before with machine := final} next

def generated {before : WholeCall.State} {tracker : MachineHooks.BorrowState} {needed : Prop} {final : S}
    (post : RootAddressOutcome.Post before tracker final) : Post before tracker needed final :=
  ⟨post.global,post.world,post.frame,post.memory,post.threads,post.runtime,post.context,post.race,
    post.bases,post.static,post.tables,post.addresses,fun _ => post.generation⟩

def cached {before : WholeCall.State} {tracker : MachineHooks.BorrowState} {needed : Prop} {final : S}
    (old : InputDraft.AddressTables before) (notNeeded : ¬ needed)
    (post : NoDrawBasicRootTotal.Post before tracker final) : Post before tracker needed final :=
  ⟨post.global,post.world,post.frame,post.memory,post.threads,post.runtime,post.context,post.race,
    post.bases,post.static,post.tables,AddressStaticPost.facts before {before with machine := final}
      old post.tables post.memory post.bases post.static,fun proof => False.elim (notNeeded proof)⟩

def identical (before : WholeCall.State) (tracker : MachineHooks.BorrowState) (needed : Prop)
    (world : TreeRuntimeInput.World before.machine tracker) (tables : InputDraft.AddressTables before)
    (generation : needed → ∃ current, InputDraft.GenerationRepresentation before current) :
    Post before tracker needed before.machine :=
  ⟨tracker.global,world,⟨rfl,rfl,by intro id tag prior;exact prior⟩,rfl,rfl,rfl,rfl,rfl,
    (by intro id row prior;exact prior),rfl,tables,
    AddressStaticPost.facts before before tables tables rfl (by intro id row prior;exact prior) rfl,generation⟩
end EmptyFunction.RelocationCallbackPost
