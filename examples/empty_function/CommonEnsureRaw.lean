import empty_function.CommonEnsureTotal
import empty_function.CanonicalRootBinding
import empty_function.RelocationPartialFold
namespace EmptyFunction.CommonEnsureTotal
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.WholeCall EmptyFunction.MaterializationPreservation
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- The original raw current input supplies every finite source-format and
relocation-target fact. The actual canonical ensure either stops with its real
non-UB error or supplies the live-tree/body/old-parent return certificates.
There is no resource, choice-supply, callback-safety, or stage-success premise. -/
theorem ensure (s : Static) (metadata : Specification.Metadata s)
    (p : Packet) (input : InputDraft.CurrentInputDraft s p)
    (id : AllocId) (sourceBytes : Allocation CtfeProvenance Unit)
    (selected : ChoiceAdmission.SelectedSource s p id sourceBytes)
    (current : State) (memory : current.machine.memory = p.before.machine.memory)
    (addresses : current.machine.user.addresses = p.before.machine.user.addresses)
    (runtime : current.machine.user.payload.payload.user.runtime = p.before.machine.user.payload.payload.user.runtime)
    (tracker : MachineHooks.BorrowState) (world : TreeRuntimeInput.World current.machine tracker)
    (noRace : current.machine.dataRace = none) : Outcome s p id current := by
  apply from_conversion s metadata p input id sourceBytes selected current memory addresses runtime noRace
  have raw := (SelectedMaterializationFacts.facts s p input id sourceBytes selected).1
  have tables := SelectedMaterializationFacts.tables s p input id sourceBytes selected
  have converted := RelocationPartialFold.convert s p.before sourceBytes raw tables current.machine memory addresses runtime
    tracker world noRace s.prepared.compiler.runtime.target.base (source s).address
    metadata.target (CanonicalRootBinding.width s metadata) (CanonicalRootBinding.classifier s)
  rw [←CanonicalRootBinding.root s] at converted
  rcases converted with ⟨converted,middle,actual,attributes,⟨post⟩⟩ | stopped
  · refine Or.inl ⟨converted,middle,actual,attributes,⟨{
      tracker := post.tracker
      world := post.world
      memory := post.memory
      threads := post.threads
      runtime := post.runtime
      context := post.context
      race := post.race
      tables := ?_
      addresses := ?_
    }⟩⟩
    · exact AddressTransport.tables {{p.before with machine := current.machine} with machine := middle}
        {current with machine := middle} rfl rfl post.tables
    · simpa only [Preservation.ExistingAddressFacts] using post.addresses
  · exact Or.inr stopped
end EmptyFunction.CommonEnsureTotal
open Lean in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name == ``EmptyFunction.CommonEnsureTotal.ensure then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved raw-ensure axiom {dependency} in {name}"
