import empty_function.RelocationNumeric
import empty_function.RootTagPost
import empty_function.RelocationContext
namespace EmptyFunction.RelocationInvariant
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
set_option autoImplicit false
set_option maxHeartbeats 4000000
/-- Composition of proved operation postconditions. No future-success fact is
part of validity: each argument below is obtained from the actual root result. -/
theorem successor (before : WholeCall.State) (after : ChoiceExecution.S)
    (tracker : MachineHooks.BorrowState) (generation next : AddressGenerationState)
    (remaining maximumSize maximumAlignment : Nat) (id : AllocId) (size : Size) (align : Align)
    (world : TreeRuntimeInput.World before.machine tracker)
    (numeric : InputDraft.GenerationResources generation remaining maximumSize maximumAlignment)
    (one : 1 ≤ remaining) (tagRoom : tracker.global.nextPointerTag.value.toNat+remaining < 2^64)
    (valid : align.pow2 ≤ 29) (sizeBound : size.bytes.toNat ≤ maximumSize)
    (alignBound : (RawGenerator.alignment align).toNat ≤ maximumAlignment)
    (memory : after.memory = before.machine.memory)
    (shape : next.generator = generation.generator ∨ ∃ slack : Fin 16,
      next.generator = (generation.generator.generate size align slack).state)
    (rootPost : ∃ global tag, tracker.global.rootPointerTag id = .ok (global,tag) ∧
      after.borrowTracker = some {tracker with global} ∧ after.dataRace = before.machine.dataRace ∧
      after.user.payload.payload.user.runtime = before.machine.user.payload.payload.user.runtime ∧
      RelocationContext.view after.user.payload = RelocationContext.view before.machine.user.payload) :
    ∃ nextTracker, TreeRuntimeInput.World after nextTracker ∧
      nextTracker.global.nextPointerTag.value.toNat+(remaining-1) < 2^64 ∧
      InputDraft.GenerationResources next (remaining-1) maximumSize maximumAlignment := by
  obtain ⟨global,tag,actual,enabled,_race,_runtime,_context⟩ := rootPost
  have tagPost := RootTagPost.root tracker.global id global tag actual
  refine ⟨{tracker with global},RootTagPost.world before.machine after tracker global id tag
    world memory enabled actual,?_,?_⟩
  · exact RelocationNumeric.tag_remaining _ _ remaining one tagRoom tagPost.2.2.2.2.2.1
  · exact RelocationNumeric.successor generation next remaining maximumSize maximumAlignment numeric
      one size align valid sizeBound alignBound shape
end EmptyFunction.RelocationInvariant
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.RelocationInvariant.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved relocation invariant axiom {dependency} in {name}"
