import empty_function.ProjectedAllocation
import empty_function.ChoiceProjection
import empty_function.PolicyChoiceSupply
namespace EmptyFunction.ProjectedPolicyChoiceSupply
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open EmptyFunction.WholeCall EmptyFunction.Specification EmptyFunction.ChoiceSupply
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

/-- A managed fresh stack allocation demands its one source slack response.
This extracts only the typed head; it does not assume address assignment succeeds. -/
 theorem supplied (s : Static) (p : Packet) (binding : SourceChoicePlan.ProjectedBinding s p)
    (id : AllocId) (reserved : MemoryState Provenance TreeBorrows.BorrowTree MiriMemoryKind)
    (reserve : p.before.machine.memory.reserveAllocId = (reserved,.ok id))
    (missing : p.before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (managed : p.before.machine.user.addresses.addressMode = .managed)
    (generation : AllocAddresses.AddressGenerationState)
    (current : p.before.machine.user.addresses.generation = some generation)
    (environment : PolicyChoiceSupply.Environment (SourceChoicePlan.projectedPlan binding) p.before.machine.user.payload.payload.user.choices) :
    PolicyChoiceSupply.Environment stackMissPlan p.before.machine.user.payload.payload.user.choices := by
  have fits := environment.fits
  unfold SourceChoicePlan.projectedPlan at fits
  rw [reserve] at fits
  simp only at fits
  unfold AddressChoicePlan.attempt at fits
  simp only [missing,Option.isSome_none,managed,current] at fits
  simp only [Bool.false_eq_true,Bool.false_or,Bool.not_true,Bool.false_and,bne_self_eq_false,
    Bool.false_eq_true,↓reduceIte] at fits
  try simp only [PolicyChoiceSupply.fits_pad] at fits
  unfold AddressChoicePlan.select at fits
  simp only [AllocAddresses.ReusePool.prepareTakeAddr,Bool.not_false,Bool.true_or,Bool.true_eq_false,
    Bool.false_eq_true,↓reduceIte,Id.run,pure,Pure.pure] at fits
  change ∃ input, ∃ supported : Supported (.index .slack 16) input, ∃ after,
    PolicyChoiceSupply.PolicyStep (.index .slack 16) p.before.machine.user.payload.payload.user.choices input after ∧ _ at fits
  obtain ⟨input,supported,after,step,tail⟩ := fits
  exact ⟨input,supported,after,step,True.intro⟩
end EmptyFunction.ProjectedPolicyChoiceSupply
