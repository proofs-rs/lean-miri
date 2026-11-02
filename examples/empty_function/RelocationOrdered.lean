import empty_function.RelocationMemoryStep
import empty_function.SourceChoicePlan
namespace EmptyFunction.RelocationOrdered
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
open EmptyFunction.ChoiceSupply
set_option autoImplicit false
set_option maxHeartbeats 4000000
private theorem fits_cast {m n : Nat} (h : Plan m = Plan n) (dimensions : m = n)
    (plan : Plan n) (tape : ExecutionChoices.Tape) :
    @Fits m (h.mpr plan) tape ↔ @Fits n plan tape := by cases dimensions; rfl
/-- Demand peeling uses the fixed physical metadata snapshot and the current
address cache; no future address success is used. -/
theorem head (snapshot : WholeCall.State) (current : ChoiceExecution.S) (id : AllocId)
    (tail : List (Option AllocId)) (info : AllocationInfo)
    (metadata : snapshot.machine.memory.getAllocInfo id = .ok info)
    (notDead : info.kind ≠ .dead) (notType : info.kind ≠ .typeId)
    (live : snapshot.machine.memory.isAllocLive id = true)
    (thread : current.threads.activeThread = snapshot.machine.threads.activeThread)
    (input : Fits (SourceChoicePlan.ordered snapshot (some id::tail) current.user.addresses)
      (ChoiceExecution.tapeAccess.get current)) :
    Fits (AddressChoicePlan.attempt current.user.addresses id
      ⟨.liveData,true,info.size,info.align,some .other,UInt32.ofNat current.threads.activeThread.toNat⟩
      (SourceChoicePlan.ordered snapshot tail)) (ChoiceExecution.tapeAccess.get current) := by
  have dimensions : 3*(tail.length+1) = 3*tail.length+3 := by omega
  cases cached : current.user.addresses.baseAddr.find? (fun row => row.allocId == id) with
  | none =>
    simp only [SourceChoicePlan.ordered,SourceChoicePlan.info,cached,Option.isSome_none,
      Bool.false_eq_true,↓reduceIte,metadata,Except.map,beq_iff_eq,notDead,notType,live,List.length_cons] at input
    rw [thread]
    exact (fits_cast (congrArg Plan dimensions) dimensions _ _).mp input
  | some row =>
    simp only [SourceChoicePlan.ordered,cached,Option.isSome_some,↓reduceIte,List.length_cons] at input
    have next := (fits_cast (congrArg Plan dimensions) dimensions _ _).mp input
    simpa only [AddressChoicePlan.attempt,cached,Option.isSome_some,↓reduceIte] using next
end EmptyFunction.RelocationOrdered
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.RelocationOrdered.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved relocation ordered axiom {dependency} in {name}"
