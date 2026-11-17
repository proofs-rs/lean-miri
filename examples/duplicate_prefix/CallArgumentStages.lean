import duplicate_prefix.CallEntryFacts
import duplicate_prefix.CopyIntrinsic
namespace DuplicatePrefix.CallArgumentStages
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

theorem copy_argument {P S C E Other Extern FnABI ArgABI : Type}
    (h : CallHooks P S C E Other Extern FnABI ArgABI) (choice : C)
    (operand : OpTy P) (callerAbi calleeAbi : ArgABI) (index : Nat) (destination : Place)
    (calleeTy : TyId) (before live evaluated copied : S) (place : RuntimeStackPlace P)
    (callee : (calleeTy == (h.argLayout calleeAbi).ty) = true)
    (caller : (operand.layout.layout == (h.argLayout callerAbi).layout) = true)
    (compat : h.checkArgumentCompat choice callerAbi calleeAbi before = .ok true before)
    (isLocal : destination.projection.isEmpty = true)
    (metadata : (!operand.metadata.hasMeta || operand.layout.ty == calleeTy) = true)
    (storage : h.storageLiveDyn choice destination.localId operand.metadata before = .ok () live)
    (evaluate : h.evalPlace choice destination false live = .ok place evaluated)
    (copy : h.copyAllowTransmute choice operand place evaluated = .ok () copied) :
    Call.passArgument h choice (.Copy operand) callerAbi calleeAbi index destination calleeTy false before =
      .ok () copied := by
  unfold Call.passArgument
  unfold_internal ".Call.require"
  simp only [FnArg.layout, FnArg.copyFnArg, callee, caller, compat, isLocal, metadata, storage, evaluate, copy,
    Bool.not_false, ↓reduceIte, bind, EStateM.bind, pure, EStateM.pure]

theorem with_retag_mode_updated
    (mode : Miri.TreeBorrows.RetagPolicy.RetagMode) (action : MachineHooks.M K U A)
    (before after : MachineHooks.State K U) (tracker next : MachineHooks.BorrowState) (value : A)
    (enabled : before.machine.borrowTracker = some tracker)
    (body : action {before with machine := {before.machine with borrowTracker := some {tracker with retagMode := mode}}} =
      .ok value after)
    (trackedAfter : after.machine.borrowTracker = some next) :
    MachineHooks.withRetagMode mode action before = .ok value
      {after with machine := {after.machine with borrowTracker := some {next with retagMode := tracker.retagMode}}} := by
  unfold MachineHooks.withRetagMode
  rw [enabled]
  dsimp only
  rw [body]
  simp only [trackedAfter]

end DuplicatePrefix.CallArgumentStages

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.CallArgumentStages.copy_argument,
      ``DuplicatePrefix.CallArgumentStages.with_retag_mode_updated] do
   for dependency in (← collectAxioms declaration) do
     unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
       throwError "unapproved call argument composition dependency {dependency}"
