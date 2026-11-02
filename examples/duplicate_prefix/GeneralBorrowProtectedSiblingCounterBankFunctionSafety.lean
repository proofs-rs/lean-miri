import duplicate_prefix.GeneralBorrowProtectedSiblingCounterBankGeneration
import duplicate_prefix.GeneralBorrowProtectedSiblingBankCaller
import duplicate_prefix.GeneralBorrowForestFunctionSafety
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingCounterBankFunctionSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open Miri.DataStructures Miri.TreeBorrows.Tree ActualReferenceContext
open GeneralBorrowProtectedSiblingPartial GeneralBorrowProtectedSiblingCounterBank
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

def sourcePrefix (bytes : UInt64) (nonzero : bytes ≠ 0) (windows : List (Window bytes)) (instructions : List Instruction)
    (room : windows.length+allocations instructions+10 ≤ 4294967295) :=
  GeneralBorrowProtectedSiblingPartialFunctionHistory.generate bytes nonzero windows (by omega)

def joined (bytes : UInt64) (nonzero : bytes ≠ 0) (windows : List (Window bytes))
    (offset len : UInt64) (positive : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ bytes.toNat)
    (instructions : List Instruction) (choices : Choices 1 instructions)
    (room : windows.length+allocations instructions+10 ≤ 4294967295) (reserve : Fin 5 → BorTag)
    (reserveAbove : ∀ i,windows.length+allocations instructions+2 ≤ (reserve i).value.toNat) :=
  GeneralBorrowProtectedSiblingCounterBankGeneration.generate (sourcePrefix bytes nonzero windows instructions room)
    nonzero offset len positive bounds instructions choices reserve reserveAbove room

/-- Actual allocation and arbitrary protected partial-window lifetimes feed
one continuous bank/global history. Every shared or mutable bank constructor
calls real GlobalState.newPointerTag and uses exactly its returned tag. Shared
branching, root exposure/Read/Write, mutable activation and full GC run on the
same tree. The final advanced global supplies the original all-count invocation.
All graph, ownership, protector, freshness and source successes are derived;
only physical caller/MIR/storage and numeric schedule resources are explicit. -/
theorem invoke (bytes : UInt64) (nonzero : bytes ≠ 0) (windows : List (Window bytes))
    (offset len : UInt64) (positive : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ bytes.toNat)
    (instructions : List Instruction) (choices : Choices 1 instructions)
    (room : windows.length+allocations instructions+10 ≤ 4294967295) (reserve : Fin 5 → BorTag)
    (reserveAbove : ∀ i,windows.length+allocations instructions+2 ≤ (reserve i).value.toNat)
    (s : GeneralBorrowProtectedSiblingBankCaller.Caller
      (joined bytes nonzero windows offset len positive bounds instructions choices room reserve reserveAbove).state.bank.tree
      (sourcePrefix bytes nonzero windows instructions room).rootNode.tag
      (joined bytes nonzero windows offset len positive bounds instructions choices room reserve reserveAbove).global.nextPointerTag offset len reserve
      (joined bytes nonzero windows offset len positive bounds instructions choices room reserve reserveAbove).global) (count : UInt64) :
    let h := sourcePrefix bytes nonzero windows instructions room
    let g := joined bytes nonzero windows offset len positive bounds instructions choices room reserve reserveAbove
    GeneralBorrowProtectedSiblingPartialFunctionHistory.operation bytes windows = .ok h.output ∧
    GeneralBorrowProtectedReleaseHistory.AllReleased h.output.generated.tree h.output.generated.global.protectedTags h.output.generated.tags ∧
    g.initial.bank.tree = h.output.tree ∧
    s.tracker.global = g.global ∧
    GeneralBorrowProtectedSiblingCounterBankRun.Run positive g.global.nextPointerTag h.output.ended g.initial instructions g.global g.state ∧
    let cfg := config s.options (s.remaining+1) s.span
    ∃ installed finalState,
      Call.initStackFrame (ExecutionMachine.callHooks cfg s.limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
          (Pointer.new (.concrete s.id s.parentTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm,
          ActualReferenceMetadata.reference⟩,.Copy (EmptyRootArguments.second count)] false (.memory s.place) (.stop true)
        ⟨⟨#[]⟩,s.before⟩ = .ok () installed ∧
      SuccessfulTrace.Trace cfg s.limits installed finalState ∧
      ExecutionMachine.step cfg s.limits () finalState = (finalState,.ok false) ∧
      finalState.stack.frames = #[] ∧
      CallSafety.NoUBBeforeReturn
        (⟨cfg,s.limits,fun _ _ => True⟩ : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit)
        1 installed ∧
      (∀ before, SuccessfulTrace.Trace cfg s.limits installed before →
        ∃ after continuing, ExecutionMachine.step cfg s.limits () before = (after,.ok continuing)) := by
  let h := sourcePrefix bytes nonzero windows instructions room
  let g := joined bytes nonzero windows offset len positive bounds instructions choices room reserve reserveAbove
  refine ⟨h.actual,h.released,g.sameTree,s.globalEq,g.history,?_⟩
  exact GeneralBorrowForestFunctionSafety.invoke g.state.bank.tree GeneralBorrowFullSharedSeed.root g.state.bank.resources
    h.rootNode.tag g.global.nextPointerTag offset len (GeneralBorrowSharedRootBankState.entryData g.state g.global.nextPointerTag g.fresh)
    reserve g.reserved (GeneralBorrowProtectedSiblingBankCaller.to_forest s g.empty) count
end
end DuplicatePrefix.GeneralBorrowProtectedSiblingCounterBankFunctionSafety
open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.GeneralBorrowProtectedSiblingCounterBankFunctionSafety.invoke] do
    for dependency in (←collectAxioms declaration) do
      unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
        throwError "unapproved sequential protected/bank original invocation dependency {dependency}"
