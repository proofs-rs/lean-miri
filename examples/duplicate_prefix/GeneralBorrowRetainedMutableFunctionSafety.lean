import duplicate_prefix.GeneralBorrowProtectedSiblingCounterBankFunctionSafety
import duplicate_prefix.GeneralBorrowProtectedSiblingCounterBankGrowth
import duplicate_prefix.GeneralBorrowRetainedMutableGlobal
namespace DuplicatePrefix.GeneralBorrowRetainedMutableFunctionSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open Miri.DataStructures Miri.TreeBorrows.Tree ActualReferenceContext
open GeneralBorrowProtectedSiblingPartial GeneralBorrowProtectedSiblingCounterBank
open GeneralBorrowProtectedSiblingCounterBankFunctionSafety
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

def bankPrefix (bytes : UInt64) (nonzero : bytes ≠ 0) (windows : List (Window bytes))
    (offset len : UInt64) (positive : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ bytes.toNat)
    (instructions : List Instruction) (choices : Choices 1 instructions)
    (room : windows.length+allocations instructions+10 ≤ 4294967295) (reserve : Fin 5 → BorTag)
    (reserveAbove : ∀ i,windows.length+allocations instructions+3 ≤ (reserve i).value.toNat) :=
  joined bytes nonzero windows offset len positive bounds instructions choices room reserve
    (by intro i;have h := reserveAbove i;omega)

def retained (bytes : UInt64) (nonzero : bytes ≠ 0) (windows : List (Window bytes))
    (offset len : UInt64) (positive : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ bytes.toNat)
    (instructions : List Instruction) (choices : Choices 1 instructions)
    (room : windows.length+allocations instructions+10 ≤ 4294967295) (reserve : Fin 5 → BorTag)
    (reserveAbove : ∀ i,windows.length+allocations instructions+3 ≤ (reserve i).value.toNat)
    (kinds : List AccessKind) := by
  let h := sourcePrefix bytes nonzero windows instructions room
  let g := bankPrefix bytes nonzero windows offset len positive bounds instructions choices room reserve reserveAbove
  have growth := GeneralBorrowProtectedSiblingCounterBankGrowth.run g.history
  have initialSize : g.initial.bank.tree.nodes.size = windows.length+1 := by rw [g.sameTree,h.nodes]
  have nodeRoom : g.state.bank.tree.nodes.size+5 ≤ 4294967295 := by rw [initialSize] at growth;omega
  have counterRoom : g.global.nextPointerTag.value.toNat+1 ≤ 4294967295 := by rw [g.counter];omega
  exact GeneralBorrowRetainedMutableGlobal.generate g.state g.global g.empty g.below positive nodeRoom counterRoom kinds reserve
    (by intro i;rw [g.counter];exact reserveAbove i)

/-- Real protected-lifetime and mixed-bank history allocates one further mutable
child with the actual global counter, activates it, and performs any finite
sequence of Read/Write operations through that SAME child. The actual advanced
global and retained child tag then supply the original all-count physical MIR
invocation. No final ownership, allocator, freshness or successful-operation
certificate is a premise. -/
theorem invoke (bytes : UInt64) (nonzero : bytes ≠ 0) (windows : List (Window bytes))
    (offset len : UInt64) (positive : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ bytes.toNat)
    (instructions : List Instruction) (choices : Choices 1 instructions)
    (room : windows.length+allocations instructions+10 ≤ 4294967295) (reserve : Fin 5 → BorTag)
    (reserveAbove : ∀ i,windows.length+allocations instructions+3 ≤ (reserve i).value.toNat)
    (kinds : List AccessKind)
    (s : GeneralBorrowProtectedSiblingBankCaller.Caller
      (retained bytes nonzero windows offset len positive bounds instructions choices room reserve reserveAbove kinds).state.tree
      (bankPrefix bytes nonzero windows offset len positive bounds instructions choices room reserve reserveAbove).global.nextPointerTag
      (retained bytes nonzero windows offset len positive bounds instructions choices room reserve reserveAbove kinds).advanced.nextPointerTag offset len reserve
      (retained bytes nonzero windows offset len positive bounds instructions choices room reserve reserveAbove kinds).advanced) (count : UInt64) :
    let h := sourcePrefix bytes nonzero windows instructions room
    let g := bankPrefix bytes nonzero windows offset len positive bounds instructions choices room reserve reserveAbove
    let q := retained bytes nonzero windows offset len positive bounds instructions choices room reserve reserveAbove kinds
    GeneralBorrowProtectedSiblingPartialFunctionHistory.operation bytes windows = .ok h.output ∧
    GeneralBorrowProtectedReleaseHistory.AllReleased h.output.generated.tree h.output.generated.global.protectedTags h.output.generated.tags ∧
    g.initial.bank.tree = h.output.tree ∧
    s.tracker.global = q.advanced ∧
    g.global.newPointerTag = .ok (q.advanced,g.global.nextPointerTag) ∧
    GeneralBorrowRetainedMutableEpisode.Completed g.state g.global.nextPointerTag ∧
    q.initial.tree = (GeneralBorrowRetainedMutableEpisode.operation g.state g.global.nextPointerTag).tree ∧
    GeneralBorrowRetainedMutableAccess.History q.initial kinds q.state ∧
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
  let g := bankPrefix bytes nonzero windows offset len positive bounds instructions choices room reserve reserveAbove
  let q := retained bytes nonzero windows offset len positive bounds instructions choices room reserve reserveAbove kinds
  refine ⟨h.actual,h.released,g.sameTree,s.globalEq,q.allocated,q.episode,q.actual,q.history,g.history,?_⟩
  exact GeneralBorrowForestFunctionSafety.invoke q.state.tree GeneralBorrowFullSharedSeed.root q.state.resources
    g.global.nextPointerTag q.advanced.nextPointerTag offset len (GeneralBorrowRetainedMutableAccess.entryData q.state q.advanced.nextPointerTag q.fresh)
    reserve q.reserved (GeneralBorrowProtectedSiblingBankCaller.to_forest s q.empty) count
end
end DuplicatePrefix.GeneralBorrowRetainedMutableFunctionSafety
