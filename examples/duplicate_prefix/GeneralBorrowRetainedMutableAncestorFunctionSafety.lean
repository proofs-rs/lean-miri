import duplicate_prefix.GeneralBorrowRetainedMutableAncestorHistory
import duplicate_prefix.GeneralBorrowRetainedMutableChainFunctionSafety
import duplicate_prefix.GeneralBorrowProtectedSiblingCounterBankFunctionSafety
import duplicate_prefix.GeneralBorrowProtectedSiblingCounterBankGrowth
namespace DuplicatePrefix.GeneralBorrowRetainedMutableAncestorFunctionSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open Miri.DataStructures Miri.TreeBorrows.Tree ActualReferenceContext
open GeneralBorrowProtectedSiblingPartial GeneralBorrowProtectedSiblingCounterBank
open GeneralBorrowProtectedSiblingCounterBankFunctionSafety GeneralBorrowRetainedMutableChain
open GeneralBorrowRetainedMutableChainFunctionSafety (ofBank)
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

def bankPrefix (bytes : UInt64) (nonzero : bytes≠0) (windows : List (Window bytes))
    (offset len : UInt64) (positive : len≠0) (bounds : offset.toNat+len.toNat≤bytes.toNat)
    (instructions : List Instruction) (choices : Choices 1 instructions) (actions : List GeneralBorrowRetainedMutableAncestorHistory.Instruction)
    (room : windows.length+allocations instructions+GeneralBorrowRetainedMutableAncestorHistory.allocations actions+10≤4294967295)
    (reserve : Fin 5→BorTag)
    (reserveAbove : ∀ i,windows.length+allocations instructions+GeneralBorrowRetainedMutableAncestorHistory.allocations actions+2≤(reserve i).value.toNat) :=
  joined bytes nonzero windows offset len positive bounds instructions choices (by omega) reserve
    (by intro i;have h:=reserveAbove i;omega)

def branched (bytes : UInt64) (nonzero : bytes≠0) (windows : List (Window bytes))
    (offset len : UInt64) (positive : len≠0) (bounds : offset.toNat+len.toNat≤bytes.toNat)
    (instructions : List Instruction) (choices : Choices 1 instructions) (actions : List GeneralBorrowRetainedMutableAncestorHistory.Instruction)
    (room : windows.length+allocations instructions+GeneralBorrowRetainedMutableAncestorHistory.allocations actions+10≤4294967295)
    (reserve : Fin 5→BorTag)
    (reserveAbove : ∀ i,windows.length+allocations instructions+GeneralBorrowRetainedMutableAncestorHistory.allocations actions+2≤(reserve i).value.toNat)
    (validActions : GeneralBorrowRetainedMutableAncestorHistory.Choices 0 actions) := by
  let h := sourcePrefix bytes nonzero windows instructions (by omega)
  let g := bankPrefix bytes nonzero windows offset len positive bounds instructions choices actions room reserve reserveAbove
  let initial := GeneralBorrowRetainedMutableAncestorStack.initial (ofBank g.state g.global.nextPointerTag g.fresh)
  have growth := GeneralBorrowProtectedSiblingCounterBankGrowth.run g.history
  have initialSize : g.initial.bank.tree.nodes.size=windows.length+1 := by rw [g.sameTree,h.nodes]
  have nodeRoom : initial.current.state.tree.nodes.size+GeneralBorrowRetainedMutableAncestorHistory.allocations actions+4≤4294967295 := by
    change g.state.bank.tree.nodes.size+GeneralBorrowRetainedMutableAncestorHistory.allocations actions+4≤_
    rw [initialSize] at growth
    omega
  have counterRoom : g.global.nextPointerTag.value.toNat+GeneralBorrowRetainedMutableAncestorHistory.allocations actions≤4294967295 := by rw [g.counter];omega
  exact GeneralBorrowRetainedMutableAncestorHistory.generate initial g.global positive actions validActions g.empty g.below nodeRoom counterRoom

/-- A source-generated protected/bank history feeds a tagless ancestor-stack
protocol: Read/Write the current pointer, allocate and activate a mutable child,
or pop to the parent. Popping discards the former descendant handle; subsequent
ancestor Writes and new sibling branches never reuse an invalidated descendant.
Every constructor uses real newPointerTag. The final selected current tag feeds
the original all-count physical MIR call. This is a restricted stack protocol. -/
theorem invoke (bytes : UInt64) (nonzero : bytes≠0) (windows : List (Window bytes))
    (offset len : UInt64) (positive : len≠0) (bounds : offset.toNat+len.toNat≤bytes.toNat)
    (instructions : List Instruction) (choices : Choices 1 instructions)
    (actions : List GeneralBorrowRetainedMutableAncestorHistory.Instruction)
    (validActions : GeneralBorrowRetainedMutableAncestorHistory.Choices 0 actions)
    (room : windows.length+allocations instructions+GeneralBorrowRetainedMutableAncestorHistory.allocations actions+10≤4294967295)
    (reserve : Fin 5→BorTag)
    (reserveAbove : ∀ i,windows.length+allocations instructions+GeneralBorrowRetainedMutableAncestorHistory.allocations actions+2≤(reserve i).value.toNat)
    (s : GeneralBorrowProtectedSiblingBankCaller.Caller
      (branched bytes nonzero windows offset len positive bounds instructions choices actions room reserve reserveAbove validActions).final.current.state.tree
      (branched bytes nonzero windows offset len positive bounds instructions choices actions room reserve reserveAbove validActions).final.current.tag
      (branched bytes nonzero windows offset len positive bounds instructions choices actions room reserve reserveAbove validActions).advanced.nextPointerTag
      offset len reserve
      (branched bytes nonzero windows offset len positive bounds instructions choices actions room reserve reserveAbove validActions).advanced)
    (count : UInt64) :
    let h := sourcePrefix bytes nonzero windows instructions (by omega)
    let g := bankPrefix bytes nonzero windows offset len positive bounds instructions choices actions room reserve reserveAbove
    let q := branched bytes nonzero windows offset len positive bounds instructions choices actions room reserve reserveAbove validActions
    GeneralBorrowProtectedSiblingPartialFunctionHistory.operation bytes windows=.ok h.output ∧
    GeneralBorrowProtectedReleaseHistory.AllReleased h.output.generated.tree h.output.generated.global.protectedTags h.output.generated.tags ∧
    g.initial.bank.tree=h.output.tree ∧
    GeneralBorrowProtectedSiblingCounterBankRun.Run positive g.global.nextPointerTag h.output.ended g.initial instructions g.global g.state ∧
    GeneralBorrowRetainedMutableAncestorHistory.Trace positive (GeneralBorrowRetainedMutableAncestorStack.initial (ofBank g.state g.global.nextPointerTag g.fresh)) g.global actions q.final q.advanced ∧
    s.tracker.global=q.advanced ∧
    let cfg := config s.options (s.remaining+1) s.span
    ∃ installed finalState,
      Call.initStackFrame (ExecutionMachine.callHooks cfg s.limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
          (Pointer.new (.concrete s.id s.parentTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm,
          ActualReferenceMetadata.reference⟩,.Copy (EmptyRootArguments.second count)] false (.memory s.place) (.stop true)
        ⟨⟨#[]⟩,s.before⟩=.ok () installed ∧
      SuccessfulTrace.Trace cfg s.limits installed finalState ∧
      ExecutionMachine.step cfg s.limits () finalState=(finalState,.ok false) ∧
      finalState.stack.frames=#[] ∧
      CallSafety.NoUBBeforeReturn
        (⟨cfg,s.limits,fun _ _=>True⟩ : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit)
        1 installed ∧
      (∀ before,SuccessfulTrace.Trace cfg s.limits installed before→
        ∃ after continuing,ExecutionMachine.step cfg s.limits () before=(after,.ok continuing)) := by
  let h := sourcePrefix bytes nonzero windows instructions (by omega)
  let g := bankPrefix bytes nonzero windows offset len positive bounds instructions choices actions room reserve reserveAbove
  let q := branched bytes nonzero windows offset len positive bounds instructions choices actions room reserve reserveAbove validActions
  have fresh := GeneralBorrowProtectedSiblingGenerationBounds.map_fresh _ _ q.below q.advanced.nextPointerTag (Nat.le_refl _)
  have reserved : ∀ i,GeneralBorrowTagMap.Fresh q.final.current.state.tree.tagMapping (reserve i) := by
    intro i
    apply GeneralBorrowProtectedSiblingGenerationBounds.map_fresh _ _ q.below
    rw [q.counter,g.counter]
    have bound:=reserveAbove i
    omega
  refine ⟨h.actual,h.released,g.sameTree,g.history,q.actual,s.globalEq,?_⟩
  exact GeneralBorrowForestFunctionSafety.invoke q.final.current.state.tree GeneralBorrowFullSharedSeed.root q.final.current.state.resources
    q.final.current.tag q.advanced.nextPointerTag offset len (GeneralBorrowRetainedMutableAccess.entryData q.final.current.state q.advanced.nextPointerTag fresh)
    reserve reserved (GeneralBorrowProtectedSiblingBankCaller.to_forest s q.empty) count
end
end DuplicatePrefix.GeneralBorrowRetainedMutableAncestorFunctionSafety
