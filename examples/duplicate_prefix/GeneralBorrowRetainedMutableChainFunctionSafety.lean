import duplicate_prefix.GeneralBorrowRetainedMutableChain
import duplicate_prefix.GeneralBorrowProtectedSiblingCounterBankFunctionSafety
import duplicate_prefix.GeneralBorrowProtectedSiblingCounterBankGrowth
namespace DuplicatePrefix.GeneralBorrowRetainedMutableChainFunctionSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open Miri.DataStructures Miri.TreeBorrows.Tree ActualReferenceContext
open GeneralBorrowProtectedSiblingPartial GeneralBorrowProtectedSiblingCounterBank
open GeneralBorrowProtectedSiblingCounterBankFunctionSafety GeneralBorrowRetainedMutableChain
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

def ofBank {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh s.bank.tree.tagMapping tag) : Current root offset len := by
  let d := GeneralBorrowSharedRootBankState.entryData s tag fresh
  exact ⟨root,rootTag,{
    tree:=s.bank.tree,resources:=s.bank.resources,node:=d.node,present:=d.parentPresent,lookup:=d.tagPresent,
    bounds:=s.bank.bounds,owned:=d.owned }⟩

def bankPrefix (bytes : UInt64) (nonzero : bytes≠0) (windows : List (Window bytes))
    (offset len : UInt64) (positive : len≠0) (bounds : offset.toNat+len.toNat≤bytes.toNat)
    (instructions : List Instruction) (choices : Choices 1 instructions) (rounds : List (List AccessKind))
    (room : windows.length+allocations instructions+rounds.length+10≤4294967295)
    (reserve : Fin 5→BorTag)
    (reserveAbove : ∀ i,windows.length+allocations instructions+rounds.length+2≤(reserve i).value.toNat) :=
  joined bytes nonzero windows offset len positive bounds instructions choices (by omega) reserve
    (by intro i;have h:=reserveAbove i;omega)

def chained (bytes : UInt64) (nonzero : bytes≠0) (windows : List (Window bytes))
    (offset len : UInt64) (positive : len≠0) (bounds : offset.toNat+len.toNat≤bytes.toNat)
    (instructions : List Instruction) (choices : Choices 1 instructions) (rounds : List (List AccessKind))
    (room : windows.length+allocations instructions+rounds.length+10≤4294967295)
    (reserve : Fin 5→BorTag)
    (reserveAbove : ∀ i,windows.length+allocations instructions+rounds.length+2≤(reserve i).value.toNat) := by
  let h := sourcePrefix bytes nonzero windows instructions (by omega)
  let g := bankPrefix bytes nonzero windows offset len positive bounds instructions choices rounds room reserve reserveAbove
  let initial := ofBank g.state g.global.nextPointerTag g.fresh
  have growth := GeneralBorrowProtectedSiblingCounterBankGrowth.run g.history
  have initialSize : g.initial.bank.tree.nodes.size=windows.length+1 := by rw [g.sameTree,h.nodes]
  have nodeRoom : initial.state.tree.nodes.size+rounds.length+4≤4294967295 := by
    change g.state.bank.tree.nodes.size+rounds.length+4≤_
    rw [initialSize] at growth
    omega
  have counterRoom : g.global.nextPointerTag.value.toNat+rounds.length≤4294967295 := by rw [g.counter];omega
  exact GeneralBorrowRetainedMutableChain.generate initial g.global positive rounds g.empty g.below nodeRoom counterRoom

/-- A source-generated protected/bank prefix is followed by any positive finite
depth of actual Default mutable reborrows. Each new counter-issued descendant
is activated by its own Write and becomes the current pointer; arbitrary
Read/Write sequences run through that current pointer before the next stage.
The final descendant, rather than an earlier root/child, supplies the original
all-count physical MIR invocation. This is a current-pointer chain protocol. -/
theorem invoke (bytes : UInt64) (nonzero : bytes≠0) (windows : List (Window bytes))
    (offset len : UInt64) (positive : len≠0) (bounds : offset.toNat+len.toNat≤bytes.toNat)
    (instructions : List Instruction) (choices : Choices 1 instructions)
    (first : List AccessKind) (rest : List (List AccessKind))
    (room : windows.length+allocations instructions+(first::rest).length+10≤4294967295)
    (reserve : Fin 5→BorTag)
    (reserveAbove : ∀ i,windows.length+allocations instructions+(first::rest).length+2≤(reserve i).value.toNat)
    (s : GeneralBorrowProtectedSiblingBankCaller.Caller
      (chained bytes nonzero windows offset len positive bounds instructions choices (first::rest) room reserve reserveAbove).current.state.tree
      (chained bytes nonzero windows offset len positive bounds instructions choices (first::rest) room reserve reserveAbove).current.tag
      (chained bytes nonzero windows offset len positive bounds instructions choices (first::rest) room reserve reserveAbove).advanced.nextPointerTag
      offset len reserve
      (chained bytes nonzero windows offset len positive bounds instructions choices (first::rest) room reserve reserveAbove).advanced)
    (count : UInt64) :
    let h := sourcePrefix bytes nonzero windows instructions (by omega)
    let g := bankPrefix bytes nonzero windows offset len positive bounds instructions choices (first::rest) room reserve reserveAbove
    let q := chained bytes nonzero windows offset len positive bounds instructions choices (first::rest) room reserve reserveAbove
    GeneralBorrowProtectedSiblingPartialFunctionHistory.operation bytes windows=.ok h.output ∧
    GeneralBorrowProtectedReleaseHistory.AllReleased h.output.generated.tree h.output.generated.global.protectedTags h.output.generated.tags ∧
    g.initial.bank.tree=h.output.tree ∧
    GeneralBorrowProtectedSiblingCounterBankRun.Run positive g.global.nextPointerTag h.output.ended g.initial instructions g.global g.state ∧
    Trace positive (ofBank g.state g.global.nextPointerTag g.fresh) g.global (first::rest) q.current q.advanced ∧
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
  let g := bankPrefix bytes nonzero windows offset len positive bounds instructions choices (first::rest) room reserve reserveAbove
  let q := chained bytes nonzero windows offset len positive bounds instructions choices (first::rest) room reserve reserveAbove
  have fresh := GeneralBorrowProtectedSiblingGenerationBounds.map_fresh _ _ q.below q.advanced.nextPointerTag (Nat.le_refl _)
  have reserved : ∀ i,GeneralBorrowTagMap.Fresh q.current.state.tree.tagMapping (reserve i) := by
    intro i
    apply GeneralBorrowProtectedSiblingGenerationBounds.map_fresh _ _ q.below
    rw [q.counter,g.counter]
    have bound:=reserveAbove i
    omega
  refine ⟨h.actual,h.released,g.sameTree,g.history,q.actual,s.globalEq,?_⟩
  exact GeneralBorrowForestFunctionSafety.invoke q.current.state.tree GeneralBorrowFullSharedSeed.root q.current.state.resources
    q.current.tag q.advanced.nextPointerTag offset len (GeneralBorrowRetainedMutableAccess.entryData q.current.state q.advanced.nextPointerTag fresh)
    reserve reserved (GeneralBorrowProtectedSiblingBankCaller.to_forest s q.empty) count
end
end DuplicatePrefix.GeneralBorrowRetainedMutableChainFunctionSafety
