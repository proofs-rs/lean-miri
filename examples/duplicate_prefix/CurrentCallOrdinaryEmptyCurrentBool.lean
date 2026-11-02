import duplicate_prefix.CurrentCallOrdinaryEmptyCurrentState
import duplicate_prefix.CurrentCallConversionBoolPhase
import duplicate_prefix.CurrentCallConversionTargetMetadataFrame
namespace DuplicatePrefix.CurrentCallOrdinaryEmptyCurrentBool
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CandidateCurrentJointCall CurrentCallOrdinaryInput CanonicalConfigFacts ActualReferenceContext ActualReferenceMetadata
open RootFrameData EmptyRootArguments TypedBorrowSteps ReferenceBorrowDriver
open CurrentCallOrdinaryEmptyCurrentState
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
noncomputable section
variable {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits} {remaining : Nat}
    {span : PreparedContracts.FixedSpanQuery} {before : Before} {argument : DuplicatePrefixSliceArgument.Argument}
    {place : MPlaceTy Provenance}
    (input : OrdinaryInput options limits remaining span before argument 0 place)
    (id : AllocId) (pointer : Pointer Provenance) (root : BorTag)
    (source : Allocation CtfeProvenance Unit)
    (externStatic : Miri.MIR.DefId→MachineAddress.M MiriMemoryKind CurrentCallConversionFiniteFold.Control (Pointer Provenance))
    (tail : List AllocId) (finalAddresses : Miri.Memory.AllocAddresses.GlobalAddressState) (finalTape : ExecutionChoices.Tape)
    (result : CurrentCallConversionFiniteFold.Result source PreparedReflection.actual.compiler.runtime.target.base
      (CurrentCallConversionActualEnsure.hooks options).address externStatic
      (CurrentCallOrdinaryEmptyCurrentCopy.registered input id pointer).machine
      (CurrentCallOrdinaryEmptyCurrentCopy.nextTracker input) tail (addressCharge before) 15 finalAddresses finalTape)
    (tree : BorrowTree)

def reindex (newTail : List AllocId) (eq : tail=newTail) :
    CurrentCallConversionFiniteFold.Result source PreparedReflection.actual.compiler.runtime.target.base
      (CurrentCallConversionActualEnsure.hooks options).address externStatic
      (CurrentCallOrdinaryEmptyCurrentCopy.registered input id pointer).machine
      (CurrentCallOrdinaryEmptyCurrentCopy.nextTracker input) newTail (addressCharge before) 15 finalAddresses finalTape := eq ▸result

theorem reindex_fields (newTail : List AllocId) (eq : tail=newTail) :
    (reindex input id pointer source externStatic tail finalAddresses finalTape result newTail eq).global=result.global ∧
    (reindex input id pointer source externStatic tail finalAddresses finalTape result newTail eq).addresses=result.addresses ∧
    (reindex input id pointer source externStatic tail finalAddresses finalTape result newTail eq).tape=result.tape := by
  cases eq
  exact ⟨rfl,rfl,rfl⟩

theorem current_data
    (latent : LatentRole before input.tracker input.returnFamily input.returnOffset 1 input.returnCapacity false)
    (different : input.returnFamily.allocation≠id)
    (frame : CompilerFrameContext.ActualFrame) (borrow : FrameState)
    (frameBorrow : frame.extra.borrowTracker=some borrow) :
    let post:=closed options result.machine id root result.converted tree result.global input.tracker.retagMode
    ∃D : CurrentCallConversionBoolPhase.CurrentData post ⟨result.global,input.tracker.retagMode⟩ #[] frame borrow place,
      D.family=input.returnFamily ∧D.offset=input.returnOffset ∧CurrentPayload before input.returnFamily.allocation D.source := by
  let post:=closed options result.machine id root result.converted tree result.global input.tracker.retagMode
  have m:=model input id pointer root source externStatic tail finalAddresses finalTape result tree
  have absent : post.memory.live.find? (fun row=>row.1==input.returnFamily.allocation)=none :=
    (live_other input id pointer root source externStatic tail finalAddresses finalTape result tree _ different).trans latent.1
  have baseEq : post.user.addresses.baseAddr.find? (fun row=>row.allocId==input.returnFamily.allocation)=before.user.addresses.baseAddr.find? (fun row=>row.allocId==input.returnFamily.allocation) := by
    obtain ⟨b,cached,_⟩:=input.returnRepresentation
    rw [addresses,cached]
    exact result.bases _ _ cached
  have roots : result.global.rootTag? input.returnFamily.allocation=input.tracker.global.rootTag? input.returnFamily.allocation := by
    obtain ⟨tag,_,cached⟩:=latent.2.2.2.2.1
    exact (result.roots _ _ cached).trans cached.symm
  apply CurrentCallConversionBoolPhase.from_initial input latent rfl frameBorrow
    (fresh input id pointer source externStatic tail finalAddresses finalTape result) absent
    (by rw [heap];rfl) (by rw [heap];rfl) (by rw [heap];rfl) baseEq roots
  · intro tag cached
    exact root_below input id pointer tag source externStatic tail finalAddresses finalTape result (cached_below input _ _ cached)
  · exact protectors input id pointer source externStatic tail finalAddresses finalTape result
  · exact extras_absent input id pointer root source externStatic tail finalAddresses finalTape result tree _ different latent.2.2.2.1
  · exact m.noDataRace
  · exact m.ghostOff
  · exact m.noBackend


theorem next_phase
    (frame : CompilerFrameContext.ActualFrame) (borrow : FrameState)
    (D : CurrentCallConversionBoolPhase.CurrentData
      (closed options result.machine id root result.converted tree result.global input.tracker.retagMode)
      ⟨result.global,input.tracker.retagMode⟩ #[] frame borrow place)
    (sourceCurrent : CurrentPayload before id source)
    (absent : before.memory.live.find? (fun row=>row.1==id)=none)
    (noFunction : before.memory.hasFunctionPointer id=false) (noVaList : before.memory.hasVaListId id=false)
    (base : UInt64) (cached : before.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩)
    (second : Allocation CtfeProvenance Unit) (secondEq : D.source=second)
    (rest : List (Allocation CtfeProvenance Unit))
    (head : CurrentCallConversionPlan.selectedPayloads before argument 0 place=source::second::rest)
    (tailEq : tail=CurrentCallConversionFiniteFold.targets second++rest.flatMap CurrentCallConversionFiniteFold.targets)
    (wiring : (CurrentCallConversionActualEnsure.hooks options).rootPointer=
      PointerSource.globalRootPointer EvalPointerSource.tape (CurrentCallConversionActualEnsure.hooks options).address externStatic) :
    ∃P : CurrentCallConversionBoolPhase.NextPhase input D,P.reserve=14 := by
  subst tail
  let entry : LocalAllocation Provenance BorrowTree MiriMemoryKind:=⟨.machine .global,result.converted.mapExtra (fun _=>tree)⟩
  have memoryEq : D.registered.machine.memory=CurrentCallConversionTargetMetadataFrame.heap before.memory id entry :=
    heap input id pointer root source externStatic _ finalAddresses finalTape result tree
  have bases : ∀query value,before.user.addresses.baseAddr.find? (fun row=>row.allocId==query)=some value→D.registered.machine.user.addresses.baseAddr.find? (fun row=>row.allocId==query)=some value := by
    intro query value found
    change (closed options result.machine id root result.converted tree result.global input.tracker.retagMode).user.addresses.baseAddr.find? _=_
    rw [addresses]
    exact result.bases _ _ found
  have targetMeta : ∀query∈CurrentCallConversionFiniteFold.targets D.source,RelocationTargetMetadata D.registered.machine query := by
    intro query member
    have selected : query∈CurrentCallConversionPlan.selectedIds before argument 0 place := by
      unfold CurrentCallConversionPlan.selectedIds
      rw [head]
      simp only [List.flatMap_cons,List.mem_append]
      exact Or.inr (Or.inl (by simpa only [secondEq,CurrentCallConversionFiniteFold.targets_eq] using member))
    exact CurrentCallConversionTargetMetadataFrame.transport before D.registered.machine id entry memoryEq ⟨⟨id,base⟩,cached⟩ bases query
      (CurrentCallOrdinaryConversionSelected.targets_metadata input query selected)
  let previous:=reindex input id pointer source externStatic _ finalAddresses finalTape result
    (CurrentCallConversionFiniteFold.targets D.source++rest.flatMap CurrentCallConversionFiniteFold.targets)
    (congrArg (fun src=>CurrentCallConversionFiniteFold.targets src++rest.flatMap CurrentCallConversionFiniteFold.targets) secondEq.symm)
  obtain ⟨previousGlobal,previousAddresses,previousTape⟩:=reindex_fields input id pointer source externStatic _ finalAddresses finalTape result
    (CurrentCallConversionFiniteFold.targets D.source++rest.flatMap CurrentCallConversionFiniteFold.targets)
    (congrArg (fun src=>CurrentCallConversionFiniteFold.targets src++rest.flatMap CurrentCallConversionFiniteFold.targets) secondEq.symm)
  refine ⟨{
    initial:=(CurrentCallOrdinaryEmptyCurrentCopy.registered input id pointer).machine
    oldTracker:=CurrentCallOrdinaryEmptyCurrentCopy.nextTracker input
    firstSource:=source,rest:=rest,head:=by simpa only [secondEq] using head,externStatic:=externStatic,wiring:=wiring,oldReserve:=15
    finalAddresses:=finalAddresses,finalTape:=finalTape,previous:=previous
    initialInfo:=by intro query;rfl
    infoEq:=info input id pointer root source externStatic _ finalAddresses finalTape result tree sourceCurrent absent noFunction noVaList
    addresses:=by rw [previousAddresses];change (closed options result.machine id root result.converted tree result.global input.tracker.retagMode).user.addresses=result.addresses;exact addresses input id pointer root source externStatic _ finalAddresses finalTape result tree
    tape:=by rw [previousTape];change EvalPointerSource.tape.get result.machine=result.tape;rw [result.frame,CurrentCallConversionFiniteFold.state_eq];rfl
    thread:=by change (closed options result.machine id root result.converted tree result.global input.tracker.retagMode).threads.activeThread=_;rw [threads];rfl
    roots:=by intro query;rw [previousGlobal];rfl
    spent:=1,reserve:=14,room:=by decide,positive:=by decide
    counter:=by rw [previousGlobal];change (TypedRetagEmpty.successorTag result.global.nextPointerTag D.fresh).value.toNat≤_;rw [GenericFunctionEntryNumerics.successor_value];exact Nat.le_refl _
    bases:=bases,metadata:=targetMeta},rfl⟩

end
end DuplicatePrefix.CurrentCallOrdinaryEmptyCurrentBool
