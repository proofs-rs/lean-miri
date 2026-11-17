import duplicate_prefix.CurrentCallConversionBoolFacts
import duplicate_prefix.CurrentCallOtherAllocationWindow

/-! Pure metadata/control frames of the SAME actual shared Bool result. -/
namespace DuplicatePrefix.CurrentCallConversionBoolModel
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open CandidateCurrentJointCall CanonicalConfigFacts ActualReferenceContext
open CurrentCallConversionBoolPhase CurrentCallConversionSourceCopy
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
noncomputable section

structure Fields (before after : Before) : Prop where
  threads : after.threads=before.threads
  race : after.dataRace=before.dataRace
  ghost : after.user.payload.ghost=before.user.payload.ghost
  validation : after.user.payload.validation=before.user.payload.validation
  backend : after.user.payload.payload.user.backend=before.user.payload.payload.user.backend
  types : after.user.payload.payload.user.types=before.user.payload.payload.user.types
  control : ∀options remaining span,(config options remaining span).terminators.getControl after.user=
    (config options remaining span).terminators.getControl before.user

variable {options : EvalConfigurationCore.Options} {remaining : Nat} {span : PreparedContracts.FixedSpanQuery}
variable {machine : Before} {tracker : MachineHooks.BorrowState}
variable {frames : Array CompilerFrameContext.ActualFrame} {frame : CompilerFrameContext.ActualFrame}
variable {borrowFrame : FrameState} {place : MPlaceTy Provenance}
variable {D : CurrentData machine tracker frames frame borrowFrame place}
variable {externStatic : Miri.MIR.DefId→MachineAddress.M MiriMemoryKind CurrentCallConversionFiniteFold.Control (Pointer Provenance)}
variable {tail : List AllocId} {charge reserve : Nat} {finalAddresses : Miri.Memory.AllocAddresses.GlobalAddressState}
variable {finalTape : ExecutionChoices.Tape}
variable {result : CurrentCallConversionFiniteFold.Result D.source PreparedReflection.actual.compiler.runtime.target.base
  (CurrentCallConversionActualEnsure.hooks options).address externStatic D.registered.machine D.next
  tail charge reserve finalAddresses finalTape}

/-- Conversion may change addresses, choices, caches and extras; the actual
Bool result retains all of these unrelated Model/control fields. -/
theorem fields (O : Protected (options:=options) (remaining:=remaining) (span:=span) D externStatic tail charge reserve finalAddresses finalTape result) :
    Fields machine O.post.machine := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  all_goals first
    | (intro opts fuel query; rw [(CanonicalConfigFacts.actual_fields opts () fuel query).terminators];
       rw [O.machineEq,result.frame,CurrentCallConversionFiniteFold.state_eq]; rfl)
    | (rw [O.machineEq,result.frame,CurrentCallConversionFiniteFold.state_eq]; rfl)

private theorem model_frame {options modelRemaining span before after old next}
    (F : Fields before after) (enabled : before.borrowTracker=some old)
    (tracked : after.borrowTracker=some next) (mode : next.retagMode=old.retagMode)
    (model : DuplicatePrefixCallModel.Model options modelRemaining span before) :
    DuplicatePrefixCallModel.Model options modelRemaining span after := by
  have defaultMode : old.retagMode=.Default := by
    obtain ⟨prior,live,mode⟩:=model.defaultTracker
    have equal:=Option.some.inj (enabled.symm.trans live)
    exact equal.symm ▸ mode
  refine ⟨model.debugOff,model.preciseOff,model.implicitOff,?_,?_,⟨next,tracked,mode.trans defaultMode⟩,?_,?_,?_,?_,?_,?_,model.nullComparator,model.sourceMatches⟩
  · rw [F.ghost];exact model.ghostOff
  · rw [F.validation];exact model.shallow
  · rw [F.race];exact model.noDataRace
  · rw [F.backend];exact model.noBackend
  · rw [F.types];exact model.metadata
  · rw [F.threads];exact model.fixedScheduler
  · rw [F.control];exact model.unchecked
  · rw [F.control];exact model.noGc

theorem model {modelRemaining : Nat}
    (O : Protected (options:=options) (remaining:=remaining) (span:=span) D externStatic tail charge reserve finalAddresses finalTape result)
    (beforeModel : DuplicatePrefixCallModel.Model options modelRemaining span machine) :
    DuplicatePrefixCallModel.Model options modelRemaining span O.post.machine :=
  CurrentCallConversionBoolFacts.model D externStatic tail charge reserve finalAddresses finalTape result O beforeModel (by
    obtain ⟨old,enabled,mode⟩:=beforeModel.defaultTracker
    have equal:=Option.some.inj (D.enabled.symm.trans enabled)
    exact equal.symm ▸ mode)

theorem origins
    (O : Protected (options:=options) (remaining:=remaining) (span:=span) D externStatic tail charge reserve finalAddresses finalTape result)
    (beforeOrigins : DuplicatePrefixTypeCacheOrigins.Origins machine.user.payload.payload.user.types) :
    DuplicatePrefixTypeCacheOrigins.Origins O.post.machine.user.payload.payload.user.types := by
  exact CurrentCallConversionBoolFacts.origins D externStatic tail charge reserve finalAddresses finalTape result O beforeOrigins

theorem threads
    (O : Protected (options:=options) (remaining:=remaining) (span:=span) D externStatic tail charge reserve finalAddresses finalTape result) :
    O.post.machine.threads=machine.threads := CurrentCallConversionBoolFacts.threads D externStatic tail charge reserve finalAddresses finalTape result O

theorem addresses
    (O : Protected (options:=options) (remaining:=remaining) (span:=span) D externStatic tail charge reserve finalAddresses finalTape result) :
    O.post.machine.user.addresses=result.addresses := by
  exact CurrentCallConversionBoolFacts.addresses D externStatic tail charge reserve finalAddresses finalTape result O

theorem base_hit
    (O : Protected (options:=options) (remaining:=remaining) (span:=span) D externStatic tail charge reserve finalAddresses finalTape result)
    (id : AllocId) (base : Miri.Memory.AllocAddresses.BaseAddressEntry)
    (cached : machine.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some base) :
    O.post.machine.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some base := by
  rw [addresses O];exact result.bases id base cached

theorem memory_other
    (O : Protected (options:=options) (remaining:=remaining) (span:=span) D externStatic tail charge reserve finalAddresses finalTape result)
    (id : AllocId) (different : id≠D.family.allocation) :
    O.post.machine.memory.live.find? (fun row=>row.1==id)=machine.memory.live.find? (fun row=>row.1==id) := by
  rw [CurrentCallConversionBoolFacts.live D externStatic tail charge reserve finalAddresses finalTape result O]
  exact CurrentCallOtherAllocationWindow.lookup _ _ _ _ (Ne.symm different)

theorem extras_other
    (O : Protected (options:=options) (remaining:=remaining) (span:=span) D externStatic tail charge reserve finalAddresses finalTape result)
    (id : AllocId) (different : id≠D.family.allocation) :
    O.post.machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row=>row.1==id)=
      machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row=>row.1==id) := by
  rw [CurrentCallConversionBoolFacts.extras D externStatic tail charge reserve finalAddresses finalTape result O]
  exact CurrentCallOtherAllocationWindow.lookup _ _ _ _ (Ne.symm different)

private theorem replace_twice {α : Type} (rows : Array (AllocId×α)) (id : AllocId) (first second : α) :
    ((((rows.filter (fun row=>row.1!=id)).push (id,first)).filter (fun row=>row.1!=id)).push (id,second))=
      (rows.filter (fun row=>row.1!=id)).push (id,second) := by simp [Array.filter_filter]

theorem memory
    (O : Protected (options:=options) (remaining:=remaining) (span:=span) D externStatic tail charge reserve finalAddresses finalTape result) :
    O.post.machine.memory={machine.memory with live := (machine.memory.live.filter (fun row=>row.1!=D.family.allocation)).push (D.family.allocation,⟨.machine .global,O.output.window.allocation⟩)} := by
  have registeredMemory : D.registered.machine.memory=machine.memory := rfl
  have actual:=congrArg (fun state : Before=>state.memory) O.machineEq
  rw [result.frame,CurrentCallConversionFiniteFold.state_eq] at actual
  simpa only [childMachine,rootMachine,CurrentCallConversionMaterialize.installed,RetagEntry.updatedMemory,
    MemoryExtras.putAllocation,replace_twice,registeredMemory] using actual

variable {L : LiveData machine tracker frame borrowFrame place}

theorem live_fields
    (O : LiveProtected (options:=options) (remaining:=remaining) (span:=span) L frames) :
    Fields machine O.post.machine := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  all_goals first
    | (intro opts fuel query;rw [(CanonicalConfigFacts.actual_fields opts () fuel query).terminators];rw [O.machineEq];rfl)
    | (rw [O.machineEq];rfl)

theorem live_model {modelRemaining : Nat}
    (O : LiveProtected (options:=options) (remaining:=remaining) (span:=span) L frames)
    (beforeModel : DuplicatePrefixCallModel.Model options modelRemaining span machine) :
    DuplicatePrefixCallModel.Model options modelRemaining span O.post.machine :=
  model_frame (live_fields O) L.enabled O.tracked rfl beforeModel

theorem live_origins
    (O : LiveProtected (options:=options) (remaining:=remaining) (span:=span) L frames)
    (beforeOrigins : DuplicatePrefixTypeCacheOrigins.Origins machine.user.payload.payload.user.types) :
    DuplicatePrefixTypeCacheOrigins.Origins O.post.machine.user.payload.payload.user.types := by
  rw [(live_fields O).types];exact beforeOrigins

theorem live_threads
    (O : LiveProtected (options:=options) (remaining:=remaining) (span:=span) L frames) :
    O.post.machine.threads=machine.threads := (live_fields O).threads

theorem live_addresses
    (O : LiveProtected (options:=options) (remaining:=remaining) (span:=span) L frames) :
    O.post.machine.user.addresses=machine.user.addresses := by rw [O.machineEq];rfl

end
end DuplicatePrefix.CurrentCallConversionBoolModel
