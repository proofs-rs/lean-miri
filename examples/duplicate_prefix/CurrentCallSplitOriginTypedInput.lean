import duplicate_prefix.CurrentCallSplitOriginTrace
import duplicate_prefix.CurrentCallTypedSourceOperation
import duplicate_prefix.RawRootInvocation
import duplicate_prefix.OrdinaryPhysicalValidity
import Miri.Input.InitialMachine

/-! A constructed CURRENT machine packet using the fixed 718-ID catalog.
The source tree is the actual completed split-origin trace; the byte storage
comes from actual checked allocation constructors. This does not assert a
historical Rust execution or whole-function admission. -/
namespace DuplicatePrefix.CurrentCallSplitOriginTypedInput
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.Input
open Miri.TreeBorrows Miri.Concurrency Miri.Memory.AllocAddresses
open CurrentCallSplitOriginTrace (tag)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option cbv.maxSteps 4000000
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail
noncomputable section

private def checked {E A : Type} : (result : Except E A) → result.isOk = true → A
  | .ok value, _ => value
  | .error _, impossible => False.elim (by cases impossible)

def sourceId : AllocId := ⟨719,by decide⟩
def destinationId : AllocId := ⟨720,by decide⟩

theorem initial_supply : PreparedReflection.actual.initialMemory.nextAllocId = 719 := rfl

/-- Actual checked allocation constructors, with explicit zero-storage backend. -/
def zeroedStorage (size : Size) (_align : Align) : Option (Array UInt8) := some (Array.replicate size.bytes.toNat 0)
def sourceCreated := Allocation.tryNew (Prov:=Provenance) (Size.ofBytes 2) Align.ONE .Zero zeroedStorage
def destinationCreated := Allocation.tryNew (Prov:=Provenance) (Size.ofBytes 1) Align.ONE .Uninit zeroedStorage
def sourceBase : Allocation Provenance Unit := sourceCreated.toOption.get (by decide +kernel)
def destinationBase : Allocation Provenance Unit := destinationCreated.toOption.get (by decide +kernel)
def sourceAllocation : Allocation Provenance BorrowTree := sourceBase.withExtra CurrentCallSplitOriginTrace.finalWrite.tree
def destinationAllocation : Allocation Provenance BorrowTree := destinationBase.withExtra (BorrowTree.new (tag 5) (Size.ofBytes 1))
def sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind := ⟨.machine .rust,sourceAllocation⟩
def destinationEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind := ⟨.machine .rust,destinationAllocation⟩

noncomputable def memory : MemoryState Provenance BorrowTree MiriMemoryKind :=
  {PreparedReflection.actual.initialMemory.setIssuedIds
      (PreparedReflection.actual.memoryData.issuedIds ++ #[sourceId,destinationId]) with
    nextAllocId := 721
    live := #[(sourceId,sourceEntry),(destinationId,destinationEntry)]}

def host : Machine.MinimalHost where
  control := ⟨0,0,0,.virtual 0,0,false⟩
  ioSources := #[]


noncomputable def initialization : InitialMachine.Configuration Unit Unit where
  geometry := ⟨4096,12288,65536⟩
  dummySpan := PreparedReflection.actual.dummySpan
  provenance := .permissive
  addressMode := .managed
  addressStop := 9223372036854775807
  addressReuse := ⟨0,0⟩
  fixedScheduling := true
  trackOutdatedLoads := false
  weakMemory := false
  backend := .none
  trackedTags := some #[]
  validation := .Shallow
  alignment := .Int
  affinity := none
  muteOutput := true
  hostUsizeBits := 64

noncomputable def initialized : Except StepError (EvalWorld.State Unit Unit Unit Unit Unit Unit Unit Unit Machine.MinimalHost) :=
  InitialMachine.create initialization memory PreparedReflection.actual.types {inputs := #[]} host
private theorem initialized_ok : initialized.isOk = true := by
  have supported (m : MemoryState Provenance BorrowTree MiriMemoryKind) (t : RuntimeArrayTypes.World) :
      (InitialMachine.create (Os:=Unit) (R:=Unit) (P:=Unit) (H:=Unit) (D:=Unit) (O:=Unit)
        initialization m t {inputs := #[]} host).isOk = true := by
    cbv
  exact supported memory PreparedReflection.actual.types
noncomputable def initialState := checked initialized initialized_ok

/-- Both allocations coexist in one fixed-catalog machine. Root5 is distinct
from the four actual source tags, and the next available tag is 6. This describes the
call-time snapshot; it does not assert a synthetic increment as an operation. -/
noncomputable def before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser :=
  let machine := (ExecutionStateTransport.inward initialState).machine
  let addresses : GlobalAddressState := {
    baseAddr := #[⟨sourceId,4096⟩,⟨destinationId,8192⟩]
    intToPtrMap := #[⟨4096,sourceId⟩,⟨8192,destinationId⟩]
    exposed := #[sourceId]
    provenanceMode := .permissive
    addressMode := .managed
    generation := some ⟨⟨12288,9223372036854775807⟩,⟨0,0,#[]⟩⟩ }
  let runtime := {machine.user.payload.payload.user.runtime with
    extras := {allocations := #[(sourceId,⟨none,#[]⟩),(destinationId,⟨none,#[]⟩)]}}
  let world := {machine.user.payload.payload.user with runtime,types := PreparedReflection.actual.types,backend := .none,host := host,choices := {inputs := #[]}}
  let stored := {machine.user.payload.payload with
    registry := ⟨ThreadId.MAIN_THREAD,#[]⟩
    identitySupply := ⟨0⟩
    user := world}
  let user := {machine.user with
    addresses := addresses
    payload := {machine.user.payload with payload := stored,validation := .Shallow,alignment := .Int,ghost := false,unionDataRanges := #[]}}
  let threads := ThreadManager.initial true
  let threads := {threads with threads := threads.threads.map fun thread =>
    {thread with originSpanToken := PreparedReflection.actual.dummySpan.id}}
  {machine with
    memory := memory
    user := user
    threads := threads
    dataRace := none
    raceAllocations := #[]
    allocationSpans := #[(sourceId,PreparedReflection.actual.dummySpan,none),(destinationId,PreparedReflection.actual.dummySpan,none)]
    borrowTracker := some ⟨{nextPointerTag := tag 6,rootPointerTags := #[(sourceId,tag 1),(destinationId,tag 5)]},.Default⟩}


def tracker : MachineHooks.BorrowState := ⟨{nextPointerTag:=tag 6,rootPointerTags:=#[(sourceId,tag 1),(destinationId,tag 5)]},.FnEntry⟩
def sourcePointer : Pointer Provenance := Pointer.new (.concrete sourceId (tag 4)) (Size.ofBytes 4096)
def destinationPointer : Pointer Provenance := Pointer.new (.concrete destinationId (tag 5)) (Size.ofBytes 8192)
def place : MPlaceTy Provenance := ⟨⟨destinationPointer.withOptionalProvenance,.none,none⟩,RootCompilerFacts.boolLayout⟩
def machine := RawRootInvocation.machine #[] {before with borrowTracker:=some tracker}
def root := RawRootInvocation.root {before with borrowTracker:=some tracker} place (by rfl)
def state := Storage.withCurrent #[] root.frame machine

theorem source_constructor : sourceCreated=.ok sourceBase := by cbv
theorem destination_constructor : destinationCreated=.ok destinationBase := by cbv

theorem source_physical : OrdinaryPhysicalValidity.MutU8Slice sourceAllocation 0 2 := by
  refine ⟨⟨by cbv,by cbv,by cbv,?_⟩,by cbv,by cbv,by cbv,by cbv,?_⟩
  · have fields : sourceAllocation.provenanceMap=ProvenanceMap.new ∧ sourceAllocation.len=2 := by cbv
    rw [fields.1,fields.2]
    constructor <;> simp [ProvenanceMap.new,ProvenanceCopy.FragmentsAvoidPointers]
  · intro index lower upper
    cbv

theorem destination_physical : OrdinaryPhysicalValidity.BoolDestination destinationAllocation 0 := by
  refine ⟨⟨by cbv,by cbv,by cbv,?_⟩,by cbv,by cbv⟩
  have fields : destinationAllocation.provenanceMap=ProvenanceMap.new ∧ destinationAllocation.len=1 := by cbv
  rw [fields.1,fields.2]
  constructor <;> simp [ProvenanceMap.new,ProvenanceCopy.FragmentsAvoidPointers]

theorem destination_uninitialized : destinationAllocation.initializationMask=InitMask.new (Size.ofBytes 1) false := by cbv

theorem source_present : machine.memory.live.find? (fun row=>row.1==sourceId)=some (sourceId,sourceEntry) := by
  change memory.live.find? (fun row=>row.1==sourceId)=some (sourceId,sourceEntry)
  simp [memory]
theorem destination_present : machine.memory.live.find? (fun row=>row.1==destinationId)=some (destinationId,destinationEntry) := by
  change memory.live.find? (fun row=>row.1==destinationId)=some (destinationId,destinationEntry)
  simp [memory,sourceId,destinationId]
theorem source_binding : CandidateCallBindings.WindowBinding machine sourcePointer sourceId 0 2 := by
  exact ⟨sourceEntry,4096,source_present,rfl,by cbv,by cbv,by cbv,by decide,by decide,rfl⟩
theorem destination_binding : CandidateCallBindings.WindowBinding machine destinationPointer destinationId 0 1 := by
  exact ⟨destinationEntry,8192,destination_present,rfl,by cbv,by cbv,by cbv,by decide,by decide,rfl⟩
theorem frame_borrow : root.frame.extra.borrowTracker=some ({} : FrameState) :=
  RawRootInvocation.frame_borrow _ place (by rfl) tracker rfl

theorem fixed_metadata : machine.user.payload.payload.user.types=PreparedReflection.actual.types := rfl

theorem catalog_ids_bounded :
    PreparedReflection.actual.memoryData.issuedIds.all (fun id=>id.value<719)=true ∧
    PreparedReflection.actual.memoryData.globals.all (fun row=>row.allocId.value<719)=true := by decide +kernel

theorem current_supply : machine.memory.nextAllocId=721 ∧
    machine.memory.issuedIds=PreparedReflection.actual.memoryData.issuedIds++#[sourceId,destinationId] ∧
    machine.borrowTracker=some tracker ∧ tracker.global.nextPointerTag=tag 6 ∧
    tracker.global.rootPointerTags=#[(sourceId,tag 1),(destinationId,tag 5)] := ⟨rfl,rfl,rfl,rfl,rfl⟩

end
end DuplicatePrefix.CurrentCallSplitOriginTypedInput
open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallSplitOriginTypedInput" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved split-origin machine dependency {dependency}"
