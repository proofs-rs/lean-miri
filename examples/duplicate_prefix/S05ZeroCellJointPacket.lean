import duplicate_prefix.S05ZeroCellCorrelatedWrite
import duplicate_prefix.DuplicatePrefixSliceArgument
import Miri.Input.InitialMachine

/-! One closed call-time machine packet. This is initial data for a finite
joint interpretation, not a metadata-changing step or a whole-history claim.
Runtime allocation IDs are chosen above the fixed imported identity world;
all caller-visible bytes, pointers, roots and address entries are explicit. -/
namespace DuplicatePrefix.S05ZeroCellJointPacket
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.Input
open Miri.TreeBorrows Miri.Concurrency Miri.Memory.AllocAddresses
open S05ZeroCellTypedGeneratedPrefix
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option cbv.maxSteps 2000000
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

private def checked {E A : Type} : (result : Except E A) → result.isOk = true → A
  | .ok value, _ => value
  | .error _, impossible => False.elim (by cases impossible)

def sourceId : AllocId := ⟨719,by decide⟩
def destinationId : AllocId := ⟨720,by decide⟩

theorem initial_supply : PreparedReflection.actual.initialMemory.nextAllocId = 719 := rfl

def sourceAllocation : Allocation Provenance BorrowTree := S05ZeroCellCorrelatedWrite.sourceFor w.tree
def destinationAllocation : Allocation Provenance BorrowTree :=
  ((Allocation.fromBytes (Prov := Provenance) #[0] Align.ONE .Mut).toOption.get (by decide)).withExtra
    (BorrowTree.new (tag 7) (Size.ofBytes 1))
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

/-- Both allocations coexist in one fixed-catalog machine. Root7 is distinct
from the six source tags, and the next available tag is 8. This describes the
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
    borrowTracker := some ⟨{nextPointerTag := tag 8,rootPointerTags := #[(sourceId,tag 1),(destinationId,tag 7)]},.Default⟩}

noncomputable def state : MachineHooks.State MiriMemoryKind Machine.RootUser := ⟨⟨#[]⟩,before⟩
noncomputable def sourcePointer : Pointer Provenance := Pointer.new (.concrete sourceId (tag 6)) (Size.ofBytes 4096)
noncomputable def destinationPointer : Pointer Provenance := Pointer.new (.concrete destinationId (tag 7)) (Size.ofBytes 8192)
noncomputable def argument : DuplicatePrefixSliceArgument.Argument := .pointer sourcePointer
noncomputable def argumentValue2 : RvalueImmTy Provenance :=
  RetagReferencePlace.sliceValue PreparedReflection.actual.runtime.target.base sourcePointer 2 RootCompilerFacts.sliceLayout
noncomputable def place : MPlaceTy Provenance :=
  ⟨⟨destinationPointer.withOptionalProvenance,.none,none⟩,RootCompilerFacts.boolLayout⟩

theorem distinct_ids : sourceId ≠ destinationId := by decide +kernel

theorem source_present : before.memory.live.find? (fun row => row.1 == sourceId) = some (sourceId,sourceEntry) := by
  change memory.live.find? (fun row => row.1 == sourceId) = some (sourceId,sourceEntry)
  simp [memory]

theorem destination_present : before.memory.live.find? (fun row => row.1 == destinationId) = some (destinationId,destinationEntry) := by
  change memory.live.find? (fun row => row.1 == destinationId) = some (destinationId,destinationEntry)
  simp [memory,distinct_ids]

theorem live_entries : before.memory.live = #[(sourceId,sourceEntry),(destinationId,destinationEntry)] := rfl

theorem source_tree : sourceEntry.allocation.extra = w.tree := rfl

theorem destination_tree : destinationEntry.allocation.extra = BorrowTree.new (tag 7) (Size.ofBytes 1) := rfl

theorem next_tag : before.borrowTracker.map (fun tracker => tracker.global.nextPointerTag) = some (tag 8) := rfl

theorem no_protectors : before.borrowTracker.map (fun tracker => tracker.global.protectedTags) = some ({} : ProtectedTags) := rfl

theorem source_cached : before.user.addresses.baseAddr.find? (fun row => row.allocId == sourceId) = some ⟨sourceId,4096⟩ := by rfl

theorem destination_cached : before.user.addresses.baseAddr.find? (fun row => row.allocId == destinationId) = some ⟨destinationId,8192⟩ := by rfl

theorem inverse_addresses : before.user.addresses.intToPtrMap = #[⟨4096,sourceId⟩,⟨8192,destinationId⟩] := rfl

theorem source_exposed : before.user.addresses.exposed = #[sourceId] := rfl

theorem canonical_types : before.user.payload.payload.user.types = PreparedReflection.actual.types := rfl

theorem current_metadata : before.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime := rfl

theorem profile : before.user.payload.ghost = false ∧ before.user.payload.validation = .Shallow ∧
    before.user.payload.alignment = .Int ∧ before.dataRace = none ∧
    before.user.payload.payload.user.backend = .none ∧ before.threads.fixedScheduling = true ∧
    before.user.payload.payload.user.host.control.checkedArithmetic = false ∧
    before.user.payload.payload.user.host.control.gcInterval = 0 := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem empty_stack : state.stack.frames = #[] := rfl

theorem source_extras : before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == sourceId) =
    some (sourceId,⟨none,#[]⟩) := rfl

theorem destination_extras : before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == destinationId) =
    some (destinationId,⟨none,#[]⟩) := rfl

theorem next_allocation : before.memory.nextAllocId = 721 := rfl

theorem issued_ids : before.memory.issuedIds = PreparedReflection.actual.memoryData.issuedIds ++ #[sourceId,destinationId] := rfl


theorem imported_issued_bounded :
    PreparedReflection.actual.memoryData.issuedIds.all (fun id => id.value < 719) = true := by decide +kernel

theorem imported_globals_bounded :
    PreparedReflection.actual.memoryData.globals.all (fun row => row.allocId.value < 719) = true := by decide +kernel

theorem source_is_issued : sourceId ∈ before.memory.issuedIds := by rw [issued_ids]; simp

theorem destination_is_issued : destinationId ∈ before.memory.issuedIds := by rw [issued_ids]; simp

theorem live_id_bounds : sourceId.value < before.memory.nextAllocId ∧ destinationId.value < before.memory.nextAllocId := by
  change (719 : UInt64) < 721 ∧ (720 : UInt64) < 721
  decide


end DuplicatePrefix.S05ZeroCellJointPacket

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05ZeroCellJointPacket." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved closed joint packet dependency {dependency}"
