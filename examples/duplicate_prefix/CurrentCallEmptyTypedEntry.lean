import duplicate_prefix.CurrentCallEmptyTypedEntryWildcardMiss
import duplicate_prefix.CurrentCallEmptyTypedEntryWildcardLive
import duplicate_prefix.CurrentCallEmptyTypedEntryWildcardNonlive
import duplicate_prefix.CurrentCallEmptyTypedEntryWildcardImage
import duplicate_prefix.CurrentCallEmptyTypedEntryImage

/-! Finite empty argument-entry dispatch from the original proposed domain.
The output retains actual branch effects for later Bool-only composition.
This is not a whole-call Result or ordinary-input coverage theorem. -/
namespace DuplicatePrefix.CurrentCallEmptyTypedEntry
open Miri Miri.ABI Miri.Memory Miri.Input Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CanonicalConfigFacts ActualReferenceContext ActualReferenceMetadata
open TypedBorrowSteps ReferenceBorrowDriver CurrentCallEmptyReferenceValidation
open DuplicatePrefixSliceArgument (Argument)
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- Actual finite branch output data. No constructor requires a source loan
or content origin; only the branches that touch a tree carry a live row. -/
inductive Effect (options : EvalConfigurationCore.Options) (before : Before) (tracker : MachineHooks.BorrowState) : Argument → Type where
  | integer (address : UInt64) : Effect options before tracker (.integer address)
  | miss (address : UInt64)
      (miss : before.user.addresses.allocIdFromAddr address 0 (GlobalAddressLiveErrorExclusion.lookup before.memory) = .ok none) :
      Effect options before tracker (.pointer (Pointer.new .wildcard (Size.ofBytes address)))
  | concreteLive (address : UInt64) (id : AllocId) (parent : BorTag)
      (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (tree : BorrowTree)
      (live : before.memory.live.find? (fun row => row.1 == id) = some (id,entry))
      (child : CurrentCallEmptyTypedEntryConcrete.ChildEffect before id parent address entry tracker.global.nextPointerTag tree) :
      Effect options before tracker (.pointer (Pointer.new (.concrete id parent) (Size.ofBytes address)))
  | concreteNonlive (address : UInt64) (id : AllocId) (parent : BorTag)
      (metadata : DuplicatePrefixEmptyReferenceInput.Metadata before.memory id (some parent))
      (absent : before.memory.live.find? (fun row => row.1 == id) = none) :
      Effect options before tracker (.pointer (Pointer.new (.concrete id parent) (Size.ofBytes address)))
  | concreteImage (address : UInt64) (id : AllocId) (parent : BorTag)
      (image : DuplicatePrefixEmptyReferenceInput.Materializable (DuplicatePrefixCallSpecification.imageContext options before tracker)
        before.memory before.user.addresses id (some parent))
      (source : Allocation CtfeProvenance Unit) (converted : Allocation Provenance Unit)
      (descriptor : DuplicatePrefixEmptyReferenceInput.ImageDescriptor (DuplicatePrefixCallSpecification.imageContext options before tracker)
        before.memory id source) (attributes : GlobalAllocationAttributes.Attributes source converted) :
      Effect options before tracker (.pointer (Pointer.new (.concrete id parent) (Size.ofBytes address)))
  | wildcardLive (address : UInt64)
      (hit : S03WildcardEmptyClassification.Hit (DuplicatePrefixCallSpecification.imageContext options before tracker)
        before.memory before.user.addresses address)
      (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (tree : BorrowTree)
      (live : before.memory.live.find? (fun row => row.1 == hit.id) = some (hit.id,entry))
      (child : CurrentCallEmptyTypedEntryWildcardLive.ChildEffect entry tracker.global.nextPointerTag tree) :
      Effect options before tracker (.pointer (Pointer.new .wildcard (Size.ofBytes address)))
  | wildcardNonlive (address : UInt64)
      (hit : S03WildcardEmptyClassification.Hit (DuplicatePrefixCallSpecification.imageContext options before tracker)
        before.memory before.user.addresses address)
      (metadata : DuplicatePrefixEmptyReferenceInput.Metadata before.memory hit.id none)
      (absent : before.memory.live.find? (fun row => row.1 == hit.id) = none) :
      Effect options before tracker (.pointer (Pointer.new .wildcard (Size.ofBytes address)))
  | wildcardImage (address : UInt64)
      (hit : S03WildcardEmptyClassification.Hit (DuplicatePrefixCallSpecification.imageContext options before tracker)
        before.memory before.user.addresses address)
      (image : DuplicatePrefixEmptyReferenceInput.Materializable (DuplicatePrefixCallSpecification.imageContext options before tracker)
        before.memory before.user.addresses hit.id none)
      (root : BorTag) (source : Allocation CtfeProvenance Unit) (converted : Allocation Provenance Unit)
      (rootCached : tracker.global.rootTag? hit.id = some root)
      (descriptor : DuplicatePrefixEmptyReferenceInput.ImageDescriptor (DuplicatePrefixCallSpecification.imageContext options before tracker)
        before.memory hit.id source) (attributes : GlobalAllocationAttributes.Attributes source converted) :
      Effect options before tracker (.pointer (Pointer.new .wildcard (Size.ofBytes address)))

def Effect.allocation {options before tracker argument} : Effect options before tracker argument → Option AllocId
  | .integer _ | .miss .. => none
  | .concreteLive _ id .. | .concreteNonlive _ id .. | .concreteImage _ id .. => some id
  | .wildcardLive _ hit .. | .wildcardNonlive _ hit .. | .wildcardImage _ hit .. => some hit.id

def Effect.output {options before tracker argument} (effect : Effect options before tracker argument) : Argument :=
  match effect.allocation with
  | none => argument
  | some id => .pointer (Pointer.new (.concrete id tracker.global.nextPointerTag)
      (Size.ofBytes (DuplicatePrefixSliceArgument.address argument)))

def copied (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (argument : Argument) (frame : CompilerFrameContext.ActualFrame) (localId : MIR.LocalId) (valid : localId < frame.locals.size) :=
  writtenFrame frame localId valid
    (DuplicatePrefixSliceArgument.rawValue (config options remaining span).access.runtime.base argument 0 reference).imm

def registered {options before tracker argument} (effect : Effect options before tracker argument)
    (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState) :=
  match effect.allocation with
  | none => frame
  | some id => registeredFrame frame borrowFrame id tracker.global.nextPointerTag

theorem registered_size {options before tracker argument} (effect : Effect options before tracker argument)
    (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState) :
    (registered effect frame borrowFrame).locals.size = frame.locals.size := by
  unfold registered
  split <;> rfl

def resultFrame {options before tracker argument} (effect : Effect options before tracker argument)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (localId : MIR.LocalId) (valid : localId < frame.locals.size) :=
  let initial := copied options remaining span argument frame localId valid
  match effect.allocation with
  | none => initial
  | some id => writtenFrame (registered effect initial borrowFrame) localId
      (by rw [registered_size];simpa only [initial,copied,writtenFrame,Array.size_set] using valid)
      (DuplicatePrefixSliceArgument.rawValue (config options remaining span).access.runtime.base effect.output 0 reference).imm

def resultMachine {options before tracker argument} (effect : Effect options before tracker argument)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (frames : Array CompilerFrameContext.ActualFrame)
    (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState) (localId : MIR.LocalId) (valid : localId < frame.locals.size) : Before :=
  match effect with
  | .integer _ | .miss .. =>
    (TypedRetagEmpty.afterTag (Storage.withCurrent frames (copied options remaining span argument frame localId valid)
      (ScopedFrame.entered before tracker .FnEntry)) {tracker with retagMode := .FnEntry} fresh).machine
  | .concreteLive _ id _ entry tree .. => restored (CurrentCallEmptyTypedEntryConcrete.installed before tracker fresh id entry tree)
  | .wildcardLive _ hit entry tree .. => restored (CurrentCallEmptyTypedEntryWildcardLive.installed before tracker fresh hit.id entry tree)
  | .concreteNonlive .. => restored (CurrentCallEmptyTypedEntryNonlive.installed before tracker fresh)
  | .wildcardNonlive .. => restored (CurrentCallEmptyTypedEntryWildcardNonlive.installed before tracker fresh)
  | .concreteImage _ id parent _ source converted .. =>
    restored (CurrentCallEmptyTypedEntryImage.installed options before tracker fresh frames
      (copied options remaining span argument frame localId valid) borrowFrame id parent source converted)
  | .wildcardImage _ hit _ root source converted .. =>
    restored (CurrentCallEmptyTypedEntryWildcardImage.installed options before tracker fresh frames
      (copied options remaining span argument frame localId valid) borrowFrame hit.id root source converted)

private theorem metadata_cases {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (id : AllocId) (metadata : DuplicatePrefixEmptyReferenceInput.Metadata memory id none) :
    (∃ entry, memory.live.find? (fun row => row.1 == id) = some (id,entry)) ∨
      (DuplicatePrefixEmptyReferenceInput.Metadata memory id none ∧ memory.live.find? (fun row => row.1 == id) = none) := by
  cases metadata with
  | live entry present parent => exact .inl ⟨entry,present⟩
  | functionRow absent present => exact .inr ⟨.functionRow absent present,absent⟩
  | vaListRow absent noFunction present => exact .inr ⟨.vaListRow absent noFunction present,absent⟩
  | nondataGlobal descriptor absent noFunction noVaList present kind => exact .inr ⟨.nondataGlobal descriptor absent noFunction noVaList present kind,absent⟩
  | dead entry absent noFunction noVaList noGlobal present => exact .inr ⟨.dead entry absent noFunction noVaList noGlobal present,absent⟩

/-- Complete finite empty-argument dispatch. The only inputs beyond the
ORIGINAL proposal are actual frame/local readiness. Every resolver, live-row,
parent, allocator, nonlive or image case is derived inside this theorem.
The copy is unscoped, so the argument pair can share ONE outer FnEntry scope. -/
theorem copy_argument
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : Before) (tracker : MachineHooks.BorrowState) (argument : Argument)
    (place : MPlaceTy Provenance) (call : CallLoans) (data : Identities)
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument 0 place call data)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (localId : MIR.LocalId) (valid : localId < frame.locals.size) (old : Immediate Provenance)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some reference) (noClocks : frame.extra.dataRace = none) :
    let fresh := CandidateCurrentLiveRuntime.tag_room options limits remaining before tracker 0 input.machine.resources
    ∃ effect : Effect options before tracker argument,
      (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
        (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base argument 0)
        (LocalPlaces.localRuntimePlace frames.size frame localId reference).stackView
        (Storage.withCurrent frames frame (ScopedFrame.entered before tracker .FnEntry)) =
        .ok () (Storage.withCurrent frames (resultFrame effect remaining span frame borrowFrame localId valid)
          (resultMachine effect fresh remaining span frames frame borrowFrame localId valid)) := by
  dsimp only
  cases argument with
  | integer address =>
    refine ⟨.integer address,?_⟩
    exact CurrentCallEmptyTypedEntryInteger.copy_argument options limits remaining span before tracker address place call data input
      frames frame localId valid old live cached noClocks
  | pointer pointer =>
    rcases pointer with ⟨⟨address⟩,provenance⟩
    cases provenance with
    | concrete id parent =>
      have candidate := CurrentCallEmptyTypedEntryInteger.empty_candidate input
      change address ≠ 0 ∧ DuplicatePrefixEmptyReferenceInput.Concrete
        (DuplicatePrefixCallSpecification.imageContext options before tracker) before.memory before.user.addresses id parent at candidate
      obtain ⟨ctx⟩ := ActualReferenceContext.exists_context options remaining span input.machine.settings.preciseOff input.machine.settings.implicitOff
      rcases ConcreteEmptyCandidateDispatch.target_cases _ _ _ id parent candidate.2.2 with liveCase | nonliveCase | imageCase
      · obtain ⟨entry,present,_⟩ := liveCase
        obtain ⟨tree,child,copy⟩ := CurrentCallEmptyTypedEntryConcrete.copy_live options limits remaining span ctx before tracker address id parent place call data
          input entry present frames frame borrowFrame frameBorrow localId valid old live cached noClocks
        exact ⟨.concreteLive address id parent entry tree present child,copy⟩
      · obtain ⟨metadata,absent⟩ := nonliveCase
        exact ⟨.concreteNonlive address id parent metadata absent,
          CurrentCallEmptyTypedEntryNonlive.copy_nonlive options limits remaining span ctx before tracker address id parent place call data
            input metadata absent frames frame borrowFrame frameBorrow localId valid old live cached noClocks⟩
      · obtain ⟨source,converted,descriptor,attributes,copy⟩ := CurrentCallEmptyTypedEntryImage.copy_image options limits remaining span before tracker address id parent place call data
          input imageCase frames frame borrowFrame frameBorrow localId valid old live cached noClocks
        exact ⟨.concreteImage address id parent imageCase source converted descriptor attributes,copy⟩
    | wildcard =>
      have candidate := CurrentCallEmptyTypedEntryInteger.empty_candidate input
      change address ≠ 0 ∧ DuplicatePrefixEmptyReferenceInput.Wildcard
        (DuplicatePrefixCallSpecification.imageContext options before tracker) before.memory before.user.addresses at candidate
      rcases S03WildcardEmptyClassification.classify _ _ _ address candidate.2 with miss | hits
      · exact ⟨.miss address miss,CurrentCallEmptyTypedEntryWildcardMiss.copy_argument options limits remaining span before tracker address place call data input miss
          frames frame localId valid old live cached noClocks⟩
      · obtain ⟨hit⟩ := hits
        obtain ⟨ctx⟩ := ActualReferenceContext.exists_context options remaining span input.machine.settings.preciseOff input.machine.settings.implicitOff
        rcases hit.target with metadata | imageCase
        · rcases metadata_cases before.memory hit.id metadata with liveCase | nonliveCase
          · obtain ⟨entry,present⟩ := liveCase
            obtain ⟨tree,child,copy⟩ := CurrentCallEmptyTypedEntryWildcardLive.copy_live options limits remaining span ctx before tracker address hit.id place call data
              input hit rfl entry present frames frame borrowFrame frameBorrow localId valid old live cached noClocks
            exact ⟨.wildcardLive address hit entry tree present child,copy⟩
          · obtain ⟨metadata,absent⟩ := nonliveCase
            exact ⟨.wildcardNonlive address hit metadata absent,
              CurrentCallEmptyTypedEntryWildcardNonlive.copy_nonlive options limits remaining span ctx before tracker address hit.id place call data
                input hit rfl metadata absent frames frame borrowFrame frameBorrow localId valid old live cached noClocks⟩
        · obtain ⟨root,source,converted,rootCached,descriptor,attributes,copy⟩ := CurrentCallEmptyTypedEntryWildcardImage.copy_image options limits remaining span before tracker address hit.id place call data
            input hit rfl imageCase frames frame borrowFrame frameBorrow localId valid old live cached noClocks
          exact ⟨.wildcardImage address hit imageCase root source converted rootCached descriptor attributes,copy⟩


/-- Argument copying preserves the callee's control and return destination;
its only frame-extra change is the exact branch's protector registration. -/
theorem resultFrame_metadata {options before tracker argument} (effect : Effect options before tracker argument)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (localId : MIR.LocalId) (valid : localId < frame.locals.size) :
    (resultFrame effect remaining span frame borrowFrame localId valid).body = frame.body ∧
    (resultFrame effect remaining span frame borrowFrame localId valid).location = frame.location ∧
    (resultFrame effect remaining span frame borrowFrame localId valid).returnPlace = frame.returnPlace ∧
    (resultFrame effect remaining span frame borrowFrame localId valid).extra = (registered effect frame borrowFrame).extra ∧
    (resultFrame effect remaining span frame borrowFrame localId valid).locals.size = frame.locals.size := by
  cases effect <;> simp [resultFrame,Effect.allocation,registered,copied,writtenFrame,
    registeredFrame,TypedRetagEntry.frameWithBorrow]

/-- Finite branch effects preserve actual address/cache and thread selectors.
Materialization's memory and runtime-extras changes remain explicit. -/
theorem resultMachine_data {options before tracker argument} (effect : Effect options before tracker argument)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (frames : Array CompilerFrameContext.ActualFrame)
    (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState) (localId : MIR.LocalId) (valid : localId < frame.locals.size) :
    (resultMachine effect fresh remaining span frames frame borrowFrame localId valid).user.addresses = before.user.addresses ∧
    (resultMachine effect fresh remaining span frames frame borrowFrame localId valid).user.payload.payload.user.types = before.user.payload.payload.user.types ∧
    (resultMachine effect fresh remaining span frames frame borrowFrame localId valid).dataRace = before.dataRace ∧
    (resultMachine effect fresh remaining span frames frame borrowFrame localId valid).threads = before.threads := by
  cases effect <;> exact ⟨rfl,rfl,rfl,rfl⟩

end
end DuplicatePrefix.CurrentCallEmptyTypedEntry


open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.CurrentCallEmptyTypedEntry.copy_argument,
      ``DuplicatePrefix.CurrentCallEmptyTypedEntry.resultFrame_metadata,
      ``DuplicatePrefix.CurrentCallEmptyTypedEntry.resultMachine_data] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "empty typed entry dispatch depends on unapproved axiom {dependency}"
