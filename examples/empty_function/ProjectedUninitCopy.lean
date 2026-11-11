import empty_function.ProjectedForce
import empty_function.ProjectedValidate
import empty_function.ProjectedCopy
import empty_function.ProjectionOffset
namespace EmptyFunction.ProjectedUninitCopy
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.Configuration EmptyFunction.WholeCall EmptyFunction.Specification EmptyFunction.InputDraft
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1400000
set_option linter.unusedSimpArgs false

/-- Internal scalar/pair operation composition. Actual allocation, the old
value write and source span equations come from their raw-data component
proofs. The public endpoint must discharge all three; they are not validity
or metadata fields. Unit copying and nested validation use the shared stages. -/
theorem from_allocation (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+2) (positive : 0 < s.options.limits.validation)
    (frames : Array LocalUnit.F) (frame : LocalUnit.F)
    (machine allocatedMachine movedMachine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (id : MIR.LocalId) (slot : LocalState Provenance LocalLayout) (baseLayout : LocalLayout)
    (bound : id < frame.locals.size) (atSlot : frame.locals[id]? = some slot)
    (live : slot.value = .live (.immediate .uninit)) (cache : slot.layout = some baseLayout)
    (sized : baseLayout.layout.isSized = true)
    (allocation : AllocId) (tag : BorTag) (base : UInt64) (offset : Size)
    (created : PlaceMachine.allocateStack s.cfg.allocation baseLayout (LocalUnit.current frames frame machine) =
      .ok ⟨⟨Pointer.new (some (.concrete allocation tag)) (Size.ofBytes base),.none,none⟩,baseLayout⟩
        (LocalUnit.current frames frame allocatedMachine))
    (moved : MachineHooks.afterLocalMovedToMemory id
      ⟨⟨Pointer.new (some (.concrete allocation tag)) (Size.ofBytes base),.none,none⟩,baseLayout⟩ s.cfg.compiler.localSpan
      (LocalUnit.current frames frame allocatedMachine) = .ok () (LocalUnit.current frames frame movedMachine))
    (footprint : IndirectFootprint (LocalUnit.current frames frame movedMachine)
      (Pointer.new (some (.concrete allocation tag)) (Size.ofBytes base)) baseLayout.layout.size)
    (within : offset.bytes.toNat ≤ baseLayout.layout.size.bytes.toNat) (signed : baseLayout.layout.size.bytes.toNat < 2^63)
    (noClocks : frame.extra.dataRace = none) (noGhost : movedMachine.user.payload.ghost = false)
    (shallow : movedMachine.user.payload.validation = .Shallow) :
    let parent : MemPlace Provenance := ⟨Pointer.new (some (.concrete allocation tag)) (Size.ofBytes base),.none,none⟩
    let updated := {frame with locals := frame.locals.set id {slot with value := .live (.indirect parent)} bound}
    (ReturnStep.control s).copyReturn () ⟨.immediate .uninit,s.abi.ret.layout⟩
      (.frameLocal frames.size id (some offset) s.abi.ret.layout frame.localsIdentity) (LocalUnit.current frames frame machine) =
      (LocalUnit.current frames updated movedMachine,.ok ()) := by
  dsimp only
  let parent : MemPlace Provenance := ⟨Pointer.new (some (.concrete allocation tag)) (Size.ofBytes base),.none,none⟩
  let updated := {frame with locals := frame.locals.set id {slot with value := .live (.indirect parent)} bound}
  let nextSlot := {slot with value := .live (.indirect parent)}
  have dictionaries := MetadataBinding.fields s metadata (by omega)
  have forced := ProjectedForce.uninit s.cfg.access s.cfg.allocation s.cfg.compiler () frames frame
    machine allocatedMachine movedMachine id slot baseLayout s.abi.ret.layout bound atSlot live cache
    sized (dictionaries.debug.trans profile.debug) ⟨parent,baseLayout⟩ created moved (some offset) frame.localsIdentity
  have wrapped := ProjectionOffset.wrapping s metadata (by omega) (LocalUnit.current frames updated movedMachine) parent offset
  simp only [ValidityMachine.placeHooks,ValidityMachine.compilerPolicy,PlaceMachine.placeHooks,
    bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure] at forced
  rw [wrapped] at forced
  have forcedEq : forceAllocation (ValidityMachine.placeHooks s.cfg.access s.cfg.allocation s.cfg.compiler) ()
      ⟨.local frames.size id (some offset) frame.localsIdentity,s.abi.ret.layout⟩ (LocalUnit.current frames frame machine) =
      .ok ⟨⟨Pointer.new (some (.concrete allocation tag)) (Size.ofBytes (base+offset.bytes)),.none,none⟩,s.abi.ret.layout⟩
        (LocalUnit.current frames updated movedMachine) := forced
  have atNext : updated.locals[id]? = some nextSlot := by simp [updated,nextSlot,bound]
  have foot := ProjectedFootprint.atState (LocalUnit.current frames frame movedMachine)
    (LocalUnit.current frames updated movedMachine) parent.ptr baseLayout.layout.size footprint rfl rfl
  have nextCache : nextSlot.layout = some baseLayout := cache
  have valid := ProjectedValidate.concrete s metadata profile remaining capacity positive frames updated movedMachine
    id nextSlot baseLayout parent allocation tag offset atNext rfl nextCache noClocks noGhost shallow rfl foot within signed
  have fields := BodyPlaceDictionaries.fields_of_make s.prepared.compiler s.prepared.image s.bytes (EmptyFunction.Configuration.proofOptions s.options)
    (Configuration.leaves s.prepared s.options.place.debugAssertions) (remaining+1) metadata.construction s.cfg
    (by simpa only [Configuration.rootConfig,capacity,Nat.add_assoc] using s.built)
  rw [←fields.projection] at forcedEq
  exact ProjectedCopy.control_from_force s metadata profile remaining capacity (LocalUnit.current frames frame machine)
    (LocalUnit.current frames updated movedMachine) frames.size id offset frame.localsIdentity
    ⟨⟨Pointer.new (some (.concrete allocation tag)) (Size.ofBytes (base+offset.bytes)),.none,none⟩,s.abi.ret.layout⟩
    rfl rfl rfl forcedEq shallow valid
end EmptyFunction.ProjectedUninitCopy
