import duplicate_prefix.RootEmptyReferenceValidity
import duplicate_prefix.TypedRetagLocal
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.PositiveReferenceValidity
open Miri.ABI Miri.Memory Miri.MIR Miri.Input Miri.Interpreter
open RootEmptyReferenceValidity
theorem positive_check_of_retag {K U C F A : Type} [DecidableEq K]
    (hooks : ValidityVisitor.Hooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra F A ValidityMemory.PaddingHandle)
    (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C)
    (retag : TypedRetag.Hooks K (ValidityMachine.UserState U))
    (prepared : CompilerFactAdapters.Prepared) (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (choice : C) (budget : Nat)
    (fields : VisitorFields hooks access allocation compiler retag choice budget)
    (sources : TypedRetagFields.SourceFields retag prepared access hooks.projection hooks.vtable pointers choice)
    (reference pointee : LocalLayout) (id : AllocId) (parentTag childTag : BorTag) (base addressOffset len : UInt64)
    (nonzero : base + addressOffset ≠ 0)
    (entry : LocalAllocation Provenance Miri.TreeBorrows.BorrowTree K)
    (pointerWiring : access.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (arithmetic : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (positive : (0 : UInt64) < len) (signedFits : len.toNat < 9223372036854775808)
    (bounds : addressOffset.toNat + len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (queries : TypedRetagFields.ReferenceQueries retag reference.ty pointee.ty)
    (dereference : CompilerFacts.builtinDeref prepared.context reference.ty true = .ok (some pointee.ty))
    (pointeeLayout : CompilerFacts.layoutOf prepared.context pointee.ty = .ok pointee)
    (pointeeAlign : pointee.layout.align.abi = Align.ONE)
    (pointerField : hooks.ptrToPlace = PointerPlaceMachine.fromImmediate access
      (CompilerExecutionProviders.pointerCompiler prepared))
    (width : access.runtime.base.pointerWidth = .w64)
    (targetWidth : hooks.target.base.pointerWidth = .w64)
    (targetSize : hooks.target.pointerSize = Size.ofBytes 8)
    (pointeeUnsized : pointee.layout.isSized = false)
    (tail : hooks.metadataTail choice pointee.ty = pure .sliceOrStr)
    (inhabited : hooks.opsemInhabited choice pointee.ty = pure true)
    (name : String)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (localId : Miri.MIR.LocalId) (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate (RetagReferencePlace.sliceValue access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base + addressOffset))) len reference).imm))
    (cached : frame.locals[localId].layout = some reference)
    (sized : reference.layout.isSized = true)
    (pa pb : Primitive) (ra rb : WrappingRange) (offset : Size)
    (repr : reference.layout.backendRepr = .ScalarPair (a := .Initialized (value := pa) (validRange := ra))
      (b := .Initialized (value := pb) (validRange := rb)) (bOffset := offset))
    (debug : compiler.debugAssertions = false)
    (noDebug : compiler.debugAbiCheck (RetagReferencePlace.sliceValue access.runtime.base
      (Pointer.new (.concrete id childTag) (Size.ofBytes (base + addressOffset))) len reference).imm reference = pure ())
    (ghost : machine.user.payload.ghost = true)
    (retain : access.retainTouched = fun machine _ => machine)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (afterFrame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (afterMachine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (sameLocals : afterFrame.locals = frame.locals)
    (sameDestination : LocalPlaces.localRuntimePlace frames.size frame localId reference =
      LocalPlaces.localRuntimePlace frames.size afterFrame localId reference)
    (ghostAfter : afterMachine.user.payload.ghost = true)
    (sizingAt : retag.sizeAndAlign
      (RetagReferencePlace.slicePlace (Pointer.new (.concrete id parentTag) (Size.ofBytes (base + addressOffset))) len pointee)
      (Storage.withCurrent frames frame machine) = .ok (some (Size.ofBytes len, Align.ONE))
      (Storage.withCurrent frames frame machine))
    (retaggedAt : hooks.retagPointer choice
      (RetagReferencePlace.sliceValue access.runtime.base (Pointer.new (.concrete id parentTag) (Size.ofBytes (base + addressOffset))) len reference)
      reference.ty (Storage.withCurrent frames frame machine) =
      .ok (some (RetagReferencePlace.sliceValue access.runtime.base
        (Pointer.new (.concrete id childTag) (Size.ofBytes (base + addressOffset))) len reference))
        (Storage.withCurrent frames afterFrame afterMachine)) :
    let state := Storage.withCurrent frames frame machine
    source_check_safe hooks choice (ReferenceValidity.referenceSession name)
      (LocalPlaces.localRuntimePlace frames.size frame localId reference) reference.ty (.reference true) state =
      .ok (ReferenceValidity.referenceSession name)
        (Storage.withCurrent frames
          {afterFrame with locals := (afterFrame.locals.set localId
            {value := .live (.immediate (RetagReferencePlace.sliceValue access.runtime.base
              (Pointer.new (.concrete id childTag) (Size.ofBytes (base + addressOffset))) len reference).imm),
             layout := (afterFrame.locals[localId]'(by simpa [sameLocals] using valid)).layout} (by simpa [sameLocals] using valid))} afterMachine) := by
  let value := RetagReferencePlace.sliceValue access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base + addressOffset))) len reference
  let place := RetagReferencePlace.slicePlace (Pointer.new (.concrete id parentTag) (Size.ofBytes (base + addressOffset))) len pointee
  let destination := LocalPlaces.localRuntimePlace frames.size frame localId reference
  let state := Storage.withCurrent frames frame machine
  let adjusted := RetagReferencePlace.sliceValue access.runtime.base
    (Pointer.new (.concrete id childTag) (Size.ofBytes (base + addressOffset))) len reference
  let after := Storage.withCurrent frames afterFrame afterMachine
  let written := Storage.withCurrent frames
    {afterFrame with locals := (afterFrame.locals.set localId
      {value := .live (.immediate adjusted.imm), layout := (afterFrame.locals[localId]'(by simpa [sameLocals] using valid)).layout}
      (by simpa [sameLocals] using valid))} afterMachine
  have read : hooks.readImmediate choice destination .reference state = .ok value state := by
    rw [fields.read]
    exact ReferenceValidity.read_local_pair_ghost access allocation compiler choice frames frame machine localId
      reference _ _ valid live cached sized debug ghost pa pb ra rb offset repr retain .reference
  have construct : hooks.ptrToPlace choice value = pure place := by
    rw [pointerField]
    exact RetagReferencePlace.canonical_from_immediate access prepared choice _ len reference pointee
      dereference pointeeLayout pointeeAlign
  have metadata : source_check_metadata hooks choice place = pure () :=
    ReferenceValidity.metadata_slice hooks choice place len tail rfl targetSize
  have sizing : hooks.sizeAndAlign choice place state = .ok (some ((Size.ofBytes len), Align.ONE)) state := by
    rw [fields.sizing]
    exact sizingAt
  have check : hooks.checkPointerAccess choice place.mplace.ptr (Size.ofBytes len) state = .ok (.ok ()) state := by
    rw [fields.check]
    exact ReferenceChecks.check_result_cached pointers access state id parentTag base addressOffset len entry
      pointerWiring arithmetic cachedAddress present positive signedFits bounds
  have retagged : hooks.retagPointer choice value reference.ty state = .ok (some adjusted) after := retaggedAt
  have write : hooks.writeNoValidate choice adjusted.imm destination after = .ok () written := by
    rw [fields.write]
    simp only [destination, sameDestination]
    exact ReferenceValidity.visitor_write_local_ghost access allocation compiler choice frames afterFrame afterMachine localId
      value.imm adjusted.imm reference (by simpa [sameLocals] using valid)
      (by simpa [sameLocals] using live) (by simpa [sameLocals] using cached) sized debug
      noDebug ghostAfter
  have encoded : Scalar.fromMaybePointer hooks.target.base place.mplace.ptr =
      .ok (Scalar.fromPointer hooks.target.base
        (Pointer.new (.concrete id parentTag) (Size.ofBytes (base + addressOffset)))) := rfl
  have nonnull : hooks.scalarMayBeNull choice (Scalar.fromPointer hooks.target.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base + addressOffset)))) = pure false := by
    rw [fields.nonnull]
    exact ReferenceChecks.pointer_not_null hooks.target.base _ targetWidth nonzero
  have aligned : hooks.checkPointerAlignResult choice place.mplace.ptr Align.ONE written = .ok (.ok ()) written := by
    rw [fields.align]
    exact ReferenceChecks.alignment_one access place.mplace.ptr written
  exact ReferenceValidity.check_reference_stage_at hooks choice name destination value adjusted place (Size.ofBytes len) Align.ONE
    _ state after written read construct pointeeUnsized metadata sizing check retagged write encoded nonnull inhabited aligned

theorem positive_validate_of_retag {K U C F A : Type} [DecidableEq K]
    (hooks : ValidityVisitor.Hooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra F A ValidityMemory.PaddingHandle)
    (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C)
    (retag : TypedRetag.Hooks K (ValidityMachine.UserState U))
    (prepared : CompilerFactAdapters.Prepared) (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (choice : C) (budget fuel : Nat)
    (fields : VisitorFields hooks access allocation compiler retag choice budget)
    (sources : TypedRetagFields.SourceFields retag prepared access hooks.projection hooks.vtable pointers choice)
    (reference pointee : LocalLayout) (id : AllocId) (parentTag childTag : BorTag) (base addressOffset len : UInt64)
    (nonzero : base + addressOffset ≠ 0)
    (entry : LocalAllocation Provenance Miri.TreeBorrows.BorrowTree K)
    (pointerWiring : access.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (arithmetic : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (positive : (0 : UInt64) < len) (signedFits : len.toNat < 9223372036854775808)
    (bounds : addressOffset.toNat + len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (queries : TypedRetagFields.ReferenceQueries retag reference.ty pointee.ty)
    (dereference : CompilerFacts.builtinDeref prepared.context reference.ty true = .ok (some pointee.ty))
    (pointeeLayout : CompilerFacts.layoutOf prepared.context pointee.ty = .ok pointee)
    (pointeeAlign : pointee.layout.align.abi = Align.ONE)
    (pointerField : hooks.ptrToPlace = PointerPlaceMachine.fromImmediate access
      (CompilerExecutionProviders.pointerCompiler prepared))
    (width : access.runtime.base.pointerWidth = .w64)
    (targetWidth : hooks.target.base.pointerWidth = .w64)
    (targetSize : hooks.target.pointerSize = Size.ofBytes 8)
    (pointeeUnsized : pointee.layout.isSized = false)
    (tail : hooks.metadataTail choice pointee.ty = pure .sliceOrStr)
    (inhabited : hooks.opsemInhabited choice pointee.ty = pure true)
    (name : String)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (localId : Miri.MIR.LocalId) (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate (RetagReferencePlace.sliceValue access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base + addressOffset))) len reference).imm))
    (cached : frame.locals[localId].layout = some reference)
    (sized : reference.layout.isSized = true)
    (pa pb : Primitive) (ra rb : WrappingRange) (offset : Size)
    (repr : reference.layout.backendRepr = .ScalarPair (a := .Initialized (value := pa) (validRange := ra))
      (b := .Initialized (value := pb) (validRange := rb)) (bOffset := offset))
    (debug : compiler.debugAssertions = false)
    (noDebug : compiler.debugAbiCheck (RetagReferencePlace.sliceValue access.runtime.base
      (Pointer.new (.concrete id childTag) (Size.ofBytes (base + addressOffset))) len reference).imm reference = pure ())
    (ghost : machine.user.payload.ghost = false)
    (retain : access.retainTouched = fun machine _ => machine)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (afterFrame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (afterMachine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (sameLocals : afterFrame.locals = frame.locals)
    (sameDestination : LocalPlaces.localRuntimePlace frames.size frame localId reference =
      LocalPlaces.localRuntimePlace frames.size afterFrame localId reference)
    (ghostAfter : afterMachine.user.payload.ghost = true)
    (sizingAt : retag.sizeAndAlign
      (RetagReferencePlace.slicePlace (Pointer.new (.concrete id parentTag) (Size.ofBytes (base + addressOffset))) len pointee)
      (Storage.withCurrent frames frame {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}) = .ok (some (Size.ofBytes len, Align.ONE))
      (Storage.withCurrent frames frame {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}))
    (retaggedAt : hooks.retagPointer choice
      (RetagReferencePlace.sliceValue access.runtime.base (Pointer.new (.concrete id parentTag) (Size.ofBytes (base + addressOffset))) len reference)
      reference.ty (Storage.withCurrent frames frame {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}) =
      .ok (some (RetagReferencePlace.sliceValue access.runtime.base
        (Pointer.new (.concrete id childTag) (Size.ofBytes (base + addressOffset))) len reference))
        (Storage.withCurrent frames afterFrame afterMachine))    (named : hooks.typeName choice reference.ty = pure name)
    (classified : hooks.classify choice reference.ty = pure (.reference true)) :
    ValidityVisitor.validatePlace hooks choice (fuel + 1)
      (LocalPlaces.localRuntimePlace frames.size frame localId reference) false true
      (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames
        {afterFrame with locals := (afterFrame.locals.set localId
          {value := .live (.immediate (RetagReferencePlace.sliceValue access.runtime.base
            (Pointer.new (.concrete id childTag) (Size.ofBytes (base + addressOffset))) len reference).imm),
           layout := (afterFrame.locals[localId]'(by simpa [sameLocals] using valid)).layout}
          (by simpa [sameLocals] using valid))}
        {afterMachine with user := {afterMachine.user with payload := {afterMachine.user.payload with ghost := false}}}) := by
  let activeMachine := {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}
  let destination := LocalPlaces.localRuntimePlace frames.size frame localId reference
  let value := RetagReferencePlace.sliceValue access.runtime.base
    (Pointer.new (.concrete id parentTag) (Size.ofBytes (base + addressOffset))) len reference
  let adjusted := RetagReferencePlace.sliceValue access.runtime.base
    (Pointer.new (.concrete id childTag) (Size.ofBytes (base + addressOffset))) len reference
  let written := Storage.withCurrent frames
    {afterFrame with locals := (afterFrame.locals.set localId
      {value := .live (.immediate adjusted.imm),
       layout := (afterFrame.locals[localId]'(by simpa [sameLocals] using valid)).layout}
      (by simpa [sameLocals] using valid))} afterMachine
  have check := positive_check_of_retag hooks access allocation compiler retag prepared pointers choice budget
    fields sources reference pointee id parentTag childTag base addressOffset len nonzero entry pointerWiring arithmetic
    positive signedFits bounds queries dereference pointeeLayout pointeeAlign pointerField width targetWidth targetSize
    pointeeUnsized tail inhabited name frames frame activeMachine localId valid live cached sized
    pa pb ra rb offset repr debug noDebug rfl retain cachedAddress present afterFrame afterMachine sameLocals
    sameDestination ghostAfter sizingAt retaggedAt
  have visited : ValidityVisitor.visit hooks choice (fuel + 1) (ReferenceValidity.referenceSession name)
      destination (Storage.withCurrent frames frame activeMachine) =
      .ok (ReferenceValidity.referenceSession name) written :=
    ReferenceValidity.visit_reference_of_check hooks choice fuel name destination _ written classified check
  have toOp : hooks.toOp choice destination (Storage.withCurrent frames frame activeMachine) =
      .ok ⟨.immediate value.imm, reference⟩ (Storage.withCurrent frames frame activeMachine) := by
    rw [fields.toOp]
    exact ScalarCopyStage.place_to_op_ghost access allocation compiler choice frames frame activeMachine localId
      reference value.imm valid live cached sized debug rfl
  exact ReferenceValidity.validate_reference_shallow_of_visit hooks choice fuel name destination
    (Storage.withCurrent frames frame machine) written value.imm ghost ghostAfter named fields.ghost toOp visited

#print axioms positive_validate_of_retag

end DuplicatePrefix.PositiveReferenceValidity

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.PositiveReferenceValidity.positive_check_of_retag,
      ``DuplicatePrefix.PositiveReferenceValidity.positive_validate_of_retag] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved positive reference dependency {dependency}"
