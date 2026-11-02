import duplicate_prefix.PositiveReferenceValidity
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.PositiveReferenceDriver
open Miri.ABI Miri.Memory Miri.MIR Miri.Input Miri.Interpreter
open RootEmptyReferenceValidity
theorem positive_validate_from_fields {K U C F A : Type} [DecidableEq K]
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
    (capacity : UInt64) (global : Miri.TreeBorrows.GlobalState)
    (borrowFrame : Miri.TreeBorrows.FrameState)
    (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (enabled : machine.borrowTracker = some ⟨global, .FnEntry⟩)
    (fresh : global.nextPointerTag.value < 18446744073709551615)
    (childTagEq : childTag = global.nextPointerTag)
    (distinct : parentTag ≠ global.nextPointerTag)
    (rootUnprotected : global.protectedTags.contains parentTag = false)
    (root : entry.allocation.extra = Miri.TreeBorrows.BorrowTree.new parentTag (Size.ofBytes capacity))
    (allocationSize : entry.allocation.byteSize = Size.ofBytes capacity)
    (globalKind : K)
    (globals : GlobalAllocationHooks Provenance Miri.TreeBorrows.BorrowTree K
      (PlaceMachine.AccessState K (ValidityMachine.UserState U)))
    (extraWiring : pointers.ensureTreeExtra = GlobalAllocationMachine.ensure globalKind globals)
    (synchronize : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}})
    (race : machine.dataRace = none)
    (afterState : TypedRetagGeneric.completedState
      (Storage.withCurrent frames frame {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}})
      frames frame borrowFrame id entry parentTag global fresh capacity addressOffset len =
      Storage.withCurrent frames afterFrame afterMachine)
    (named : hooks.typeName choice reference.ty = pure name)
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
  let active := Storage.withCurrent frames frame activeMachine
  let pointer := Pointer.new (Provenance.concrete id parentTag) (Size.ofBytes (base + addressOffset))
  let place := RetagReferencePlace.slicePlace pointer len pointee
  let value := RetagReferencePlace.sliceValue access.runtime.base pointer len reference
  have beforeEq : TypedRetagGeneric.beforeTagState active frames frame borrowFrame global = active :=
    TypedRetagGeneric.before_tag_eq active frames frame borrowFrame global rfl frameBorrow enabled
  have sizing : retag.sizeAndAlign place
      (TypedRetagGeneric.beforeTagState active frames frame borrowFrame global) =
      .ok (some (Size.ofBytes len, Align.ONE))
        (TypedRetagGeneric.beforeTagState active frames frame borrowFrame global) := by
    rw [beforeEq]
    exact sizingAt
  have inBounds : addressOffset.toNat + len.toNat ≤ capacity.toNat := by
    simpa only [allocationSize, Size.ofBytes] using bounds
  have driver := TypedRetagLocal.retag_pointer_local retag prepared access hooks.projection hooks.vtable
    pointers choice sources budget place reference active frames frame borrowFrame id entry capacity base addressOffset len
    parentTag global fresh distinct rootUnprotected rfl queries.freeze pointerWiring arithmetic globalKind globals
    extraWiring synchronize cachedAddress present root allocationSize positive signedFits inBounds sizing rfl
    queries.shape queries.pointee_eq dereference pointeeLayout pointeeAlign queries.unpin queries.unsafeUnpin race
  rw [beforeEq] at driver
  have guarded : hooks.retagPointer choice value reference.ty active =
      .ok (some (RetagReferencePlace.sliceValue access.runtime.base
        (Pointer.new (.concrete id childTag) (Size.ofBytes (base + addressOffset))) len reference))
        (Storage.withCurrent frames afterFrame afterMachine) := by
    rw [fields.retagAction]
    unfold TypedRetag.machineRetagPtrValue
    simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
      active, activeMachine, Storage.withCurrent, enabled]
    have completed : TypedRetagGeneric.completedState active frames frame borrowFrame id entry parentTag global fresh capacity addressOffset len =
        Storage.withCurrent frames afterFrame afterMachine := afterState
    rw [completed] at driver
    simpa only [value, pointer, active, activeMachine, Storage.withCurrent, enabled, childTagEq] using driver
  exact PositiveReferenceValidity.positive_validate_of_retag hooks access allocation compiler retag prepared pointers
    choice budget fuel fields sources reference pointee id parentTag childTag base addressOffset len nonzero entry pointerWiring
    arithmetic positive signedFits bounds queries dereference pointeeLayout pointeeAlign pointerField width targetWidth targetSize
    pointeeUnsized tail inhabited name frames frame machine localId valid live cached sized pa pb ra rb offset repr debug noDebug
    ghost retain cachedAddress present afterFrame afterMachine sameLocals sameDestination ghostAfter sizingAt guarded named classified

#print axioms positive_validate_from_fields

end DuplicatePrefix.PositiveReferenceDriver
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.PositiveReferenceDriver.positive_validate_from_fields) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved positive reference driver dependency {dependency}"
