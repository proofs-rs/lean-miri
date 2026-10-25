import Miri.Interpreter.ValidityMachine
import Miri.Interpreter.ValidityVisitor

open Miri.ABI Miri.Memory Miri.Interpreter
open Miri.Interpreter.ValidityMachine

private def testId : AllocId := ⟨1, by decide⟩
private def testTag : BorTag := ⟨1, by decide⟩

private def allocationInfoMemory : MemoryState Provenance Miri.TreeBorrows.BorrowTree Unit :=
  MemoryState.setGlobalEntries .empty #[{
    allocId := testId, kind := .memory, size := Size.ofBytes 16,
    align := Align.ONE, mutability := .Mut }]

private def testUser : ValidityMachine.UserState Unit :=
  {
    addresses := {
      provenanceMode := .default, addressMode := .managed, generation := none },
    payload := { payload := (), validation := .Deep, alignment := .Int },
    symbolicAlignment := #[] }

private def testState : ValidityMachine.State Unit Unit := {
  stack := Stack.empty,
  machine := {
    memory := allocationInfoMemory,
    borrowTracker := none,
    dataRace := none,
    threads := Miri.Concurrency.ThreadManager.initial false,
    raceAllocations := #[],
    allocationSpans := #[],
    user := testUser } }

private def accessConfig : ValidityMachine.Access Unit Unit := {
  runtime := RuntimeTargetDataLayout.default,
  ghostMode := true,
  globalKind := none,
  globalHooks := {
    synchronizeMemory := fun _ hooks => hooks,
    evaluateStaticInitializer := fun memory hooks _ => ⟨memory, hooks, .error "unused"⟩,
    beforeAccessGlobal := fun memory hooks _ _ _ _ => ⟨memory, hooks, .error "unused"⟩,
    adjustGlobalAllocation := fun memory hooks _ _ => ⟨memory, hooks, .error "unused"⟩ },
  dynamicLayout := fun memory hooks _ => ⟨memory, hooks, .ok none⟩,
  resolvePointer := fun _ pointer _ state =>
    match pointer.provenance with
    | some (.concrete id tag) =>
      .ok (.ok ⟨id, pointer.offset, .concrete tag⟩) state
    | _ => .ok (.error pointer.offset.bytes) state,
  beforeAllocationAccess := fun _ => pure (),
  diagnostic := fun _ _ _ => pure (),
  weakMemoryWrite := fun _ _ => pure (),
  syncAccess := fun _ _ _ => pure (),
  retainTouched := fun machine _ => machine,
  memoryError := fun error => .invalidProgram s!"unused access error: {repr error}" }

private def stateChangingResolver : MemoryState Provenance Miri.TreeBorrows.BorrowTree Unit →
    Pointer (Option Provenance) → Int →
    PlaceMachine.MachineM Unit (ValidityMachine.UserState Unit)
      (Except UInt64 (ResolvedPointer ProvenanceExtra)) :=
  fun _ _ _ state =>
    let user := state.user
    let user := { user with symbolicAlignment := user.symbolicAlignment.push (testId, Size.ZERO, Align.ONE) }
    .error (.callback "alignment resolver unavailable") { state with user := user }

private def testPointer : Pointer (Option Provenance) :=
  ⟨Size.ofBytes 1, some (.concrete testId testTag)⟩

private def missing {S A : Type} : EStateM StepError S A :=
  throw (.invalidProgram "unused validity fixture callback")

private def testLayout (align : Align) : LocalLayout := {
  ty := 1,
  layout := {
    fields := .Primitive, variants := .Single 0,
    backendRepr := .Memory (sized := true), largestNiche := none,
    uninhabited := false, align := .new align, size := Size.ofBytes 8,
    maxReprAlign := none, unadjustedAbiAlign := align,
    reprC := false, randomizationSeed := 0 } }

private def visitorHooks : ValidityVisitor.Hooks Provenance
    (ValidityMachine.State Unit Unit) Unit Miri.Interpreter.MachineHooks.FrameExtra
    Unit Unit Miri.Interpreter.ValidityMemory.PaddingHandle := by
  let target := RuntimeTargetDataLayout.default
  let place : PlaceHooks Provenance (ValidityMachine.State Unit Unit) Unit
      Miri.Interpreter.MachineHooks.FrameExtra := {
    getFrame := missing, setFrame := fun _ => missing,
    debugAssertions := false, frameIndex := missing,
    resolveLayout := fun _ _ => missing, localToOp := fun _ _ => missing,
    projection := fun _ => missing, deref := fun _ _ _ => missing,
    checkPlaceType := fun _ _ _ => missing, allocateStack := fun _ _ => missing,
    writeMemoryNoValidate := fun _ _ _ => missing,
    afterLocalMovedToMemory := fun _ _ _ => missing,
    memoryOffset := fun _ _ _ _ _ => missing,
    writeLocalImmediate := fun _ _ _ _ => missing,
    enforceValidity := fun _ _ => missing, validate := fun _ _ => missing }
  let dynamic : DynamicLayoutHooks Provenance (ValidityMachine.State Unit Unit) Unit := {
    target := target.base, maxSizeOfVal := Size.ofBytes 1024,
    classify := fun _ _ => missing, field := fun _ _ _ => missing,
    packedAlign := fun _ _ => missing,
    vtableSizeAndAlign := fun _ _ _ => missing }
  let projection : PlaceProjectionHooks Provenance (ValidityMachine.State Unit Unit) Unit
      Miri.Interpreter.MachineHooks.FrameExtra := {
    place, target := target.base, maxSizeOfVal := Size.ofBytes 1024,
    dynamic, dynamicFuel := 4,
    isSliceOrStr := fun _ _ => missing, field := fun _ _ _ => missing,
    variant := fun _ _ _ => missing, packedAlign := fun _ _ => missing,
    subsliceLayout := fun _ _ _ => missing, layoutOf := fun _ _ => missing,
    localIndex := fun _ _ => missing }
  let vtable : VTableHooks Provenance (ValidityMachine.State Unit Unit) Unit Unit Unit := {
    target := target.base, isDynamic := fun _ _ => missing,
    memoryOffset := fun _ _ _ _ _ => missing,
    resolvePointer := fun _ _ => missing, globalVTable := fun _ _ => missing,
    globalFunction := fun _ _ => missing, predicates := fun _ _ => missing,
    normalizePredicate := fun _ _ => missing, layoutOf := fun _ _ => missing,
    eraseAndAnonymize := fun _ _ _ => missing,
    ensureMonomorphicType := fun _ _ => missing,
    ensureMonomorphicDyn := fun _ _ => missing, globalSalt := fun _ => missing,
    reserveVTable := fun _ _ _ _ => missing, globalRootPointer := fun _ _ => missing,
    entries := fun _ _ _ => missing, assertVirtualInstanceMatches := fun _ _ _ _ _ => missing }
  let discriminant : DiscriminantHooks Provenance (ValidityMachine.State Unit Unit) Unit
      (RuntimePlace Provenance) := {
    runtimeTarget := target,
    discriminantLayout := fun _ _ => missing, tagLayout := fun _ _ => missing,
    discriminantValue := fun _ _ _ => missing,
    variantForDiscriminant := fun _ _ _ => missing,
    adtVariantCount := fun _ _ => missing, projectRead := fun _ _ _ => missing,
    readImmediate := fun _ _ => missing,
    destLayout := fun place => place.layout,
    projectWrite := fun _ _ _ => missing, writeScalar := fun _ _ _ => missing,
    toOp := fun _ _ => missing, scalarMayBeNull := fun _ _ => missing }
  exact {
    target, projection, vtable, discriminant, debugAssertions := false,
    classify := fun _ _ => pure (.reference true),
    unitLayout := fun _ => missing, typeName := fun _ _ => pure "Root",
    opsemInhabited := fun _ _ => pure true, isFreeze := fun _ _ => pure true,
    fieldPath := fun _ _ _ _ => missing, variantPath := fun _ _ _ => missing,
    projectBox := fun _ _ => missing, toOp := fun _ _ => missing,
    readImmediate := fun _ _ _ => pure ⟨
      .scalar (Scalar.fromPointer target.base (Pointer.new (.concrete testId testTag) (Size.ofBytes 1))),
      testLayout Align.EIGHT⟩,
    clearProvenance := fun _ _ => missing,
    writeNoValidate := fun _ _ _ => missing,
    sizeAndAlign := fun _ _ => pure (some (Size.ofBytes 8, Align.EIGHT)),
    ptrToPlace := fun _ _ => pure ⟨
      ⟨testPointer, .none, none⟩, testLayout Align.EIGHT⟩,
    metadataTail := fun _ _ => missing,
    checkPointerAccess := fun _ => ValidityMachine.checkPointerAccessResult accessConfig,
    checkPointerAlign := fun _ => ValidityMachine.checkPointerAlign accessConfig,
    checkPointerAlignResult := fun _ => ValidityMachine.checkPointerAlignResult accessConfig,
    scalarMayBeNull := fun _ => ValidityMachine.scalarMayBeNull,
    retagPointer := fun _ _ _ => missing,
    ctfePointerLookup := fun _ _ _ => missing,
    inMutableMemory := fun _ _ => missing,
    readBytes := fun _ _ _ _ => missing,
    clearBytesProvenance := fun _ _ _ => missing,
    beginPadding := fun _ _ _ => missing,
    writePadding := fun _ _ _ => missing,
    cachedUnionRanges := fun _ _ _ => missing,
    withGhostValidation := fun action => action }

private def check (condition : Bool) (message : String) : IO Unit :=
  if condition then pure () else throw <| IO.userError message

def main : IO Unit := do
  let path : ValidationPath := ⟨"Root", #[.field "inner", .tupleElem 2]⟩
  let session : ValidityVisitor.Session Provenance := {
    path, flags := ⟨false, false⟩, ctfeMode := none,
    refTracking := none, dataBytes := none }
  let root : RuntimePlace Provenance :=
    ⟨.memory ⟨testPointer, .none, none⟩, testLayout Align.ONE⟩
  let walked := ValidityVisitor.visit visitorHooks () 2 session root testState
  check
    (match walked with
      | .error (.undefinedBehavior message) _ =>
        message == "validation.inner.2: encountered an unaligned reference (required 8 byte alignment but found 1)"
      | _ => false)
    "real visitor walk did not carry the concrete MemoryState alignment failure through checkSafe"
  let alignmentCheck := ValidityMachine.checkPointerAlignResult accessConfig
    testPointer Align.EIGHT
  let mapped := ValidityVisitor.mapPointerAlignmentOutcome path (.reference true)
    alignmentCheck testState
  check
    (match mapped with
      | .error (.undefinedBehavior message) _ =>
        message == "validation.inner.2: encountered an unaligned reference (required 8 byte alignment but found 1)"
      | _ => false)
    "actual MemoryState alignment check did not produce source-formatted validity UB"
  let resolverAccess : ValidityMachine.Access Unit Unit :=
    { accessConfig with resolvePointer := stateChangingResolver }
  let resolverVisitor := { visitorHooks with
    checkPointerAlignResult := fun _ =>
      ValidityMachine.checkPointerAlignResult resolverAccess }
  let preserved := ValidityVisitor.visit resolverVisitor () 2 session root testState
  check
    (match preserved with
      | .error (.callback "alignment resolver unavailable") state =>
        state.machine.user.symbolicAlignment.size == 1
      | _ => false)
    "checkSafe remapping changed the non-alignment error or discarded its resolver state prefix"
  IO.println "Connected pointer alignment check: PASS"
