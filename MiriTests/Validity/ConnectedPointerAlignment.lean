import Miri.Interpreter.ValidityMachine
import Miri.Interpreter.ValidityVisitor

open Miri.ABI Miri.Memory Miri.Interpreter
open Miri.Interpreter.ValidityMachine

-- Selecting a variant or extracting the scalar data field of a wide pointer
-- preserves the source type ID, including when rank is zero.
example (rank : Miri.MIR.TyId → Nat) (parent child : LocalLayout)
    (same : child.ty = parent.ty)
    (multiple : parent.layout.variants = .Multiple tag encoding field variants)
    (single : child.layout.variants = .Single selected) :
    ValidityVisitor.layoutOrder rank child < ValidityVisitor.layoutOrder rank parent := by
  cases fields : child.layout.fields <;>
    simp [ValidityVisitor.layoutOrder,same,multiple,single,fields] <;> omega

example (rank : Miri.MIR.TyId → Nat) (parent child : LocalLayout)
    (same : child.ty = parent.ty)
    (pair : parent.layout.fields = .Arbitrary offsets order)
    (single : child.layout.variants = .Single selected)
    (scalar : child.layout.fields = .Primitive) :
    ValidityVisitor.layoutOrder rank child < ValidityVisitor.layoutOrder rank parent := by
  cases variants : parent.layout.variants <;>
    simp [ValidityVisitor.layoutOrder,same,pair,single,scalar,variants] <;> omega

example (rank : Miri.MIR.TyId → Nat) (parent child : LocalLayout)
    (dynamic : parent.layout.isSized = false) (concrete : child.layout.isSized = true) :
    Prod.Lex (· < ·) (· < ·) (ValidityVisitor.visitOrder rank child) (ValidityVisitor.visitOrder rank parent) := by
  apply Prod.Lex.left
  simp [dynamic,concrete]

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
    raceAllocations := {},
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
    typeRank := fun _ ty => if ty == 2 then 1 else 0
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
  let walked := ValidityVisitor.visit visitorHooks () (visitorHooks.typeRank testState) session root testState
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
  let preserved := ValidityVisitor.visit resolverVisitor () (resolverVisitor.typeRank testState) session root testState
  check
    (match preserved with
      | .error (.callback "alignment resolver unavailable") state =>
        state.machine.user.symbolicAlignment.size == 1
      | _ => false)
    "checkSafe remapping changed the non-alignment error or discarded its resolver state prefix"
  -- Three distinct references fit at depth two. The invalid first element is
  -- visited last by the pointee worklist, after the two valid pointees.
  let refLayout := testLayout Align.ONE
  let arrayLayout := { refLayout with ty := 2, layout := { refLayout.layout with
    fields := .Array (Size.ofBytes 8) 3, size := Size.ofBytes 24 } }
  let elementLayout := { refLayout with ty := 3 }
  let hooks := { visitorHooks with
    classify := fun _ ty => pure (if ty == 2 then .sequence 1 else if ty == 1 then .reference false else .boolean)
    unitLayout := fun _ => pure refLayout
    projection := { visitorHooks.projection with
      layoutOf := fun _ _ => pure refLayout, field := fun _ _ _ => pure refLayout
      place := { visitorHooks.projection.place with memoryOffset := fun _ base offset _ metadata => do
        let offset ← match base.ptr.offset.add offset with
          | .ok value => pure value | .error error => throw (.invalidProgram (reprStr error))
        pure {base with ptr := {base.ptr with offset}, metadata := metadata} } }
    readImmediate := fun _ place _ => do
      let .memory memory := place.ref | missing
      let scalar ← if place.layout.ty == 1 then
          pure (Scalar.fromPointer RuntimeTargetDataLayout.default.base
            (Pointer.new (.concrete testId testTag) memory.ptr.offset))
        else do
          modify fun state =>
            let user := state.machine.user
            {state with machine := {state.machine with user := {user with
              symbolicAlignment := user.symbolicAlignment.push (testId,memory.ptr.offset,Align.ONE)}}}
          match Scalar.fromUInt (BitVec.ofNat 128 (if memory.ptr.offset == Size.ZERO then 2 else 1)) (Size.ofBytes 1) with
          | .ok value => pure value | .error _ => missing
      pure ⟨.scalar scalar,place.layout⟩
    ptrToPlace := fun _ value => do
      let .scalar scalar := value.imm | missing
      let .ok ptr := scalar.toPointer RuntimeTargetDataLayout.default.base | missing
      pure ⟨⟨ptr,.none,none⟩,elementLayout⟩
    sizeAndAlign := fun _ _ => pure (some (Size.ofBytes 1,Align.ONE))
    scalarMayBeNull := fun _ _ => pure false
    checkPointerAlignResult := fun _ _ _ => pure (.ok ())
    checkPointerAccess := fun _ _ _ => pure (.ok ()) }
  let arrayRoot : RuntimePlace Provenance :=
    ⟨.memory ⟨{testPointer with offset := Size.ZERO},.none,none⟩,arrayLayout⟩
  match ValidityVisitor.validatePlace hooks () arrayRoot true false testState with
  | .error (.undefinedBehavior message) state =>
    check (state.machine.user.symbolicAlignment.map (fun entry => entry.2.1.bytes) == #[16,8,0])
      "tracked pointees did not run in reverse discovery order"
    check (message.startsWith "validation[0]") s!"unexpected pointee diagnostic: {message}"
  | _ => throw <| IO.userError "validation failed to reach the invalid third tracked pointee"
  -- A pattern visits its base at the same byte offset. This exceeds the
  -- old runner depth of 128 while every static type edge descends.
  let patternHooks := { hooks with
    typeRank := fun _ ty => ty
    classify := fun _ ty => pure (if ty == 0 then .foreign else .pattern (ty-1))
    projection := { hooks.projection with layoutOf := fun _ ty => pure {refLayout with ty} } }
  let nested := {arrayRoot with layout := {refLayout with ty := 150}}
  match ValidityVisitor.validatePlace patternHooks () nested false false testState with
  | .ok () _ => pure ()
  | .error error _ => throw <| IO.userError s!"deep pattern validation failed: {reprStr error}"
  let unionLayout := fun (ty : Nat) =>
    {refLayout with ty,layout := {refLayout.layout with fields := if ty == 0 then .Primitive else .Union 1}}
  let unionHooks := { hooks with projection := {hooks.projection with
    field := fun _ parent _ => pure (unionLayout (parent.ty-1))} }
  match ValidityVisitor.unionRanges unionHooks () id (unionLayout 150) Size.ZERO .empty testState with
  | .ok ranges _ => check (ranges.toArray == #[allocRange Size.ZERO refLayout.layout.size]) "deep union byte range mismatch"
  | .error error _ => throw <| IO.userError s!"deep union traversal failed: {reprStr error}"
  IO.println "Connected pointer alignment check: PASS"
