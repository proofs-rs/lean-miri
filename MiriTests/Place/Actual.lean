import Miri.Interpreter.Place
open Miri Miri.ABI Miri.Memory Miri.Interpreter

private def scalarAbi : ABI.Scalar := .Initialized (value := .Int .I32 false)
  (validRange := ⟨BitVec.ofNat 128 0, BitVec.ofNat 128 (2^32-1)⟩)
private def fieldLayout : LocalLayout := ⟨1, ⟨.Primitive, .Single 0, .Scalar scalarAbi,
  none, false, ⟨⟨2⟩⟩, Size.ofBytes 4, none, ⟨2⟩, false, 0⟩⟩
private def pairLayout : LocalLayout := ⟨2, ⟨.Arbitrary #[Size.ZERO, Size.ofBytes 4] #[0,1], .Single 0,
  .ScalarPair (a := scalarAbi) (b := scalarAbi) (bOffset := Size.ofBytes 4),
  none, false, ⟨⟨2⟩⟩, Size.ofBytes 8, none, ⟨2⟩, false, 0⟩⟩
private def scalar (n : Nat) : Except StepError (Memory.Scalar AllocId) :=
  (Scalar.fromUInt (BitVec.ofNat 128 n) (Size.ofBytes 4)).mapError fun e => .callback (reprStr e)
private structure S where
  frame : Frame AllocId LocalLayout Nat
  memory : MemoryState AllocId Unit Unit := .empty
  events : Array String := #[]
private def emit (event : String) : PlaceM S Unit := do
  modify fun s => { s with events := s.events.push event }
private def putMemory (s : S) (memory : MemoryState AllocId Unit Unit) (events : Array String) : S :=
  { s with memory, events }
private def globalHooks : GlobalAllocationHooks AllocId Unit Unit (Array String) := {
  synchronizeMemory := fun _ state => state
  evaluateStaticInitializer := fun memory s _ => ⟨memory, s, .error "no statics"⟩
  beforeAccessGlobal := fun memory s _ _ _ _ => ⟨memory, s, .error "no globals"⟩
  adjustGlobalAllocation := fun memory s _ _ => ⟨memory, s, .error "no globals"⟩ }
private def accessHooks : AllocationAccessHooks AllocId Unit Unit (Array String) Unit := {
  resolvePointer := fun _ s ptr _ => match ptr.provenance with
    | some id => ⟨s.push "resolve", .ok (.ok ⟨id, ptr.offset, ()⟩)⟩
    | none => ⟨s, .error "no exposed addresses"⟩
  beforeAllocationAccess := fun s _ => ⟨s.push "access", .ok ()⟩
  beforeMemoryRead := fun s extra _ _ _ _ => ⟨s.push "read", extra, .ok ()⟩
  beforeMemoryWrite := fun s extra _ _ _ _ => ⟨s.push "write", extra, .ok ()⟩ }
private def context : LocalReadContext AllocId Unit Unit (Array String) Unit := {
  runtime := RuntimeTargetDataLayout.default
  ghostMode := false, globalKind := none, globalHooks, accessHooks
  dynamicLayout := fun memory s _ => ⟨memory, s, .error "no DST"⟩ }
private def cx : ProjectionCx AllocId := {
  target := ⟨.little, .w64⟩, maxSizeOfVal := Size.ofBytes 1024
  isSliceOrStr := fun _ => .ok false
  field := fun l i => if l.ty == 2 && i < 2 then .ok fieldLayout else .error (.obligation "field")
  variant := fun _ _ => .error (.obligation "variant")
  dynamicAlign := fun _ _ => .error (.obligation "DST")
  packedAlign := fun _ => .ok none
  immediateOffset := projectionImmediateOffset (fun _ _ => .ok ())
  memoryOffset := fun _ _ _ _ => .error (.obligation "memory offset")
  subsliceLayout := fun _ _ => .error (.obligation "subslice")
  layoutOf := fun _ => .error (.obligation "layoutOf")
  deref := fun _ => .error (.obligation "deref")
  localIndex := fun _ => .error (.obligation "index") }
private def hooks (failMove : Bool := false) : PlaceHooks AllocId S Unit Nat := {
  debugAssertions := false
  getFrame := return (← get).frame
  setFrame := fun frame => modify fun s => { s with frame }
  frameIndex := pure 0
  resolveLayout := fun _ _ => do emit "layout"; return pairLayout
  localToOp := fun _ id => do
    emit "local-read"
    let frame := (← get).frame
    match frame.getLocalOperand id, frame.getLocalLayout id with
    | .ok op, .ok (some layout) => return ⟨op, layout⟩
    | _, _ => throw (.callback "local read")
  projection := fun _ => pure cx
  deref := fun _ _ _ => throw (.unsupported "fixture has no deref")
  checkPlaceType := fun _ _ _ => emit "typecheck"
  allocateStack := fun _ layout => do
    emit "allocate"
    placeAllocateStack (Size.ofBytes 1024)
      (fun size _ => some (Array.replicate size.bytes.toNat 0))
      (fun _ state => state)
      (fun memory s _ _ _ _ => ⟨memory,s.push "init-extra",.ok ()⟩)
      (fun memory s id _ => ⟨memory,s.push "root",.ok ⟨Size.ZERO, id⟩⟩)
      S.memory S.events putMemory layout
  writeMemoryNoValidate := fun _ value place =>
    placeMemoryWrite context (fun _ => false) S.memory S.events putMemory (fun s _ => s) value place
  afterLocalMovedToMemory := fun _ _ _ => do
    emit "moved"
    modify fun s => { s with frame := { s.frame with extra := s.frame.extra + 1 } }
    if failMove then throw (.callback "migration failure")
  memoryOffset := fun _ place offset mode metadata => do
    if mode != .wrapping then throw (.unsupported "fixture offset mode")
    match place.ptr.wrappingOffset offset ⟨Size.ofBytes 8⟩ with
    | .error e => throw (.callback (reprStr e))
    | .ok ptr => return { place with ptr, metadata }
  writeLocalImmediate := fun _ id layout value =>
    placeWriteLocalImmediate (return (← get).frame)
      (fun frame => modify fun s => {s with frame}) (pure false)
      (fun _ storage => if storage then throw (.invalidProgram "ordinary write got storage-live") else emit "local-write")
      (fun value layout => do
        match value, layout.layout.backendRepr with
        | .uninit, _ => pure ()
        | .scalar a, .Scalar _ =>
          if a.size != layout.layout.size || a.isPointer then throw (.invalidProgram "scalar ABI")
        | .scalarPair a b, .ScalarPair .. =>
          if a.size != Size.ofBytes 4 || b.size != Size.ofBytes 4 || a.isPointer || b.isPointer then
            throw (.invalidProgram "pair ABI")
        | _, _ => throw (.invalidProgram "fixture immediate ABI")) id layout value
  enforceValidity := fun _ _ => pure true
  validate := fun _ _ => emit "validate" }

private def memoryCopyHooks : MemoryCopyHooks AllocId Unit Unit (Array String) Unit := {
  synchronizeMemory := fun _ state => state
  pointerAccess := fun memory s ptr size => match ptr.provenance with
    | some id => ⟨memory,s.push "copy-access",.ok (if size.bytes == 0 then none else some (id, ptr.offset, ()))⟩
    | none => ⟨memory,s,.error "no exposed copy pointers"⟩
  tryGetAllocId := fun _ _ ptr _ => ptr.provenance
  beforeAllocationAccess := fun memory s _ => ⟨memory,s.push "copy-allocation",.ok ()⟩
  beforeMemoryRead := fun s memory _ _ _ _ _ => ⟨memory, s.push "copy-read", .ok ()⟩
  beforeMemoryWrite := fun s memory _ _ _ _ _ => ⟨memory, s.push "copy-write", .ok ()⟩ }
private def copyHooks : PlaceCopyHooks AllocId S Unit := {
  compatible := fun a b => .ok (a == b)
  hasPadding := fun _ => .ok true
  readRaw := fun _ op => placeReadRaw context S.memory S.events putMemory (fun s _ => s) op
  memoryCopy := fun _ src dest =>
    placeMemoryCopy true (Size.ofBytes 8)
      (fun place => pure (some (place.layout.layout.size, place.layout.layout.align.abi)))
      memoryCopyHooks S.memory S.events putMemory src dest
  validateSource := fun _ _ _ => emit "validate-source" }

private def fixtureBodies : Array MIR.Body := #[
  ⟨.Built, 0, none, #[pairLayout.ty, pairLayout.ty], #[]⟩,
  ⟨.Built, 0, none, #[3, 3], #[]⟩]
private def fixtureLoaded (key : Fin fixtureBodies.size) : LoadedBody :=
  ⟨BodyIdentity.ofCanonicalIndex key.val, fixtureBodies[key]⟩
private def fixtureIdentity : LocalsIdentity := (LocalsIdentitySupply.allocate ⟨0⟩).2
private def initial : Except StepError S := do
  let a ← scalar 10
  let b ← scalar 20
  let frame : Frame AllocId LocalLayout Nat := {
    body := (fixtureLoaded ⟨0, by decide⟩).body, bodyIdentity := (fixtureLoaded ⟨0, by decide⟩).identity, localsIdentity := fixtureIdentity, functionInstance := ⟨.Item 0, #[]⟩, extra := 0
    returnContinuation := .stop true, returnPlace := .frameLocal 0 0 none pairLayout fixtureIdentity
    locals := #[⟨.live (.immediate (.scalarPair a b)), some pairLayout⟩,
      ⟨.live (.immediate .uninit), some pairLayout⟩]
    vaList := #[], trackCallerArg := none, location := .unwinding ⟨0⟩ }
  return ⟨frame, .empty, #[]⟩

private def run (action : PlaceM S A) (s : S) : IO (A × S) := do
  match action s with
  | .ok value s => return (value, s)
  | .error e _ => throw (IO.userError s!"{repr e}")

def main : IO Unit := do
  let s ← match initial with | .ok s => pure s | .error e => throw (IO.userError (reprStr e))
  let (dest, s) ← run (evalPlace (hooks false) () ⟨0, #[.Field 1 1]⟩ false) s
  unless s.memory.live.isEmpty do throw (IO.userError "projection eagerly allocated")
  let (_, s) ← run (writePlaceImmediate (hooks false) () (.scalar (← match scalar 99 with
    | .ok x => pure x | .error e => throw (IO.userError (reprStr e)))) dest) s
  unless s.frame.extra == 1 do throw (IO.userError "migration lost frame extra")
  let (.ok slot) := s.frame.getLocal 0 | throw (IO.userError "local")
  unless slot.layout == some pairLayout do throw (IO.userError "layout cache lost")
  let (memory, s) ← run (forceAllocation (hooks false) () ⟨.local 0 0 none fixtureIdentity, pairLayout⟩) s
  let (read, _) ← run (placeReadRaw context S.memory S.events putMemory (fun s _ => s) ⟨.indirect memory.mplace, pairLayout⟩) s
  let .immediate value := read | throw (IO.userError "pair read")
  let .scalarPair a b := value.value | throw (IO.userError "pair shape")
  unless a == (← match scalar 10 with | .ok x => pure x | .error _ => throw (IO.userError "scalar")) &&
      b == (← match scalar 99 with | .ok x => pure x | .error _ => throw (IO.userError "scalar")) do
    throw (IO.userError "materialization did not preserve old field")
  match forceAllocation (hooks true) () ⟨.local 0 0 none fixtureIdentity, pairLayout⟩ (← match initial with
      | .ok s => pure s | .error _ => throw (IO.userError "initial")) with
  | .ok _ _ => throw (IO.userError "migration failure succeeded")
  | .error _ state =>
    unless state.frame.extra == 1 && state.memory.live.size == 1 do
      throw (IO.userError "migration failure lost effects")
    let .ok (.immediate _) := state.frame.getLocalOperand 0 | throw (IO.userError "local replaced before hook success")
  let big : LocalLayout := ⟨3, { pairLayout.layout with size := Size.ofBytes 12, backendRepr := .Memory (sized := true) }⟩
  let nextFrame := { s.frame with
    body := (fixtureLoaded ⟨1, by decide⟩).body
    bodyIdentity := (fixtureLoaded ⟨1, by decide⟩).identity
    localsIdentity := (LocalsIdentitySupply.allocate ⟨1⟩).2
    locals := #[⟨.live (.immediate .uninit), some big⟩,
      ⟨.live (.immediate .uninit), some big⟩] }
  let s := { s with frame := nextFrame }
  let (source, s) ← run ((hooks false).allocateStack () big) s
  let some id := source.mplace.ptr.provenance | throw (IO.userError "source provenance")
  let allocation ← match Allocation.fromBytes (Prov := AllocId) #[1,2,3,4,5,6,7,8,9,10,11,12] ⟨2⟩ .Mut with
    | .ok a => pure a | .error _ => throw (IO.userError "source bytes")
  let memory ← match s.memory.setLiveAllocation id allocation with
    | .ok m => pure m | .error _ => throw (IO.userError "source install")
  let s := { s with memory }
  let (_, s) ← run (copyRuntimePlace (hooks false) copyHooks () ⟨.indirect source.mplace, big⟩
    ⟨.local 0 1 none s.frame.localsIdentity, big⟩ false) s
  let (target, s) ← run (forceAllocation (hooks false) () ⟨.local 0 1 none s.frame.localsIdentity, big⟩) s
  let some targetId := target.mplace.ptr.provenance | throw (IO.userError "target provenance")
  let some entry := s.memory.live.find? (fun e => e.1 == targetId) | throw (IO.userError "target allocation")
  let bytes ← match entry.2.allocation.getBytesUnchecked (allocRange Size.ZERO (Size.ofBytes 12)) with
    | .ok bytes => pure bytes | .error _ => throw (IO.userError "target read")
  unless bytes == #[1,2,3,4,5,6,7,8,9,10,11,12] do throw (IO.userError "slow memory copy bytes")
  IO.println "place projection, materialization, write/read and failure effects passed"
