import Miri.Interpreter.Place
open Miri Miri.ABI Miri.Memory Miri.Interpreter
private def layout : LocalLayout := ⟨0, ⟨.Arbitrary #[] #[], .Single 0, .Memory (sized := true),
  none, false, ⟨.ONE⟩, Size.ofBytes 8, none, .ONE, false, 0⟩⟩
private structure S where
  frame : Frame AllocId LocalLayout Unit
  events : Array String := #[]
  fail : Bool
  marker : Scalar AllocId
private def emit (e : String) : PlaceM S Unit := modify fun s => {s with events := s.events.push e}
private def h : PlaceHooks AllocId S Unit Unit := {
  debugAssertions := false
  getFrame := return (← get).frame
  setFrame := fun frame => modify fun s => {s with frame}
  frameIndex := pure 0
  resolveLayout := fun _ _ => pure layout
  localToOp := fun _ _ => throw (.unsupported "unused")
  projection := fun _ => throw (.unsupported "unused")
  deref := fun _ _ _ => throw (.unsupported "unused")
  checkPlaceType := fun _ _ _ => throw (.unsupported "unused")
  allocateStack := fun _ layout => do
    emit "allocate"
    return ⟨⟨⟨Size.ZERO, none⟩, .metadata (← get).marker, none⟩, layout⟩
  writeMemoryNoValidate := fun _ _ _ => emit "write"
  afterLocalMovedToMemory := fun _ _ _ => do
    emit "moved"
    if (← get).fail then throw (.callback "moved")
  memoryOffset := fun _ place offset _ _ => do
    emit "offset"
    return {place with ptr := {place.ptr with offset}, metadata := .none}
  writeLocalImmediate := fun _ _ _ _ => throw (.unsupported "unused")
  enforceValidity := fun _ _ => throw (.unsupported "unused")
  validate := fun _ _ => throw (.unsupported "unused") }
private def fixtureBodies : Array MIR.Body := #[⟨.Built, 0, none, #[layout.ty], #[]⟩]
private def fixtureLoaded : LoadedBody := ⟨BodyIdentity.ofCanonicalIndex 0, fixtureBodies[0]⟩
private def fixtureIdentity : LocalsIdentity := (LocalsIdentitySupply.allocate ⟨0⟩).2
private def frame (operand : Operand AllocId) : Frame AllocId LocalLayout Unit := {
  body := fixtureLoaded.body, bodyIdentity := fixtureLoaded.identity, localsIdentity := fixtureIdentity, functionInstance := ⟨.Item 0, #[]⟩, extra := ()
  returnContinuation := .stop true, returnPlace := .frameLocal 0 0 none layout fixtureIdentity
  locals := #[⟨.live operand, some layout⟩], vaList := #[], trackCallerArg := none,
  location := .unwinding ⟨0⟩ }
def main : IO Unit := do
  let marker ← match Scalar.fromUInt (Prov := AllocId) (BitVec.ofNat 128 7) (Size.ofBytes 4) with
    | .ok scalar => pure scalar | .error _ => throw (IO.userError "marker")
  for initial in [:3] do
    for fail in [false,true] do
      for projected in [false,true] do
        let operand := match initial with
          | 0 => Operand.immediate .uninit
          | 1 => .immediate (.scalar marker)
          | _ => .indirect ⟨⟨Size.ZERO, none⟩, .metadata marker, none⟩
        let result := forceAllocation h () ⟨.local 0 0 (if projected then some (Size.ofBytes 4) else none) fixtureIdentity, layout⟩
          ⟨frame operand, #[], fail, marker⟩
        let (ok, metadataValue, state) := match result with
          | .ok place state => (true, if place.mplace.metadata.hasMeta then 7 else 0, state)
          | .error _ state => (false, 99, state)
        let indirect := match state.frame.getLocalOperand 0 with
          | .ok (.indirect _) => true | _ => false
        IO.println s!"{initial} {fail} {projected} {ok} {indirect} {metadataValue} {String.intercalate "," state.events.toList}"
