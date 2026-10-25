import Miri.Interpreter.Stack
open Miri.Interpreter Miri.Memory Miri.ABI Miri.MIR

def fixtureBody : Body := ⟨.Built, 0, none, #[0, 0], #[]⟩
def fixtureBodies : Array Body := #[fixtureBody]
def fixtureLoaded : LoadedBody := ⟨BodyIdentity.ofCanonicalIndex 0, fixtureBodies[0]⟩
def returnLayout : LocalLayout := ⟨fixtureBody.locals[0], {
    fields := .Primitive, variants := .Single 0, backendRepr := .Memory (sized := true),
    largestNiche := none, uninhabited := false, align := .new Align.ONE, size := Size.ZERO,
    maxReprAlign := none, unadjustedAbiAlign := Align.ONE, reprC := false, randomizationSeed := 0 }⟩

def fixtureIdentity : LocalsIdentity := (LocalsIdentitySupply.allocate ⟨0⟩).2
def frame (value : LocalValue Unit) : Frame Unit Bool Unit :=
  { body := fixtureLoaded.body
    bodyIdentity := fixtureLoaded.identity
    functionInstance := ⟨.Item 0, #[]⟩
    extra := ()
    returnContinuation := .stop true
    returnPlace := .frameLocal 0 0 none returnLayout fixtureIdentity
    localsIdentity := fixtureIdentity
    locals := #[⟨.dead, none⟩, ⟨value, some true⟩]
    vaList := #[]
    trackCallerArg := none
    location := .unwinding ⟨0⟩ }

def hooks (fail : Bool) : LocalStorageHooks Unit Bool Unit Nat :=
  { veryTriviallySized := fun _ => .ok true
    layout := fun state _ _ => ⟨state, .ok true⟩
    isSized := id
    afterLocalWrite := fun state _ _ => ⟨state + 10, .ok ()⟩
    allocateDyn := fun state _ _ => ⟨state, .error (.allocationFailure "test")⟩
    deallocateStack := fun state _ =>
      ⟨state + 1, if fail then .error (.deallocationFailure "test") else .ok ()⟩ }

def main : IO Unit := do
  let values : Array (LocalValue Unit) := #[.dead, .live (.immediate .uninit),
    .live (.indirect ⟨⟨Size.ofBytes 0, some ()⟩, .none, none⟩)]
  for (value, index) in values.toList.zipIdx do
    for fail in [false, true] do
      let result := (frame value).storageDead 0 (hooks fail) 1
      let .ok slot := result.frame.getLocal 1 | throw (IO.userError "local")
      IO.println s!"D {index} {fail} {result.state} {result.outcome.isOk} {slot.value == .dead} {slot.layout == some true}"
      let live := (frame value).storageLive 0 (hooks fail) 1
      let .ok slot := live.frame.getLocal 1 | throw (IO.userError "local")
      IO.println s!"L {index} {fail} {live.state} {live.outcome.isOk} {slot.value == .live (.immediate .uninit)} {slot.layout == some true}"
