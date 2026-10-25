import Miri.Interpreter.LocalAccess
open Miri.Interpreter Miri.Memory Miri.ABI

def layout : LocalLayout := ⟨17, ⟨.Arbitrary #[] #[], .Single 0, .Memory (sized := true), none, false, ⟨.ONE⟩, Size.ZERO, none, .ONE, false, 0⟩⟩
def fixtureBodies : Array Miri.MIR.Body := #[⟨.Built, 0, none, #[layout.ty], #[]⟩]
def fixtureLoaded : LoadedBody := ⟨BodyIdentity.ofCanonicalIndex 0, fixtureBodies[0]⟩
def fixtureIdentity : LocalsIdentity := (LocalsIdentitySupply.allocate ⟨0⟩).2
def frame (value : LocalValue Unit) (cached : Bool) : Frame Unit LocalLayout Unit :=
  { body := fixtureLoaded.body
    bodyIdentity := fixtureLoaded.identity
    localsIdentity := fixtureIdentity
    functionInstance := ⟨.Item 0, #[]⟩, extra := (), returnContinuation := .stop true
    returnPlace := .frameLocal 0 0 none layout fixtureIdentity
    locals := #[⟨value, if cached then some layout else none⟩]
    vaList := #[], trackCallerArg := none, location := .unwinding ⟨0⟩ }
def hooks (validation fail : Bool) : LocalAccessHooks Unit Unit (Array String) :=
  { layout := fun f s _ _ => ⟨f, s.push "layout", .ok layout⟩
    validationInProgress := fun _ => validation
    afterLocalRead := fun f s _ => ⟨f, s.push "read",
      if fail then .error (.resolver "read failed") else .ok ()⟩
    project := fun f s _ _ => ⟨f, s.push "project", .error (.resolver "projection required")⟩
    checkPlaceType := fun f s _ _ => ⟨f, s.push "check", .ok ()⟩
    runtimeChecks := fun f s _ => ⟨f, s, .error (.resolver "runtime checks required")⟩
    constant := fun f s _ _ => ⟨f, s, .error (.resolver "constant required")⟩ }

def main : IO Unit := do
  for cached in [false, true] do
    for validation in [false, true] do
      let dead := localToOp (hooks validation false) (frame .dead cached) #[] 0 none
      unless dead.state == (if cached then #[] else #["layout"]) && !dead.outcome.isOk do
        throw (IO.userError "dead access order")
      let live := localToOp (hooks validation false) (frame (.live (.immediate .uninit)) cached) #[] 0 none
      let expected := (if cached then #[] else #["layout"]) ++ (if validation then #[] else #["read"])
      unless live.state == expected && live.outcome.isOk do throw (IO.userError "read hook order")
      let indirect := localToOp (hooks validation true)
        (frame (.live (.indirect ⟨⟨Size.ZERO, some ()⟩, .none, none⟩)) cached) #[] 0 none
      unless indirect.outcome.isOk && indirect.state == (if cached then #[] else #["layout"]) do
        throw (IO.userError "indirect must avoid local read hook")
  let failed := localToOp (hooks false true) (frame (.live (.immediate .uninit)) false) #[] 0 none
  unless failed.state == #["layout", "read"] && !failed.outcome.isOk do
    throw (IO.userError "hook failure effects")
  let .ok slot := failed.frame.getLocal 0 | throw (IO.userError "missing local")
  unless slot.layout == some layout do throw (IO.userError "cache lost after failure")
  IO.println "local access ordering, validation, indirect, and partial-state checks passed"

def copyHooks (compat padding failForce : Bool) : LocalCopyHooks Unit Unit (Array String) LocalLayout :=
  { destinationLayout := id
    compatible := fun _ _ => .ok compat
    hasPadding := fun _ => .ok padding
    readRaw := fun f s _ => ⟨f, s.push "raw", .ok (.immediate ⟨.uninit, localMemoryLayout layout⟩)⟩
    writeImmediate := fun f s _ _ => ⟨f, s.push "write", .ok ()⟩
    forceDestination := fun f s _ => ⟨f, s.push "force",
      if failForce then .error (.resolver "force failed")
      else .ok ⟨⟨⟨Size.ZERO, some ()⟩, .none, none⟩, localMemoryLayout layout⟩⟩
    writeTransmuted := fun f s _ source _ =>
      ⟨f, s.push s!"transmute:{source.ty}", .ok ()⟩
    copyMemory := fun f s _ _ => ⟨f, s.push "memcpy", .ok ()⟩
    validate := fun f s _ _ => ⟨f, s.push "validate", .ok ()⟩ }

example : (copyOperand (copyHooks true true false) (frame .dead true) #[]
    ⟨.immediate .uninit, layout⟩ layout false).state = #["write", "validate"] := by decide
example : (copyOperand (copyHooks true false false) (frame .dead true) #[]
    ⟨.immediate .uninit, layout⟩ layout false).state = #["raw", "write", "validate"] := by decide
example : (copyOperand (copyHooks false true false) (frame .dead true) #[]
    ⟨.immediate .uninit, layout⟩ layout true).state = #["force", "transmute:17", "validate"] := by decide
example : (copyOperand (copyHooks true true false) (frame .dead true) #[]
    ⟨.indirect ⟨⟨Size.ZERO, some ()⟩, .none, none⟩, layout⟩ layout false).state =
    #["force", "memcpy", "validate"] := by decide
example : (copyOperand (copyHooks true true true) (frame .dead true) #[]
    ⟨.indirect ⟨⟨Size.ZERO, some ()⟩, .none, none⟩, layout⟩ layout false).state =
    #["force"] := by decide
example : (copyOperand (copyHooks false true false) (frame .dead true) #[]
    ⟨.immediate .uninit, layout⟩ layout false).state = #[] := by decide
