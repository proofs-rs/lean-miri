import Miri.Interpreter.Stack
open Miri.Interpreter Miri.Memory Miri.ABI Miri.MIR

def body : Body := ⟨.Built, 0, none, #[0, 0], #[⟨#[], ⟨⟨⟨0⟩, 0⟩, .Return⟩, false⟩]⟩
def fixtureBodies : Array Body := #[body]
def fixtureLoaded : LoadedBody := ⟨BodyIdentity.ofCanonicalIndex 0, fixtureBodies[0]⟩
def returnLayout : LocalLayout := ⟨body.locals[0], {
    fields := .Primitive, variants := .Single 0, backendRepr := .Memory (sized := true),
    largestNiche := none, uninhabited := false, align := .new Align.ONE, size := Size.ZERO,
    maxReprAlign := none, unadjustedAbiAlign := Align.ONE, reprC := false, randomizationSeed := 0 }⟩
def fixtureIdentity : LocalsIdentity := (LocalsIdentitySupply.allocate ⟨0⟩).2
def place : RuntimeStackPlace Unit := .frameLocal 0 0 none returnLayout fixtureIdentity
def storage : LocalStorageHooks Unit Bool Unit Nat :=
  { veryTriviallySized := fun _ => .ok true
    layout := fun s _ _ => ⟨s + 100, .ok true⟩
    isSized := id
    afterLocalWrite := fun s _ _ => ⟨s + 1, .ok ()⟩
    allocateDyn := fun s _ _ => ⟨s, .error (.allocationFailure "test")⟩
    deallocateStack := fun s _ => ⟨s + 10, .ok ()⟩ }
def lifecycle : StackLifecycleHooks Unit Bool Unit Nat :=
  { storage
    freshLocalsIdentity := fun state => (state, (LocalsIdentitySupply.allocate ⟨state⟩).2)
    initFrame := fun s f => ⟨s + 1, .ok f⟩
    requiredConstants := fun st s => ⟨st, s + 10, .ok ()⟩
    afterPush := fun st s => ⟨st, s + 100, .ok ()⟩
    beforePop := fun st s => ⟨st, s + 1000, .ok ()⟩
    afterPop := fun st s _ unwinding => ⟨st, s + (if unwinding then 10000 else 100000), .ok .normal⟩
    alwaysLiveVarsAndTemps := fun _ => .ok #[1]
    deallocateVararg := fun s _ => ⟨s + 1000000, .ok ()⟩ }
def check (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)
def main : IO Unit := do
  let pushed := Stack.empty.pushStackFrameRaw 0 lifecycle fixtureLoaded ⟨.Item 0, #[]⟩ (.stop true) place ⟨0⟩
  check (pushed.outcome.isOk && pushed.state == 111 && pushed.stack.frames.size == 1) "push order"
  let done_ := pushed.stack.pushStackFrameDone pushed.state lifecycle
  check (done_.outcome.isOk && done_.state == 113) "storage initialization"
  let some f := done_.stack.currentFrame? | throw (IO.userError "missing frame")
  check (f.location == .mir .start) "start location"
  let popped := done_.stack.popStackFrameRaw done_.state lifecycle
  let .ok f := popped.outcome | throw (IO.userError "pop")
  check (popped.state == 1113 && popped.stack.frames.isEmpty) "before pop ordering"
  for unwind in [false, true] do
    let cleaned := popped.stack.cleanupStackFrame 0 lifecycle unwind f
    check (cleaned.outcome.isOk && cleaned.state == if unwind then 10000 else 100000) "cleanup hook"
  let skipped := popped.stack.cleanupStackFrame 0 lifecycle true { f with returnContinuation := .stop false }
  check (skipped.outcome == .ok .noCleanup && skipped.state == 0) "skip cleanup"
  let failedHooks := { lifecycle with requiredConstants := fun st s =>
    ⟨st, s + 10, .error (.machineHookFailure "test")⟩ }
  let failed := Stack.empty.pushStackFrameRaw 0 failedHooks fixtureLoaded ⟨.Item 0, #[]⟩ (.stop true) place ⟨0⟩
  check (!failed.outcome.isOk && failed.stack.frames.size == 1 && failed.state == 11) "failed push retains frame"
  let unsizedHooks := { storage with
    veryTriviallySized := fun _ => .ok false
    layout := fun s _ _ => ⟨s + 100, .ok false⟩ }
  let failedLive := f.storageLive 0 unsizedHooks 1
  check (!failedLive.outcome.isOk && failedLive.state == 100) "unsized metadata failure"
  check (failedLive.frame.getLocalLayout 1 == .ok (some false)) "layout cache persists"
  let indirect : LocalValue Unit := .live (.indirect ⟨⟨Size.ofBytes 0, some ()⟩, .none, none⟩)
  let .ok allocatedFrame := f.replaceLocalValue 1 indirect | throw (IO.userError "replace")
  let allocatedFrame := { allocatedFrame with vaList := #[⟨⟨⟨Size.ofBytes 0, some ()⟩, .none, none⟩,
    ⟨Size.ofBytes 0, ⟨0⟩, .Memory (sized := true), none⟩⟩] }
  let cleaned := Stack.empty.cleanupStackFrame 0 lifecycle false allocatedFrame
  check (cleaned.state == 1100010 && cleaned.outcome.isOk) "local vararg cleanup before hook"
  let failStorage := { storage with deallocateStack := fun s _ =>
    ⟨s + 10, .error (.deallocationFailure "test")⟩ }
  let failLifecycle := { lifecycle with storage := failStorage }
  let failedCleanup := Stack.empty.cleanupStackFrame 0 failLifecycle false allocatedFrame
  check (failedCleanup.state == 10 && !failedCleanup.outcome.isOk) "cleanup stops on first error"
  let failWrite := { storage with afterLocalWrite := fun s _ _ =>
    ⟨s + 7, .error (.machineHookFailure "test")⟩ }
  let failedWrite := allocatedFrame.storageLive 0 failWrite 1
  let .ok slot := failedWrite.frame.getLocal 1 | throw (IO.userError "slot")
  check (failedWrite.state == 7 && slot.value == indirect) "failed write hook before replacement"
  IO.println "stack lifecycle and layout-cache checks passed"
