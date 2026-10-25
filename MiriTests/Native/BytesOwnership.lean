import Miri.Interpreter.NativeAllocBytes

open Miri.Interpreter

private structure HostState where
  released : Array (Nat × NativeIsolatedAlloc.Layout) := #[]

private structure IsolatedState where
  storage : NativeIsolatedAlloc.Storage := ⟨4096,#[],#[]⟩
  releasedPages : Array (Nat × Nat) := #[]

private def host (pointer : Nat) (failCopy : Bool) : NativeAllocBytes.GlobalHost HostState := {
  hostBits := 64
  allocate := fun _ _ => pure pointer
  deallocate := fun pointer layout => do
    modify fun state => {state with released := state.released.push (pointer,layout)}
  copyFrom := fun _ _ => if failCopy then throw (.callback "host copy failed") else pure ()
  read := fun _ length => pure (Array.replicate length (0 : UInt8)) }

private def isolatedHost : NativeAllocBytes.Host IsolatedState := {
  allocator := {
    hostBits := 64
    sysconfPageSize := pure 4096
    mmapAnonymousReadWrite := fun _ => pure 4096
    munmap := fun address size => do
      modify fun state => {state with releasedPages := state.releasedPages.push (address,size)}
      pure 0
    zero := fun _ _ => pure () }
  copyFrom := fun _ _ => throw (.callback "isolated copy failed")
  read := fun _ length => pure (Array.replicate length (0 : UInt8)) }

private def isolatedAccess : NativeIsolatedAlloc.Access IsolatedState where
  get := IsolatedState.storage
  put := fun state storage => {state with storage}

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def main : IO Unit := do
  let isolated := (NativeAllocBytes.fromBytes isolatedAccess isolatedHost #[1,2] 1).run {}
  match isolated with
  | .ok _ _ => throw (IO.userError "isolated host copy failure must propagate")
  | .error error state => do
    if error != .callback "isolated copy failed" then
      throw (IO.userError s!"isolated copy error changed: {reprStr error}")
    check (state.releasedPages == #[(4096,4096)]) "isolated failed copy must munmap its owning page"
    check state.storage.pages.isEmpty "isolated failed copy retained its allocation bitmap owner"
  let copied := (NativeAllocBytes.globalFromBytes (host 4096 true) #[1,2] 1).run {}
  match copied with
  | .ok _ _ => throw (IO.userError "host copy failure must propagate")
  | .error error state => do
    if error != .callback "host copy failed" then
      throw (IO.userError s!"copy error changed: {reprStr error}")
    check (state.released.size == 1) "failed copy must release its fresh native owner exactly once"
    let some (pointer,layout) := state.released[0]? | throw (IO.userError "released owner vanished")
    check (pointer == 4096 && layout.size == 2 && layout.align == 1)
      "failed copy released the wrong owner or adjusted layout"
  let badPointerHost := {host 256 false with hostBits := 8}
  let allocated := (NativeAllocBytes.globalAllocate badPointerHost ⟨1,1⟩ false).run {}
  match allocated with
  | .ok _ _ => throw (IO.userError "out-of-range native pointer must fail")
  | .error error state => do
    if error != .invalidProgram "global native allocator returned non-usize pointer" then
      throw (IO.userError s!"pointer-width error changed: {reprStr error}")
    check (state.released.size == 1) "invalid returned pointer must be released"
    let some (pointer,layout) := state.released[0]? | throw (IO.userError "invalid owner release vanished")
    check (pointer == 256 && layout.size == 1 && layout.align == 1)
      "invalid pointer cleanup used the wrong host layout"
  IO.println "Native backing allocation failure prefixes: PASS"
