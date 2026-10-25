import Miri.Interpreter.RandomMemory
open Miri Miri.Memory Miri.Interpreter
private structure Trace where
  events : Array String := #[]
private abbrev M := EStateM StepError Trace
private def event (name : String) : M Unit := modify fun s => {s with events := s.events.push name}
private def bytes (n : Nat) : ByteArray := ByteArray.mk (Array.replicate n 7)
private def hooks (host hostError writeError : Bool) : RandomMemory.Hooks Trace where
  communicate := host
  hostUsizeBits := 64
  hostFill := fun n => do
    event "host"
    return if hostError then .error "fixture host failure" else .ok (bytes n)
  isolatedFill := fun n => do event "isolated"; return bytes n
  writeBytes := fun _ data => do
    event s!"write{data.size}"
    if writeError then throw (.undefinedBehavior "fixture write failure")
private def run (host hostError writeError : Bool) (n : Nat) : String :=
  let result := RandomMemory.generate (hooks host hostError writeError) (Pointer.withoutProvenance 0) (UInt64.ofNat n) {}
  let (kind,state) := match result with
    | .ok _ state => ("ok",state)
    | .error (.unsupported _) state => ("unsupported",state)
    | .error (.undefinedBehavior _) state => ("ub",state)
    | .error _ state => ("other",state)
  s!"{n}|{host}|{hostError}|{writeError}|{kind}|{String.intercalate "," state.events.toList}"
def main : IO Unit := do
  for (host,hostError,writeError,n) in [(false,false,false,0),(true,true,true,0),
      (false,false,false,3),(true,false,false,3),(true,true,false,3),(false,false,true,3)] do
    IO.println (run host hostError writeError n)
