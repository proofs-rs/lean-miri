import Miri.Input.EvalTimeConstruction

open Miri.ABI Miri.Memory Miri.Interpreter Miri.Input

namespace TimezoneGuestEnvFixture

structure GuestEnv where
  values : EnvVars.State (Option Provenance) String
  tzValue : String
  reads : Nat

def hooks : EnvVars.Hooks (Option Provenance) String GuestEnv := {
  family := .unix
  get := do return (← get).values
  put := fun values => modify fun state => {state with values}
  encodeUnix := fun value => pure value.toUTF8
  decodeUnix := fun bytes =>
    match String.fromUTF8? bytes with
    | some value => pure value
    | none => throw (.invalidProgram "fixture invalid UTF-8")
  emptyOs := ""
  concatOs := (· ++ ·)
  asciiOs := id
  isEmpty := String.isEmpty
  containsEquals := fun value => value.contains '='
  nullPointer := Pointer.null
  isNull := fun _ => pure true
  readCString := fun _ => do
    let state ← get
    modify fun state => {state with reads := state.reads + 1}
    pure state.tzValue.toUTF8
  allocCString := fun _ _ => pure Pointer.null
  allocPointerCell := fun _ => pure Pointer.null
  allocPointerArray := fun _ _ => pure Pointer.null
  projectPointerElement := fun _ _ _ => pure Pointer.null
  readPointer := fun _ => do
    modify fun state => {state with reads := state.reads + 1}
    pure Pointer.null
  writePointer := fun _ _ => pure ()
  offset := fun pointer _ => pure pointer
  deallocate := fun _ _ => pure ()
  invalidArgument := pure 22
  readWideString := fun _ => pure ""
  writeWideString := fun _ _ _ => pure (false,0)
  allocWideString := fun _ _ => pure Pointer.null
  envVarNotFound := pure () }

def guestVars : EnvVars.State (Option Provenance) String :=
  .unix ⟨#[("TZ".toUTF8, Pointer.null)], Pointer.null⟩

def readTimezone := EvalTimeConstruction.guestTimezone hooks
  (fun value => if value == "<non-unicode>" then .error () else .ok value)

def readAfterMutation : EStateM StepError GuestEnv
    (Option (Except Unit String) × Option (Except Unit String)) := do
  let first ← readTimezone
  modify fun state => {state with tzValue := "Guest/AfterMutation"}
  let second ← readTimezone
  pure (first,second)

def valueAfter (action : EStateM StepError GuestEnv A) (state : GuestEnv) : Option A :=
  match action.run state with
  | .ok value _ => some value
  | .error _ _ => none

def stateAfter (action : EStateM StepError GuestEnv A) (state : GuestEnv) : Option GuestEnv :=
  match action.run state with
  | .ok _ final => some final
  | .error _ _ => none

def initial : GuestEnv := ⟨guestVars, "Guest/Initial", 0⟩
def absent : GuestEnv := ⟨.unix ⟨#[], Pointer.null⟩, "ignored", 0⟩
def invalidUnicode : GuestEnv := ⟨guestVars, "<non-unicode>", 0⟩
def hostTimezone := "Host/Environment"

example : valueAfter readTimezone initial = some (.some (.ok "Guest/Initial")) := by rfl
example : valueAfter readAfterMutation initial =
    some (.some (.ok "Guest/Initial"), .some (.ok "Guest/AfterMutation")) := by rfl
example : valueAfter readTimezone absent = some none := by rfl
example : valueAfter readTimezone invalidUnicode = some (.some (.error ())) := by rfl
example : hostTimezone != "Guest/Initial" := by decide
example : (valueAfter readTimezone initial).isSome := by decide
example : (stateAfter readTimezone initial).map GuestEnv.reads = some 2 := by rfl

end TimezoneGuestEnvFixture
