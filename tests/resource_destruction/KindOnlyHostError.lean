import NativeRunner

open Miri.ABI Miri.Memory Miri.Interpreter

namespace KindOnlyHostErrorTest

-- These equalities hold for every kind, not just WouldBlock.
example (kind : IoError.ErrorKind) : (NativeRunnerError.fromKind kind).kind = kind := rfl
example (kind : IoError.ErrorKind) : (NativeRunnerError.fromKind kind).raw = none := rfl
example (kind : IoError.ErrorKind) : (NativeRunnerError.fromKind kind).payload = () := rfl

private def unavailable (message : String) : EStateM StepError Unit A :=
  throw (.unsupported message)
private def hooks : IoError.Hooks Unit Unit := {
  family := .unix, os := "linux", hostUnix := true
  hostErrno := fun _ => unavailable "host errno must not be queried for a simple-kind error"
  -- Deliberately non-OS sentinel: proves the table consumes its target leaf.
  libc := fun name =>
    if name == "EWOULDBLOCK" then
      match Scalar.fromInt 1234 (Size.ofBytes 4) with
      | .ok value => pure value
      | .error _ => unavailable "scalar sentinel construction"
    else unavailable s!"unavailable target constant {name}"
  windows := fun _ => unavailable "Windows constants unavailable"
  scalarI32 := fun _ => unavailable "unused scalar conversion"
  scalarU32 := fun _ => unavailable "unused scalar conversion"
  hostFromRaw := fun _ => unavailable "raw host conversion remains unsupported"
  hostFromKind := fun kind => pure (NativeRunnerError.fromKind kind)
  getLastErrorPlace := unavailable "unused errno place"
  setLastErrorPlace := fun _ => unavailable "unused errno place"
  allocateU32Machine := unavailable "unused errno allocation"
  writeScalar := fun _ _ => unavailable "unused errno write"
  readScalar := fun _ => unavailable "unused errno read"
  writeInt := fun _ _ => unavailable "unused integer write" }

private def check : IO Unit := do
  match IoError.hostErrorToErrnum hooks (NativeRunnerError.fromKind .WouldBlock) () with
  | .ok scalar _ =>
    unless scalar.toInt (Size.ofBytes 4) == .ok 1234 do
      throw (IO.userError "kind translation did not consume the target compiler constant")
  | .error error _ => throw (IO.userError s!"simple-kind translation failed: {reprStr error}")
  match IoError.hostErrorToErrnum hooks (NativeRunnerError.fromKind .Other) () with
  | .error (.unsupported "unsupported host io error") _ => pure ()
  | _ => throw (IO.userError "unmapped kind became a successful errno")
  -- ErrorKind::Unsupported is a guest error kind, not permission to invent an errno.
  match IoError.hostErrorToErrnum hooks (NativeRunnerError.fromKind .Unsupported) () with
  | .error (.unsupported "unavailable target constant ENOSYS") _ => pure ()
  | _ => throw (IO.userError "missing target errno evidence was accepted")
  match hooks.hostFromRaw 11 () with
  | .error (.unsupported "raw host conversion remains unsupported") _ => pure ()
  | _ => throw (IO.userError "raw host conversion became available")
  -- A transcript error with raw errno is not a simple-kind error. Even when
  -- its kind has an available target sentinel, an absent real host errno
  -- table must stop conversion before falling back to that sentinel. The
  -- number here is synthetic input data, not a claimed host errno constant.
  let observed : HostStdio.Error := ⟨.WouldBlock, some 11⟩
  match IoError.hostErrorToErrnum hooks observed.toHost () with
  | .error (.unsupported "host errno must not be queried for a simple-kind error") _ => pure ()
  | _ => throw (IO.userError "raw transcript errno was dropped or guessed from its kind")
  IO.println "simple ErrorKind preserves kind/raw-none/unit; target lookup and unsupported boundaries passed"

#eval check
end KindOnlyHostErrorTest
