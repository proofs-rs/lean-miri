import Miri.Interpreter.HostStdioReplay

/-! Actual pinned-Rust standard streams. Private wire records are checked before
becoming guest observations. These IO externs have explicit failing fallbacks;
there is no pure host axiom or simulated successful write. -/
namespace NativeStdioHost
open Miri.Interpreter
@[extern "lean_miri_stdio_write"] private def rawWrite (_stream : UInt32) (_bytes : @& ByteArray) : IO ByteArray :=
  throw (IO.userError "unsupported native stdio write bridge")
@[extern "lean_miri_stdio_flush"] private def rawFlush : IO ByteArray :=
  throw (IO.userError "unsupported native stdout flush bridge")
@[extern "lean_miri_stdio_adopt"] private def rawAdopt (_fd : UInt32) : IO ByteArray :=
  throw (IO.userError "unsupported native control adoption bridge")
@[extern "lean_miri_stdio_control"] private def rawControl (_bytes : @& ByteArray) : IO ByteArray :=
  throw (IO.userError "unsupported native control write bridge")
@[extern "lean_miri_stdio_close"] private def rawClose : IO ByteArray :=
  throw (IO.userError "unsupported native control close bridge")

private def kind (code : Nat) : Option IoError.ErrorKind := match code with
  | 1 => some .ArgumentListTooLong
  | 2 => some .AddrInUse
  | 3 => some .AddrNotAvailable
  | 4 => some .ResourceBusy
  | 5 => some .ConnectionAborted
  | 6 => some .ConnectionRefused
  | 7 => some .ConnectionReset
  | 8 => some .Deadlock
  | 9 => some .QuotaExceeded
  | 10 => some .AlreadyExists
  | 11 => some .FileTooLarge
  | 12 => some .HostUnreachable
  | 13 => some .Interrupted
  | 14 => some .InvalidInput
  | 15 => some .IsADirectory
  | 16 => some .FilesystemLoop
  | 17 => some .NotFound
  | 18 => some .OutOfMemory
  | 19 => some .StorageFull
  | 20 => some .TooManyLinks
  | 21 => some .InvalidFilename
  | 22 => some .NetworkDown
  | 23 => some .NetworkUnreachable
  | 24 => some .NotConnected
  | 25 => some .NotADirectory
  | 26 => some .DirectoryNotEmpty
  | 27 => some .BrokenPipe
  | 28 => some .ReadOnlyFilesystem
  | 29 => some .NotSeekable
  | 30 => some .StaleNetworkFileHandle
  | 31 => some .TimedOut
  | 32 => some .ExecutableFileBusy
  | 33 => some .CrossesDevices
  | 34 => some .InProgress
  | 35 => some .InputOutputError
  | 36 => some .PermissionDenied
  | 37 => some .WouldBlock
  | 38 => some .Unsupported
  | 39 => some .TooManyOpenFiles
  | 40 => some .Other
  | _ => none

private def word (bytes : ByteArray) (start count : Nat) : Nat :=
  (List.range count).foldl (fun result i => result + bytes[start+i]!.toNat * 256^i) 0

/-- Checked IO boundary exposed for malformed-wire regression tests. -/
def decodeResponse (bytes : ByteArray) : IO (Except HostStdio.Error Nat) := do
  unless bytes.size == 24 do throw (IO.userError "invalid native stdio result length")
  let status := word bytes 0 4
  let code := word bytes 4 4
  let hasRaw := word bytes 8 4
  let raw := word bytes 12 4
  let count := word bytes 16 8
  if status == 0 then
    unless code == 0 && hasRaw == 0 && raw == 0 do
      throw (IO.userError "invalid native stdio success fields")
    return .ok count
  unless status == 1 && hasRaw <= 1 && count == 0 do
    throw (IO.userError "unsupported native stdio error kind or bridge failure")
  let some value := kind code | throw (IO.userError "unsupported native stdio error kind")
  unless hasRaw == 1 || raw == 0 do throw (IO.userError "invalid absent native errno")
  return .error {kind := value, raw := if hasRaw == 1 then some (Int32.ofInt (if raw < 2147483648 then Int.ofNat raw else Int.ofNat raw - 4294967296)) else none}

def writeOnce (stream : HostStdio.Stream) (bytes : @& ByteArray) : IO (Except HostStdio.Error Nat) := do
  let result ← decodeResponse (← rawWrite (match stream with | .stdout => 0 | .stderr => 1) bytes)
  if let .ok count := result then
    unless count <= bytes.size do throw (IO.userError "native stdio write count exceeds request")
  return result

def flushStdout : IO (Except HostStdio.Error Unit) := do
  match ← decodeResponse (← rawFlush) with
  | .ok 0 => return .ok ()
  | .ok _ => throw (IO.userError "invalid native stdout flush count")
  | .error error => return .error error

private def controlResult (result : Except HostStdio.Error Nat) (expected : Nat) : IO Unit := do
  match result with
  | .ok count => unless count == expected do throw (IO.userError "invalid native control count")
  | .error error => throw (IO.userError s!"native control I/O failed: {reprStr error}")

def adoptControl (fd : UInt32) : IO Unit := do
  controlResult (← decodeResponse (← rawAdopt fd)) 0

def writeControlAll (bytes : @& ByteArray) : IO Unit := do
  controlResult (← decodeResponse (← rawControl bytes)) bytes.size

def closeControl : IO Unit := do
  controlResult (← decodeResponse (← rawClose)) 0
end NativeStdioHost
