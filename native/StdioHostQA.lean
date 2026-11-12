import NativeStdioHost
open Miri.Interpreter
private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)
private def rejected (action : IO Unit) : IO Unit := do
  let failed ← try action; pure false catch _ => pure true
  require failed "expected explicit bridge failure"
private def decodeChecks : IO Unit := do
  -- status=error, kind=Interrupted, raw present, raw=-123, count=0.
  let wire := ByteArray.mk #[1,0,0,0,13,0,0,0,1,0,0,0,133,255,255,255,0,0,0,0,0,0,0,0]
  match ← NativeStdioHost.decodeResponse wire with
  | .error e => require (e.kind == .Interrupted && e.raw == some (-123 : Int32)) "signed errno bits lost"
  | .ok _ => throw (IO.userError "error became success")
  rejected (do let _ ← NativeStdioHost.decodeResponse (ByteArray.mk #[0]); pure ())
  let unknown := wire.set! 4 0
  rejected (do let _ ← NativeStdioHost.decodeResponse unknown; pure ())
  let badPresent := wire.set! 8 2
  rejected (do let _ ← NativeStdioHost.decodeResponse badPresent; pure ())
  let panicStatus := wire.set! 0 3
  rejected (do let _ ← NativeStdioHost.decodeResponse panicStatus; pure ())
def main (args : List String) : IO Unit := do
  match args with
  | ["decode"] => decodeChecks
  | ["reject", fd] =>
    let some fd := fd.toNat? | throw (IO.userError "fd parse")
    rejected (NativeStdioHost.adoptControl fd.toUInt32)
  | ["broken"] =>
    let r ← NativeStdioHost.writeOnce .stdout (ByteArray.mk #[66,10])
    let r ← match r with | .error e => pure (.error e) | .ok _ => NativeStdioHost.flushStdout
    match r with
    | .error e => IO.eprintln s!"broken-pipe-error: {reprStr e}"
    | .ok () => throw (IO.userError "closed pipe unexpectedly succeeded")
  | ["normal", fd, controlPath] =>
    let some fd := fd.toNat? | throw (IO.userError "fd parse")
    NativeStdioHost.adoptControl fd.toUInt32
    try
      rejected (NativeStdioHost.adoptControl fd.toUInt32)
      let leaked ← IO.Process.output {cmd := "python3", args := #["-c",
        "import os,sys; p='/proc/self/fd/'; bad=[];\nfor f in os.listdir(p):\n try:\n  if os.readlink(p+f)==sys.argv[1]: bad.append(f)\n except OSError: pass\nsys.exit(bool(bad))", controlPath]}
      unless leaked.exitCode == 0 do throw (IO.userError "control descriptor leaked through exec")
      let out := ByteArray.mk #[0,255,10,65]
      let err := ByteArray.mk #[69,0,254]
      match ← NativeStdioHost.writeOnce .stdout out with
      | .ok n => require (n == out.size) "stdout short fixture write"
      | .error _ => throw (IO.userError "stdout fixture error")
      match ← NativeStdioHost.writeOnce .stderr err with
      | .ok n => require (n == err.size) "stderr short fixture write"
      | .error _ => throw (IO.userError "stderr fixture error")
      match ← NativeStdioHost.flushStdout with
      | .ok () => pure ()
      | .error _ => throw (IO.userError "flush fixture error")
      NativeStdioHost.writeControlAll "control-only\n".toUTF8
    finally NativeStdioHost.closeControl
    rejected (NativeStdioHost.writeControlAll "after-close".toUTF8)
    rejected NativeStdioHost.closeControl
    rejected (NativeStdioHost.adoptControl fd.toUInt32)
    match ← NativeStdioHost.writeOnce .stdout (ByteArray.mk #[90]) with
    | .ok 1 => pure ()
    | _ => throw (IO.userError "closing control affected stdout")
    match ← NativeStdioHost.writeOnce .stderr (ByteArray.mk #[89]) with
    | .ok 1 => pure ()
    | _ => throw (IO.userError "closing control affected stderr")
    match ← NativeStdioHost.flushStdout with
    | .ok () => pure ()
    | _ => throw (IO.userError "post-control-close flush failed")
  | _ => throw (IO.userError "native stdio QA arguments")
