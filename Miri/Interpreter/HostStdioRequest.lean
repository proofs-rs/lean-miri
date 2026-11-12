/-! Requests contain only already checked bytes and standard stream identity.
They grant no access to arbitrary host descriptors or paths. -/
namespace Miri.Interpreter.HostStdio

inductive Stream where
  | stdout | stderr
  deriving Repr, DecidableEq

inductive Request where
  | write (stream : Stream) (bytes : ByteArray)
  | flushStdout
  deriving DecidableEq

instance : Repr Request where
  reprPrec request _ := match request with
    | .write stream bytes => s!"HostStdio.write {reprStr stream} {reprStr bytes.data}"
    | .flushStdout => "HostStdio.flushStdout"

structure Pending where
  ordinal : Nat
  request : Request
  deriving Repr, DecidableEq

end Miri.Interpreter.HostStdio
