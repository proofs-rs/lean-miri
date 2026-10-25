import Miri.Input.EvalWindowsRunConstruction

open Miri.Input.EvalWindowsRunConstruction
open Miri.Interpreter Miri.Concurrency

private def source : BlockingIo.Source :=
  { fd := ⟨⟨1⟩⟩ }

private def live : FileOwnership.Registry Nat :=
  { entries := #[⟨⟨⟨1⟩, 7⟩, 1⟩] }

private def watcher : ReadinessMachine.WatcherEntry :=
  ⟨10, 1, { queue := #[ThreadId.MAIN_THREAD] }⟩

private def readiness : ReadinessMachine.Registry Nat :=
  { watchers := #[watcher], watched := #[(⟨1⟩, { watchers := #[10] })] }

private def virtualOnly : BlockingIo.Manager Unit :=
  { poll := some (), sources := #[] }

private def hostSource : BlockingIo.Manager Unit :=
  { poll := some (), sources := #[(⟨1⟩, source)] }

private def directHostBlock : BlockingIo.Manager Unit :=
  { poll := some (), sources := #[(⟨1⟩, { source with blocked := #[(ThreadId.MAIN_THREAD, .read)] })] }

def main : IO Unit := do
  if needsHostIo virtualOnly readiness live then
    throw (IO.userError "virtual-only watcher incorrectly needs host polling")
  unless needsHostIo hostSource readiness live do
    throw (IO.userError "live host-source watcher was missed")
  if needsHostIo hostSource readiness ({} : FileOwnership.Registry Nat) then
    throw (IO.userError "closed host-source watcher incorrectly needs polling")
  unless needsHostIo directHostBlock readiness live do
    throw (IO.userError "direct host block was missed")
  IO.println "Windows host IO demand PASS: virtual, host watcher, closed source, direct block"
