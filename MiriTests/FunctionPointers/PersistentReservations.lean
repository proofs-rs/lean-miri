import Miri.Interpreter.FunctionPointers

open Miri.Interpreter Miri.Memory
open Miri.Interpreter.FunctionPointers

private def id1 : AllocId := ⟨1, by decide⟩
private def id2 : AllocId := ⟨2, by decide⟩
private def instance1 : CallInstance := ⟨.Item 10, #[]⟩
private def instance2 : CallInstance := ⟨.Item 11, #[]⟩
private def entry (callee : CallInstance) (id : AllocId) : FunctionEntry :=
  ⟨callee, ⟨0, by decide⟩, id⟩

#eval show IO Unit from do
  let imported := entry instance1 id1
  let runtime := entry instance2 id2
  let fresh : Registry Unit := ⟨#[imported], #[]⟩
  let live : Registry Unit := ⟨#[imported, runtime], #[(id1, ())]⟩
  let merged ← match Registry.mergePersistent fresh live with
    | .ok merged => pure merged
    | .error error => throw (IO.userError s!"valid TCX reservations failed to merge: {error}")
  unless merged.functions.size == 2 && merged.extras.isEmpty do
    throw (IO.userError "persistent function identities or per-world extras were mishandled")
  let conflictingKey : Registry Unit := ⟨#[entry instance1 id2], #[]⟩
  match Registry.mergePersistent fresh conflictingKey with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "conflicting function identity was silently replaced")
  let conflictingId : Registry Unit := ⟨#[entry instance2 id1], #[]⟩
  match Registry.mergePersistent fresh conflictingId with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "one AllocId was assigned to multiple function keys")
