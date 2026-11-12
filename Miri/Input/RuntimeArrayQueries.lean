import Miri.Input.RuntimeArrayTypes
import Miri.Interpreter.OsStrings
import Miri.Interpreter.ValidityVisitor

/-! All runtime constructor/query callbacks share the execution-owned universe
stored through this single Access. A query never recreates an initial arena. -/
namespace Miri.Input.RuntimeArrayQueries
open Miri.ABI Miri.Interpreter
structure Access (S : Type) where
  get : S → RuntimeArrayTypes.World
  set : S → RuntimeArrayTypes.World → S
private def failure : RuntimeArrayTypes.Error → StepError
  | .metadata reason => .unsupported s!"runtime type universe query: {reason}"
  | .missingRuntimeType id => .unsupported s!"missing runtime type {id}"
  | error => .invalidProgram s!"runtime type constructor/layout: {reprStr error}"
private def lift (value : Except RuntimeArrayTypes.Error α) : EStateM StepError S α :=
  match value with | .ok value => pure value | .error error => throw (failure error)

/-- Run one source algorithm and retain the updated universe in the same state. -/
def perform (access : Access S) (action : TypeArena.WorldM α) : EStateM StepError S α := do
  let state ← get
  let (result,world) ← lift (RuntimeArrayTypes.perform (access.get state) action)
  set (access.set state world)
  pure result

/-- Commit the single type/instance world, including all nested type effects. -/
def performCompiler (access : Access S) (action : RuntimeArrayTypes.CompilerM α) :
    EStateM StepError S α := do
  let state ← get
  let (result,world) ← lift (RuntimeArrayTypes.performCompiler (access.get state) action)
  set (access.set state world)
  pure result

def compilerSnapshot (access : Access S) : EStateM StepError S RuntimeArrayTypes.World :=
  return access.get (← get)

def snapshot (access : Access S) : EStateM StepError S TypeArena.World :=
  return (access.get (← get)).arena

def arrayLayout (access : Access S) (element : MIR.TyId) (count : UInt64) :
    EStateM StepError S LocalLayout := do
  let state ← get
  let (layout,world) ← lift (RuntimeArrayTypes.internElement (access.get state) element count)
  set (access.set state world)
  pure layout

def osStringsHooks (access : Access S) (base : OsStrings.Hooks P S Os Kind) :
    OsStrings.Hooks P S Os Kind :=
  {base with arrayLayout := fun wide count => do
    let state ← get
    let (layout,world) ← lift (RuntimeArrayTypes.osStringArray (access.get state) wide count)
    set (access.set state world)
    pure layout}

def layoutOf (access : Access S) (id : MIR.TyId) : EStateM StepError S LocalLayout := do
  perform access (RuntimeMetadata.layoutInWorld (access.get (← get)).metadata id)

def fieldLayout (access : Access S) (parent : LocalLayout) (index : Nat) : EStateM StepError S LocalLayout := do
  perform access (RuntimeMetadata.fieldLayoutForInWorld (access.get (← get)).metadata parent index)

/-- Classification reads syntax from the same world; non-array families are
handled by the general compiler facts hooks rather than an auxiliary table. -/
def validityHooks (access : Access S) (base : ValidityVisitor.Hooks P S C E Fn Abi Pad) :
    ValidityVisitor.Hooks P S C E Fn Abi Pad :=
  {base with classify := fun choice ty => do
    let world := access.get (← get)
    match RuntimeArrayTypes.arrayInfo world ty with
    | .ok (_,element) => pure (.sequence element)
    | .error _ => base.classify choice ty}
end Miri.Input.RuntimeArrayQueries
