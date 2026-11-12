import Miri.Input.RuntimeArrayQueries
import Miri.Input.CompilerWorldFacts

/-! Runtime retag/validity facts use the same execution-owned type universe as
all other constructors. There is no array-specific fact table or second arena. -/
namespace Miri.Input.RuntimeArrayFacts
open Miri.ABI Miri.Interpreter

def boolean (context : CompilerFacts.Context) (ty : MIR.TyId) (key : String) :
    TypeArena.WorldM Bool := CompilerFacts.booleanInWorld context ty key

def opsemInhabited (context : CompilerFacts.Context) (ty : MIR.TyId) :
    TypeArena.WorldM Bool := CompilerFacts.booleanInWorld context ty "opsem_inhabited"

def retagHooks (access : RuntimeArrayQueries.Access (MachineHooks.State K U))
    (context : CompilerFacts.Context) (base : TypedRetag.Hooks K U) : TypedRetag.Hooks K U :=
  let run := fun {A} (action : TypeArena.WorldM A) => RuntimeArrayQueries.perform access action
  let traitQuery := fun ty key => run (CompilerFacts.booleanInWorld context ty key)
  {base with
    typeShape := fun ty => run (CompilerFacts.retagTypeShapeInWorld context ty)
    builtinDeref := fun ty => run (CompilerFacts.requiredTypeInWorld context ty "builtin_deref_explicit")
    referencePointee := fun ty => run (CompilerFacts.referencePointeeInWorld context ty)
    isUnpin := fun ty => traitQuery ty "is_unpin"
    isUnsafeUnpin := fun ty => traitQuery ty "is_unsafe_unpin"
    typeIsFreeze := fun ty => traitQuery ty "is_freeze"
    freeze := {base.freeze with
      isUnsafeCell := fun ty => traitQuery ty "is_unsafe_cell"
      typeIsFreeze := fun ty => traitQuery ty "is_freeze"
      isDynamic := fun ty => traitQuery ty "is_dynamic"
      isBox := fun ty => traitQuery ty "is_box"
      isTooGeneric := fun ty => traitQuery ty "is_too_generic"}}
end Miri.Input.RuntimeArrayFacts
