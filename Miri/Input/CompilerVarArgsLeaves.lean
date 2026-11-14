import Miri.Input.CompilerProviders
import Miri.Input.CompilerWorldCompatibility
import Miri.Interpreter.CompilerExecutionProviders
import Miri.Interpreter.IntrinsicSymbolsMachine

/-! Exact C-varargs compiler leaves from intrinsics.rs:877–931,1416–1433;
identical_c_types delegates to the source call.rs structural compatibility port.
Target-specific VaList fields come from instantiated compiler ADT declarations.
-/
namespace Miri.Input.CompilerVarArgsLeaves
open Miri.ABI Miri.Interpreter Miri.Memory
def make (p : CompilerProviders.Prepared)
    (types : RuntimeArrayQueries.Access (MachineHooks.State K U)) (compatibilityBudget : Nat)
    (typeConstants : RuntimeEffectfulLayout.Provider (MachineHooks.State K U) := RuntimeEffectfulLayout.unavailable) :
    IntrinsicSymbolsMachine.VarArgsLeaves K U C :=
  let context := p.lifecycle.calls.symbols.facts.context
  let run := fun {A} (action : TypeArena.WorldM A) => RuntimeArrayQueries.perform types action
  { layoutOf := fun _ ty => RuntimeEffectfulLayout.layout types typeConstants CompilerTypingEnv.fullyMonomorphized none context.runtime ty
    typeInfo := fun _ ty => do
      match ← run (CompilerWorldCompatibility.kind ty) with
      | .integer kind =>
        return if kind.signed then .signedInteger kind else .unsignedInteger kind
      | .rawPointer child | .reference child => return .pointer child
      | _ => pure .other
    identicalCTypes := fun _ left right =>
      LayoutCompat.identicalCTypes (CompilerWorldCompatibility.queries context types typeConstants) compatibilityBudget left right
    isCVoid := fun _ ty => run (CompilerFacts.booleanInWorld context ty "is_c_void")
    vaListFields := fun _ ty => do
      let adt ← run (CompilerWorldCompatibility.adt context.runtime ty)
      if adt.kind == .Enum then throw (.invalidProgram "VaListImpl must be a non-enum ADT")
      unless adt.variants.size == 1 do throw (.invalidProgram "VaListImpl has invalid non-enum variant declarations")
      let some fields := adt.variants[0]? | throw (.unsupported "VaListImpl compiler fields unavailable")
      pure (fields.map (·.ty))
    isRawPointer := fun _ ty => do
      pure ((← run (RuntimeMetadata.shapeKindInWorld context.runtime ty)) == .rawPointer) }
end Miri.Input.CompilerVarArgsLeaves
