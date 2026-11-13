import Miri.Input.WorldVTableInstance
import Miri.Input.RuntimeArrayQueries
import Miri.Input.WorldDynamicData

/-! Source-owned virtual-call consistency leaves. Runtime receiver selection,
vtable memory and recursive callee body/ABI checks remain their own providers. -/
namespace Miri.Input.WorldVirtualHooks
open Miri.Interpreter

/-- Both call assembly paths install this wrapper last. Limits bound source
normalization and selection work; exhaustion never falls back to answer rows. -/
def hooks (types : RuntimeArrayQueries.Access S) (base : VirtualCalls.CompilerHooks S C)
    (work : Nat := 100000) (fuel : Nat := 2048) : VirtualCalls.CompilerHooks S C :=
  {base with
    dynamicData := fun owner => RuntimeArrayQueries.performCompiler types
      (WorldDynamicData.runtimeData fuel owner)
    parentTrait := fun method => RuntimeArrayQueries.performCompiler types
      (WorldVTableInstance.parentTrait method)
    rebaseVirtualArgs := fun args parent concrete => RuntimeArrayQueries.performCompiler types
      (WorldVTableInstance.rebaseVirtualArgs args parent concrete)
    expectResolveForVTable := fun _ method args => RuntimeArrayQueries.performCompiler types
      (WorldVTableInstance.resolveMethod work fuel method args)}

/-- Install last, after machine reservation adapters. New predicate handles
cannot enter unported comparison, normalization, entry or allocation catalogs. -/
def vtableHooks (types : RuntimeArrayQueries.Access S) (base : VTableHooks P S C F ABI) :
    VTableHooks P S C F ABI :=
  let check := fun values => RuntimeArrayQueries.performCompiler types
    (WorldDynamicData.requireMaterialPredicates values)
  let checkType := fun id => RuntimeArrayQueries.performCompiler types
    (WorldDynamicData.requireMaterialType id)
  {base with
    globalVTable := fun choice id => do
      let result ← base.globalVTable choice id
      if let some (_,predicates) := result then check predicates
      pure result
    predicates := fun choice values => do check values; base.predicates choice values
    normalizePredicate := fun choice predicate => do
      check #[predicate.id]
      base.normalizePredicate choice predicate
    eraseAndAnonymize := fun choice ty values => do
      checkType ty
      check values
      let (ty,values) ← base.eraseAndAnonymize choice ty values
      checkType ty
      check values
      pure (ty,values)
    ensureMonomorphicType := fun choice ty => do checkType ty; base.ensureMonomorphicType choice ty
    ensureMonomorphicDyn := fun choice values => do check values; base.ensureMonomorphicDyn choice values
    reserveVTable := fun choice ty values salt => do check values; base.reserveVTable choice ty values salt
    entries := fun choice principal ty => do
      checkType ty
      RuntimeArrayQueries.performCompiler types (WorldDynamicData.requireMaterialPrincipal principal)
      let entries ← base.entries choice principal ty
      for entry in entries do
        if let .traitVPtr principal := entry then
          RuntimeArrayQueries.performCompiler types (WorldDynamicData.requireMaterialPrincipal (some principal))
      pure entries}
end Miri.Input.WorldVirtualHooks
