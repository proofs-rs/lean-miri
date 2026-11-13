import Miri.Input.WorldVTableInstance
import Miri.Input.RuntimeArrayQueries

/-! Source-owned virtual-call consistency leaves. Runtime receiver selection,
vtable memory and recursive callee body/ABI checks remain their own providers. -/
namespace Miri.Input.WorldVirtualHooks
open Miri.Interpreter

/-- Both call assembly paths install this wrapper last. Limits bound source
normalization and selection work; exhaustion never falls back to answer rows. -/
def hooks (types : RuntimeArrayQueries.Access S) (base : VirtualCalls.CompilerHooks S C)
    (work : Nat := 100000) (fuel : Nat := 2048) : VirtualCalls.CompilerHooks S C :=
  {base with
    parentTrait := fun method => RuntimeArrayQueries.performCompiler types
      (WorldVTableInstance.parentTrait method)
    rebaseVirtualArgs := fun args parent concrete => RuntimeArrayQueries.performCompiler types
      (WorldVTableInstance.rebaseVirtualArgs args parent concrete)
    expectResolveForVTable := fun _ method args => RuntimeArrayQueries.performCompiler types
      (WorldVTableInstance.resolveMethod work fuel method args)}
end Miri.Input.WorldVirtualHooks
