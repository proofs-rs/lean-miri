import Miri.Input.EvalNativeConstruction
import Miri.Input.CompilerProviders
import Miri.Input.WorldNormalization
import Miri.Input.RuntimeEffectfulLayout
import Miri.Interpreter.NativeAbi

/-! Native libffi compiler queries from native_lib/mod.rs:367–435. Shape is
actual compiler ADT/tuple evidence, not diagnostic spelling or ABI size. -/
namespace Miri.Input.CompilerNative
open Lean Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
private def lift (value : Except String A) : EStateM StepError S A :=
  match value with | .ok value => pure value | .error reason => throw (.callback s!"native compiler query unavailable: {reason}")

private def sourceShape {m : Type → Type} [Monad m] [MonadStateOf TypeArena.World m]
    [MonadExceptOf String m] [MonadLiftT (Except String) m] [MonadLiftT TypeArena.WorldM m]
    (normalization : RuntimeMetadata.LayoutNormalization m) (p : CompilerProviders.Prepared)
    (layout : LocalLayout) : m Native.TypeShape := do
  let world ← get
  let constructor ← match ← world.lookupType layout.ty with
    | .constructed key => pure key
    | .material node => do
      let some key ← world.materialKey node | throw "native source constructor unavailable"
      pure key
  match constructor with
  | .tuple elements => pure (if elements.isEmpty then .emptyTuple else .other)
  | .adt definition arguments =>
    let declaration ← RuntimeMetadata.adtDeclarationInWorld p.runtime layout.ty
    let reprC := declaration.representation.c
    let isEnum := declaration.kind == .enumKind
    let isStruct := declaration.kind == .structKind
    if let .Scalar .. := layout.layout.backendRepr then return .adt isEnum isStruct reprC #[]
    if !isStruct || !reprC then return .adt isEnum isStruct reprC #[]
    let fields ← (declaration.fields.filter (·.variantIndex == 0)).mapM fun field => do
      let term ← GenericInstantiationWorld.instantiateFieldTerm (← get) 16384
        definition arguments 0 field.fieldIndex
      normalization.resolve 16384 16384 term
    pure (.adt isEnum isStruct reprC fields)
  | _ => pure .other

/-- Material and constructed native fields share raw declaration templates.
Only a reached field normalization may invoke the owning effectful provider. -/
def abiQueries (p : CompilerProviders.Prepared) (arrays : RuntimeArrayQueries.Access S)
    (provider : RuntimeEffectfulLayout.Provider S := RuntimeEffectfulLayout.unavailable) : NativeAbi.Queries S C :=
  { typeShape := fun _ layout => RuntimeEffectfulLayout.perform arrays provider
      CompilerTypingEnv.fullyMonomorphized none p.runtime
      (fun {_} _ _ _ _ _ normalization => sourceShape normalization p layout)
      (fun message => .callback s!"native compiler query unavailable: {message}")
    layoutOf := fun _ ty => return .ok (← RuntimeEffectfulLayout.perform arrays provider
      CompilerTypingEnv.fullyMonomorphized none p.runtime
      (fun {_} _ _ _ _ _ normalization => RuntimeMetadata.layoutEffectfulInWorld normalization p.runtime ty)
      (fun message => .callback s!"native compiler query unavailable: {message}")) }

def make (p : CompilerProviders.Prepared)
    (arrays : RuntimeArrayQueries.Access (NativeMachine.State MiriMemoryKind U))
    (provider : RuntimeEffectfulLayout.Provider (NativeMachine.State MiriMemoryKind U) := RuntimeEffectfulLayout.unavailable) :
    EvalNativeConstruction.Compiler U C where
  typeShape := (abiQueries p arrays provider).typeShape
  layoutOf := (abiQueries p arrays provider).layoutOf
end Miri.Input.CompilerNative
