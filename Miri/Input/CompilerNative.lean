import Miri.Input.EvalNativeConstruction
import Miri.Input.CompilerProviders
import Miri.Input.WorldNormalization
import Miri.Interpreter.NativeAbi

/-! Native libffi compiler queries from native_lib/mod.rs:367–435. Shape is
actual compiler ADT/tuple evidence, not diagnostic spelling or ABI size. -/
namespace Miri.Input.CompilerNative
open Lean Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
private def lift (value : Except String A) : EStateM StepError S A :=
  match value with | .ok value => pure value | .error reason => throw (.callback s!"native compiler query unavailable: {reason}")

private def shape (p : CompilerProviders.Prepared) (layout : LocalLayout) : Except String Native.TypeShape := do
  let source ← p.runtime.node layout.ty |>.mapError toString
  match source.shape with
  | .adt data =>
    let reprC := data.representation.c
    let (isEnum,isStruct) := match data.kind with
      | .enumKind => (true,false) | .structKind => (false,true) | .unionKind => (false,false)
    if let .Scalar .. := layout.layout.backendRepr then return .adt isEnum isStruct reprC #[]
    if !isStruct || !reprC then return .adt isEnum isStruct reprC #[]
    let info ← CompilerFacts.adtInfo p.lifecycle.calls.symbols.facts.context layout.ty
    unless info.variants.size == 1 do throw "native struct lacks one non-enum variant"
    let some fields := info.variants[0]? | throw "native struct fields unavailable"
    pure (.adt isEnum isStruct reprC (fields.map (·.ty)))
  | .tuple elements => pure (if elements.isEmpty then .emptyTuple else .other)
  | _ => pure .other

private def liftWorld (value : Except String A) : TypeArena.WorldM A :=
  match value with | .ok result => pure result | .error reason => throw reason

private def perform (arrays : RuntimeArrayQueries.Access S) (action : TypeArena.WorldM A) :
    EStateM StepError S A := do
  let state ← get
  let (result,world) ← lift ((RuntimeArrayTypes.perform (arrays.get state) action).mapError reprStr)
  set (arrays.set state world)
  pure result

private def shapeInWorld (p : CompilerProviders.Prepared)
    (aliases : Except String AliasRuntime.Context) (layout : LocalLayout) :
    TypeArena.WorldM Native.TypeShape := do
  let world ← get
  match ← liftWorld (world.lookupType layout.ty) with
  | .material _ => liftWorld (shape p layout)
  | .constructed constructor =>
    let actual ← RuntimeMetadata.layoutInWorld p.runtime layout.ty
    unless actual == layout do throw "native runtime constructor layout disagrees with canonical type"
    match constructor with
    | .tuple elements => pure (if elements.isEmpty then .emptyTuple else .other)
    | .adt definition arguments =>
      let reference ← liftWorld (world.definitionRef definition)
      let some source := world.definitions[reference]? | throw "native ADT source definition absent"
      let some declaration := source.adtDeclaration | throw "native ADT source declaration absent"
      let reprC := declaration.representation.c
      let isEnum := declaration.kind == .enumKind
      let isStruct := declaration.kind == .structKind
      if let .Scalar .. := layout.layout.backendRepr then return .adt isEnum isStruct reprC #[]
      if !isStruct || !reprC then return .adt isEnum isStruct reprC #[]
      let some template := source.genericTemplate | throw "native struct source field expressions absent"
      let aliases ← liftWorld aliases
      let fields ← (template.fields.filter (·.variantIndex == 0)).mapM fun field => do
        let term ← liftWorld (GenericInstantiationWorld.instantiateFieldTerm (← get) 16384
          definition arguments 0 field.fieldIndex)
        WorldNormalization.resolveNormalizedTerm aliases 16384 16384 term
      pure (.adt isEnum isStruct reprC fields)
    | _ => pure .other

/-- Native queries inspect the current material/constructed universe. Field
normalization and layout constructors retain newly created identities there. -/
def abiQueries (p : CompilerProviders.Prepared)
    (arrays : RuntimeArrayQueries.Access S) : NativeAbi.Queries S C :=
  let aliases := AliasRuntime.Context.ofDocument p.program.input
  { typeShape := fun _ layout => perform arrays (shapeInWorld p aliases layout)
    layoutOf := fun _ ty => return .ok (← perform arrays (RuntimeMetadata.layoutInWorld p.runtime ty)) }
/-- The same genuine compiler queries work on full-state native calls and
machine-only closure construction, without introducing an artificial frame. -/
def make (p : CompilerProviders.Prepared)
    (arrays : RuntimeArrayQueries.Access (NativeMachine.State MiriMemoryKind U)) :
    EvalNativeConstruction.Compiler U C where
  typeShape := (abiQueries p arrays).typeShape
  layoutOf := (abiQueries p arrays).layoutOf
end Miri.Input.CompilerNative
