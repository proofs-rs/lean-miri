import Miri.Input.RuntimeArrayQueries
import Miri.Input.CompilerFacts

/-! Source fast paths in rustc_middle/ty/util.rs::is_trivially_freeze and
is_trivially_unpin (1191–1267). A true structural fast path justifies Freeze,
Unpin and UnsafeUnpin; false does not justify a negative trait result. Nontrivial
runtime arrays still require genuine compiler trait resolution evidence. -/
namespace Miri.Input.RuntimeArrayFacts
open Lean Miri.ABI Miri.Interpreter
private def trivial (world : RuntimeArrayTypes.World) (ty : MIR.TyId) : Nat → Except String Bool
  | 0 => throw "structural trivial-trait query budget exhausted"
  | fuel+1 => do
    if let some entry := world.entries.find? (·.value.ty == ty) then
      let child := match entry.key.element with
        | .u8 => world.byteLayout.ty | .u16 => world.wideLayout.ty | .compiler id => id
      return ← trivial world child fuel
    let node ← world.metadata.node ty |>.mapError toString
    unless node.shapeStatus == .supported do throw "structural trait query requires compiler type shape"
    match node.shapeKind with
    | .int | .uint | .float | .bool | .char | .str | .never | .reference | .rawPointer
    | .functionDefinition | .functionPointer | .errorType => pure true
    | .tuple =>
      let some id := node.relations.elements | throw "tuple elements absent"
      let elements ← world.metadata.source.typeRelationTables.typeLists.lookup id |>.mapError
        (fun id => s!"invalid tuple element list {id}")
      for child in elements do
        unless ← trivial world child fuel do return false
      pure true
    | .array | .slice | .patternType =>
      let some child := if node.shapeKind == .patternType then node.relations.base else node.relations.element
        | throw "structural trait child type absent"
      trivial world child fuel
    | _ => pure false

def boolean (world : RuntimeArrayTypes.World)
    (ty : MIR.TyId) (key : String) : Except String Bool := do
  unless key == "is_freeze" || key == "is_unpin" || key == "is_unsafe_unpin" do
    throw "unsupported structural array trait query"
  if !world.entries.any (·.value.ty == ty) then return ← CompilerFacts.booleanRuntime world.metadata ty key
  if ← trivial world ty (world.entries.size + world.metadata.source.types.size + 1) then return true
  -- Compiler aliases retain actual queried traits. A newly constructed array
  -- has no such query; recurse only through a source-supported fast path above.
  if world.metadata.source.types.any (·.id == ty) then return ← CompilerFacts.booleanRuntime world.metadata ty key
  throw "nontrivial runtime array trait requires exact compiler resolution evidence"
private def lift (value : Except String A) : EStateM StepError S A :=
  match value with | .ok value => pure value | .error error => throw (.unsupported error)

/-- rustc_middle/ty/inhabitedness/mod.rs:312–314: an array is opsem
inhabited exactly when its evaluated length is zero or its element is inhabited.
Compiler-owned elements retain their actual normalized query result. -/
def opsemInhabited (world : RuntimeArrayTypes.World)
    (ty : MIR.TyId) : Nat → Except String Bool
  | 0 => throw "runtime array inhabitedness query budget exhausted"
  | fuel+1 => do
    if let some entry := world.entries.find? (·.value.ty == ty) then
      if entry.key.count == 0 then return true
      let child := match entry.key.element with
        | .u8 => world.byteLayout.ty | .u16 => world.wideLayout.ty | .compiler id => id
      opsemInhabited world child fuel
    else CompilerFacts.booleanRuntime world.metadata ty "opsem_inhabited"

def retagHooks (access : RuntimeArrayQueries.Access (MachineHooks.State K U))
    (base : TypedRetag.Hooks K U) : TypedRetag.Hooks K U :=
  let constructed := fun ty => do return (access.get (← get)).entries.any (·.value.ty == ty)
  let traitQuery := fun ty key => do lift (boolean (access.get (← get)) ty key)
  {base with
    typeShape := fun ty => do
      if ← constructed ty then return ⟨false,false,false,false⟩
      base.typeShape ty
    isUnpin := fun ty => traitQuery ty "is_unpin"
    isUnsafeUnpin := fun ty => traitQuery ty "is_unsafe_unpin"
    typeIsFreeze := fun ty => traitQuery ty "is_freeze"
    freeze := {base.freeze with
      isUnsafeCell := fun ty => do if ← constructed ty then pure false else base.freeze.isUnsafeCell ty
      typeIsFreeze := fun ty => traitQuery ty "is_freeze"
      isDynamic := fun ty => do if ← constructed ty then pure false else base.freeze.isDynamic ty
      isBox := fun ty => do if ← constructed ty then pure false else base.freeze.isBox ty
      isTooGeneric := fun ty => do if ← constructed ty then pure false else base.freeze.isTooGeneric ty}}
end Miri.Input.RuntimeArrayFacts
