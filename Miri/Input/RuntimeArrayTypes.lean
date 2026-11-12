import Miri.Input.RuntimeMetadata
import Miri.Input.GenericInstantiationWorld

/-! One execution-owned type/constant universe. Runtime arrays use the same
constructor interner as generic MIR, ADTs and function items. Layout results are
computed on demand and are never retained as a second canonical type table. -/
namespace Miri.Input.RuntimeArrayTypes
open Lean Miri.ABI TypeArena
inductive Element where
  | u8 | u16 | compiler (id : TypeId)
  deriving DecidableEq, Repr
structure Key where
  element : Element
  count : UInt64
  deriving DecidableEq, Repr
structure World where
  metadata : RuntimeMetadata
  arena : TypeArena.World
inductive Error where
  | metadata (reason : String)
  | targetUsizeOverflow (count : UInt64)
  | sizeOverflow
  | missingRuntimeType (id : TypeId)
  | fieldOutOfBounds (index count : Nat)
  deriving DecidableEq, Repr
private def lift (result : Except String α) : Except Error α := result.mapError Error.metadata

def calculate (target : RuntimeTargetDataLayout) (element : LayoutData)
    (count : UInt64) : Except Error LayoutData :=
  (PrimitiveLayout.arrayLike target element count).mapError (fun _ => .sizeOverflow)

def create (runtime : RuntimeMetadata) : Except Error World := do
  let some checked := runtime.checkedMaterial
    | throw (.metadata "checked source material prefix is absent")
  pure {metadata := runtime, arena := TypeArena.World.ofCheckedMaterial checked}

/-- Every stateful source query commits its returned constructor universe. -/
def perform (world : World) (action : TypeArena.WorldM α) : Except Error (α × World) := do
  let (result,arena) ← lift (action.run world.arena)
  pure (result,{world with arena})

private def elementId (world : World) : Element → TypeId
  | .u8 => world.metadata.source.queries.primitives.u8
  | .u16 => world.metadata.source.queries.primitives.u16
  | .compiler id => id
private def elementOfId (world : World) (id : TypeId) : Element :=
  if id == world.metadata.source.queries.primitives.u8 then .u8
  else if id == world.metadata.source.queries.primitives.u16 then .u16 else .compiler id

def lookup (world : World) (id : TypeId) : Except Error (TyAndLayout TypeId × World) :=
  perform world (RuntimeMetadata.layoutInWorld world.metadata id)

def intern (world : World) (element : Element) (count : UInt64) :
    Except Error (TyAndLayout TypeId × World) := do
  let bytes := world.arena.pointerBytes
  unless count.toNat < 2^(8 * bytes) do throw (.targetUsizeOverflow count)
  let elementId := elementId world element
  if let some expected := match element with
      | .u8 => some MIR.IntegerKind.u8 | .u16 => some .u16 | .compiler _ => none then
    let actual ← match ← lift (world.arena.lookupType elementId) with
      | .material source => pure source.shapeMetadata.unsignedKind
      | .constructed (.integer false kind) => pure (some (.known kind))
      | _ => pure none
    unless actual == some (.known expected) do
      throw (.metadata "runtime OS array primitive is not its exact source unsigned type")
  perform world do
    let elementLayout ← RuntimeMetadata.layoutInWorld world.metadata elementId
    unless elementLayout.layout.isSized do throw "array element requires a sized type"
    let usize := world.metadata.source.queries.primitives.usize
    let length ← TypeArena.World.internConstant (.Value usize ⟨#[.Leaf count.toNat bytes],0⟩)
    let id ← TypeArena.World.internType (.array elementId length)
    RuntimeMetadata.layoutInWorld world.metadata id

def internElement (world : World) (element : TypeId) (count : UInt64) :
    Except Error (TyAndLayout TypeId × World) := intern world (.compiler element) count

def osStringArray (world : World) (wide : Bool) (count : UInt64) :
    Except Error (TyAndLayout TypeId × World) := intern world (if wide then .u16 else .u8) count

/-- Read constructor syntax only. This function neither computes layouts nor
creates a temporary universe whose IDs could escape. -/
def arrayInfo (world : World) (id : TypeId) : Except Error (Key × TypeId) := do
  let (element,length) ← match ← lift (world.arena.lookupType id) with
    | .material source => match source.shape with
      | .array element length _ => pure (element,length)
      | _ => throw (.missingRuntimeType id)
    | .constructed (.array element length) => pure (element,length)
    | _ => throw (.missingRuntimeType id)
  let .Value ty tree ← lift (world.arena.lookupConstant length)
    | throw (.metadata "array length requires raw canonical constant value material")
  let usize ← match ← lift (world.arena.lookupType ty) with
    | .material source => pure (source.shapeMetadata.unsignedKind == some (.known .usize))
    | .constructed (.integer false .usize) => pure true
    | _ => pure false
  let some (.Leaf bits bytes) := tree.nodes[tree.root]?
    | throw (.metadata "array length requires a scalar raw constant")
  unless usize && bytes == world.arena.pointerBytes && bits < 2^(8 * bytes) && bits < 2^64 do
    throw (.metadata "array length is not a canonical target usize")
  pure (⟨elementOfId world element,UInt64.ofNat bits⟩,element)

def fieldLayout (world : World) (parent index : Nat) : Except Error (TyAndLayout TypeId × World) :=
  perform world (RuntimeMetadata.fieldLayoutInWorld world.metadata parent index)
end Miri.Input.RuntimeArrayTypes
