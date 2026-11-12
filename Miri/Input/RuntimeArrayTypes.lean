import Miri.Input.RuntimeMetadata
import Miri.Input.GenericInstantiationWorld
import Miri.Input.InstanceArena
import Miri.Input.BodyArena

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
  instances : InstanceArena.Store
  bodies : BodyArena.Store
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
  let arena := TypeArena.World.ofCheckedMaterial checked
  let instances ← lift (InstanceArena.Store.ofSource arena runtime.source.instances)
  pure {metadata := runtime, arena, instances, bodies := BodyArena.Store.ofSource runtime.source.bodies}

/-- Every stateful source query commits its returned constructor universe. -/
def perform (world : World) (action : TypeArena.WorldM α) : Except Error (α × World) := do
  let (result,arena) ← lift (action.run world.arena)
  pure (result,{world with arena})

/-- Type and instance syntax share one execution-owned compiler state. -/
abbrev CompilerM := StateT World (Except String)

def liftType (action : TypeArena.WorldM α) : CompilerM α := do
  let world ← get
  let (value,arena) ← match action.run world.arena with
    | .ok value => pure value | .error error => throw error
  set {world with arena}
  pure value

def internInstance (kind : Miri.Interpreter.CallInstanceKind)
    (arguments : Array MIR.GenericArg) : CompilerM InstanceId := do
  let world ← get
  let result := do
    let key ← InstanceArena.Key.ofSource world.arena kind arguments
    world.instances.intern world.arena key
  let (id,instances) ← match result with
    | .ok value => pure value | .error error => throw error
  set {world with instances}
  pure id

def internBody (templateId instanceId : Nat) (promoted : Option Nat) : CompilerM BodyId := do
  let world ← get
  let result := do
    let key ← BodyArena.Key.create world.arena world.instances
      world.metadata.source.mirTemplates templateId instanceId promoted
    world.bodies.intern world.arena world.instances world.metadata.source.mirTemplates world.metadata.source.bodies key
  let (id,bodies) ← match result with
    | .ok value => pure value | .error error => throw error
  set {world with bodies}
  pure id

def performCompiler (world : World) (action : CompilerM α) : Except Error (α × World) :=
  lift (action.run world)

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
