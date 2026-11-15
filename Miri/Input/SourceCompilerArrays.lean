import Miri.Input.SourceCompilerTypes
import Miri.Input.RuntimeArrayTypes

/-! Runtime array constructors share the source compiler's canonical type pool.
The element's identity is supplied explicitly; equal layout never identifies a
Rust type. Geometry follows rustc_abi::layout_of_array_like, also independently
implemented by RuntimeArrayTypes.calculate. -/
namespace Miri.Input.SourceCompilerArrays
open Miri.ABI SourceCompilerWorld

def intern (initial : World) (target : RuntimeTargetDataLayout) (element : TypeId) (count : UInt64) :
    Except String (World × TyAndLayout TypeId) := do
  let runtime : RuntimeMetadata := ⟨initial.canonical,target⟩
  let child ← (runtime.lookup element).mapError toString
  let childNode ← (runtime.node element).mapError toString
  let some childRow := initial.canonical.layouts[childNode.layoutId]?
    | throw "canonical runtime array element layout row absent"
  unless child.layout.isSized do throw "canonical runtime array requires a sized element"
  unless count.toNat < 2^(target.pointerOffset.bytes.toNat*8) do
    throw "canonical runtime array count exceeds target usize"
  let computed ← (RuntimeArrayTypes.calculate target child.layout count).mapError reprStr
  let usize := initial.canonical.queries.primitives.usize
  let usizeNode ← (runtime.node usize).mapError toString
  unless usizeNode.shapeMetadata.unsignedKind == some (.known .usize) do
    throw "canonical runtime array usize source identity unavailable"
  let usizeLayout ← (runtime.lookup usize).mapError toString
  unless usizeLayout.layout.size == target.pointerOffset do throw "canonical runtime array usize width mismatch"
  let (world,length) ← internScalarConstant initial usize count.toNat target.pointerOffset.bytes.toNat
  let row : Layout := {
    maxReprAlignBytes := none,reprC := child.layout.reprC,
    uninhabited := child.layout.uninhabited && count != 0,
    largestNiche := if count == 0 then none else childRow.largestNiche,
    randomizationSeed := computed.randomizationSeed.toNat,
    kind := .layout,sizeBytes := some computed.size.bytes.toNat,
    abiAlignBytes := some (← computed.align.abi.bytes.mapError toString).toNat,
    unadjustedAbiAlignBytes := some (← computed.unadjustedAbiAlign.bytes.mapError toString).toNat,
    fieldOffsetsBytes := .arrayFormula child.layout.size.bytes.toNat count.toNat,
    fields := some ⟨.array,count.toNat,none,some child.layout.size.bytes.toNat,#[],#[]⟩,
    variantsLayout := some ⟨.single,some 0,none,none,none,#[]⟩,
    backendRepresentation := some ⟨.memory,some true,none,none,none,none,none,none,none⟩,
    variantsKind := some .single,backendReprKind := some .memory,variants := none,backendRepr := none }
  let (world,id) ← internType world (.array element length ⟨count.toNat,true⟩) row "runtime array"
  return (world,⟨id,computed⟩)
/-- A cache can only be attached when every previously issued ID has the same
canonical array meaning and layout. This never repairs an ID collision by alias.
Normal bootstrap supplies an empty cache; conflicting legacy caches fail closed. -/
def view (arrays : RuntimeArrayTypes.World) (world : World) :
    Except String RuntimeArrayTypes.World := do
  unless arrays.metadata.source.runtimeTargetDataLayout == world.canonical.runtimeTargetDataLayout &&
      arrays.metadata.source.producer.targetTriple == world.canonical.producer.targetTriple do
    throw "runtime array and canonical target evidence differ"
  let runtime : RuntimeMetadata := ⟨world.canonical,arrays.metadata.target⟩
  let fresh ← (RuntimeArrayTypes.create runtime).mapError reprStr
  unless arrays.byteLayout == fresh.byteLayout && arrays.wideLayout == fresh.wideLayout do
    throw "runtime array primitive identities differ from canonical World"
  for entry in arrays.entries do
    let some (_,id) := fresh.aliases.find? (·.1 == entry.key)
      | throw "runtime array identity was not installed in the canonical World"
    unless id == entry.value.ty do throw "runtime array and source type IDs conflict"
    let actual ← (RuntimeArrayTypes.lookup fresh id).mapError reprStr
    unless actual == entry.value do throw "runtime array and canonical layout conflict"
  return {fresh with entries := arrays.entries, canonicalOwned := true}

/-- Both persistent states change atomically, with one canonical ID allocator.
The runtime array world is a validated view/cache, never another ID source. -/
def internCached (arrays : RuntimeArrayTypes.World) (world : World) (element : TypeId) (count : UInt64) :
    Except String (TyAndLayout TypeId × RuntimeArrayTypes.World × World) := do
  let before ← view arrays world
  let (world,expected) ← intern world before.metadata.target element count
  let after ← view before world
  let (actual,after) ← (RuntimeArrayTypes.internElement after element count).mapError reprStr
  unless actual == expected do throw "canonical array constructor/view contradiction"
  return (actual,after,world)
end Miri.Input.SourceCompilerArrays
