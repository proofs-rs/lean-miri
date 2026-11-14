import Miri.Input.CompilerInitialAllocationWorld
import Miri.Input.RuntimeMetadata

/-! Bounded source-derived static metadata. Layout uses the actual World
algorithm. Freeze is proved structurally only for primitive scalars and arrays;
all other source shapes remain unavailable, never assumed immutable. -/
namespace Miri.Input.CompilerInitialAllocation.StaticMaterial
open Miri.Memory Miri.ABI
set_option autoImplicit false
private def freeze (world : TypeArena.World) : Nat → TypeId → Except String Unit
  | 0, _ => .error "initial static source Freeze depth exhausted"
  | fuel+1, id => do
    let shape ← match ← world.lookupType id with
      | .constructed value => pure (some value)
      | .material node => world.materialKey node
    match shape with
    | some .bool | some .char | some (.integer ..) | some (.float ..) | some .never => pure ()
    | some (.array element _) => freeze world fuel element
    | _ => throw "initial static Freeze outside primitive/array source domain"

def prepare (runtime : RuntimeMetadata) (snapshot : Snapshot) (original : TypeArena.World) :
    Except String (SymbolicMaterial × TypeArena.World) := do
  let mut world := original
  let mut entries : Array (GenericSubstitution.DefinitionIdentity × GlobalAllocation) := #[]
  for binding in snapshot.globals do
    if let .static definition := binding.key then
      let some source := binding.staticSource | throw "static source descriptor absent"
      unless source.isStatic && !source.nested do throw "nonstatic/nested initial static source unsupported"
      let some type := source.type | throw "initial static source type unavailable"
      freeze world 1024 type
      let definitionRef ← world.definitionRef definition
      let (layout,nextWorld) ← (RuntimeMetadata.layoutInWorld runtime type).run world
      world := nextWorld
      unless layout.layout.isSized do throw "initial static source is unsized"
      let mut align := layout.layout.align.abi
      if let some explicit := source.explicitAlignBytes then
        let declared ← (Align.fromBytes explicit).mapError toString
        if align.pow2 < declared.pow2 then align := declared
      let mutability := if source.mutability == .mutable then Mutability.Mut else .Not
      let placeholder : AllocId := ⟨1,by decide⟩
      let entry : GlobalAllocation := {
        allocId := placeholder,kind := .static,size := layout.layout.size,align,mutability,
        payload := some (.static definitionRef source.isStatic source.threadLocal source.foreignItem) }
      entries := entries.push (definition,entry)
  let symbolic : SymbolicMaterial := {
    prepare := fun _ => .error "initial function/vtable/typeid runtime material unavailable"
    prepareStatic := fun definition _ => match entries.find? (fun row => row.1 == definition) with
      | some row => .ok row.2 | none => .error "static metadata absent from source-derived candidate" }
  pure (symbolic,world)
end Miri.Input.CompilerInitialAllocation.StaticMaterial
