import Miri.Input.WorldSourceAutoTraits

namespace Miri.Input.WorldBoxAbi
open Miri.ABI GenericSubstitution
private def liftPure (result : Except String α) : RuntimeArrayTypes.CompilerM α :=
 match result with | .ok value => pure value | .error error => throw error
private def languageItem (world : TypeArena.World) (definition : DefinitionIdentity) : Except String (Option String) := do
 let id ← world.definitionRef definition
 let some declaration := world.definitions[id]?.bind (·.adtDeclaration) | throw "Box ADT raw declaration absent"
 pure declaration.langItem

/-- Pinned layout.rs::pointee_info_at(Box) and abi.rs scalar attributes.
Box is recognized by raw lang-item identity, never by its physical layout. -/
def classify (session : AbiSessionMaterial) (isReturn : Bool) (layout : TyAndLayout TypeId)
    (arguments : Array Miri.MIR.GenericArg) : RuntimeArrayTypes.CompilerM (ArgAbi TypeId) := do
 let world ← get
 let some (Miri.MIR.GenericArg.Type pointee) := arguments[0]? | throw "Box raw pointee argument absent"
 let global ← liftPure do
  match arguments[1]? with
  | none => pure true
  | some (Miri.MIR.GenericArg.Type allocator) =>
    let source ← match ← world.arena.lookupType allocator with
     | .constructed source => pure (some source)
     | .material source => world.arena.materialKey source
    match source with
    | some (.adt allocator _) => pure ((← languageItem world.arena allocator) == some "global_alloc_ty")
    | _ => pure false
  | _ => throw "Box allocator argument is not a type"
 let .Scalar (.Initialized (value := .Pointer _) (validRange := range)) := layout.layout.backendRepr
  | throw "Box thin ABI requires initialized scalar pointer layout"
 let child ← RuntimeArrayTypes.liftType (RuntimeMetadata.layoutInWorld world.metadata pointee)
 unless child.layout.isSized do throw "Box unsized pointee ABI unavailable"
 let permitted ← if session.optimization == .no then pure false else do
  if !(← WorldSourceAutoTraits.query pointee "unpin") then pure false
  else WorldSourceAutoTraits.query pointee "unsafe_unpin"
 let regular : UInt16 := 128 ||| (if range.contains 0 then 0 else 16) |||
   (if permitted && global && session.boxNoalias && !isReturn then 8 else 0)
 -- Boxes can be freed by the callee. Writable applies only to mutable refs.
 pure (ArgAbi.new layout fun _ _ =>
  {regular := regular,argExt := .None,pointeeSize := if permitted then child.layout.size else Size.ZERO,
   pointeeAlign := if child.layout.align.abi.pow2 > 0 then some child.layout.align.abi else none})

end Miri.Input.WorldBoxAbi
