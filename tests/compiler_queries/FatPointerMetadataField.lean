import Miri.Input.Decoder
import Miri.Input.GenericMaterialCodec

open Lean Miri.Input Miri.ABI
private def must [ToString ε] (value : Except ε A) : IO A :=
  match value with | .ok result => pure result | .error error => throw (IO.userError (toString error))
private def check (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)
private def nat (row : Json) (key : String) : IO Nat := must ((row.getObjVal? key).bind Json.getNat?)
private def boolean (row : Json) (key : String) : IO Bool := must ((row.getObjVal? key).bind Json.getBool?)
private def expectedLayout (row : Json) : IO LayoutData := do
  check ((← must ((row.getObjVal? "fields").bind Json.getStr?)) == "primitive") "oracle fields unsupported"
  check ((← must ((row.getObjVal? "backend").bind Json.getStr?)) == "initialized_pointer") "oracle backend unsupported"
  let space : AddressSpace := ⟨UInt32.ofNat (← nat row "address_space")⟩
  let range : WrappingRange := ⟨BitVec.ofNat 128 (← nat row "start"),BitVec.ofNat 128 (← nat row "end")⟩
  let niche ← must (row.getObjVal? "niche")
  let largest : Niche := ⟨← must (RuntimeMetadata.size (← nat niche "offset")),.Pointer space,
    ⟨BitVec.ofNat 128 (← nat niche "start"),BitVec.ofNat 128 (← nat niche "end")⟩⟩
  let maximum ← must (row.getObjVal? "max_repr_align")
  let maximum ← if maximum == .null then pure none else
    some <$> must (RuntimeMetadata.alignment (← must maximum.getNat?))
  pure ⟨.Primitive,.Single (← nat row "variant"),.Scalar (.Initialized (value := .Pointer space) (validRange := range)),some largest,
    ← boolean row "uninhabited",⟨← must (RuntimeMetadata.alignment (← nat row "align"))⟩,
    ← must (RuntimeMetadata.size (← nat row "size")),maximum,
    ← must (RuntimeMetadata.alignment (← nat row "unadjusted_align")),← boolean row "repr_c",
    UInt64.ofNat (← nat row "randomization_seed")⟩

def main (args : List String) : IO Unit := do
  let [sourcePath,oraclePath] := args | throw (IO.userError "expected current source and independent field oracle")
  let document := (← must (decodeJson (← IO.FS.readFile sourcePath))).document
  let runtime ← must ((RuntimeMetadata.ofDocument document).mapError toString)
  let rows ← must ((← must (Json.parse (← IO.FS.readFile oraclePath))).getArr?)
  let empty ← must (TypeArena.World.ofMaterial #[] #[] document.definitions #[] runtime.target.pointerSize.bytes.toNat)
  let some checked := runtime.checkedMaterial | throw (IO.userError "checked source material absent")
  let materialWorld := TypeArena.World.ofCheckedMaterial checked
  let mut world := empty
  let mut count := 0
  for row in rows do
    let term ← must (GenericMaterialCodec.readTerm 16384 (← must (row.getObjVal? "parent")))
    let expectedType ← must (GenericMaterialCodec.readTerm 16384 (← must (row.getObjVal? "field_type")))
    let (owner,next) ← must ((GenericInstantiationWorld.resolveType 16384 term).run world)
    world := next
    let (parent,next) ← must ((RuntimeMetadata.layoutInWorld runtime owner).run world)
    world := next
    let (field,next) ← must ((RuntimeMetadata.fieldLayoutForInWorld runtime parent 1).run world)
    world := next
    check ((← must (GenericInstantiationWorld.ofType world 16384 field.ty)) == expectedType)
      "vtable metadata field exact normalized type differs from independent compiler"
    check (field.layout == (← expectedLayout row)) "complete vtable metadata field layout differs from independent compiler"
    let (materialOwner,materialState) ← must ((GenericInstantiationWorld.resolveType 16384 term).run materialWorld)
    check (materialOwner < materialWorld.materialTypes.size) "oracle parent did not resolve to actual material source type"
    let (materialParent,materialState) ← must ((RuntimeMetadata.layoutInWorld runtime materialOwner).run materialState)
    let (materialField,materialState) ← must ((RuntimeMetadata.fieldLayoutForInWorld runtime materialParent 1).run materialState)
    check ((← must (GenericInstantiationWorld.ofType materialState 16384 materialField.ty)) == expectedType)
      "material vtable metadata field exact normalized type differs from independent compiler"
    check (materialField.layout == field.layout) "material and constructed pointer metadata field layouts differ"
    match (RuntimeMetadata.fieldLayoutForInWorld runtime parent 2).run world with
    | .error "pointer projection field index out of bounds" => pure ()
    | _ => throw (IO.userError "pointer field bounds residual changed")
    check (world.materialTypes.isEmpty && world.materialConstants.isEmpty && world.materialPredicates.isEmpty)
      "source field projection acquired copied material prefixes"
    count := count + 1
  check (count == 9) "expected nine independent field vectors"
  match SourceDynMethods.minimumEntries runtime.normalizationContext 0 0 none with
  | .ok 3 => pure ()
  | _ => throw (IO.userError "no-principal vtable minimum changed")
  let some declaration := runtime.normalizationContext.traits.traits[0]?
    | throw (IO.userError "source traits absent")
  match SourceDynMethods.minimumEntries runtime.normalizationContext 1024 0 (some declaration.definition) with
  | .error "vtable minimum source traversal exhausted" => pure ()
  | _ => throw (IO.userError "source traversal fuel exhaustion hidden")
  let invalidConstructor : GenericSubstitution.Term := .node .type "dynamic" ""
    (.cons (.binder #[] (.atom .aggregate "trait" "")) (.cons (.atom .region "static" "") .nil))
  match (GenericInstantiationWorld.resolveType 16384 invalidConstructor).run world with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "malformed existential constructor was accepted")
  let context := runtime.normalizationContext
  let duplicated := {context with traits := {context.traits with traits := context.traits.traits.push declaration}}
  match SourceDynMethods.minimumEntries duplicated 65536 16384 (some declaration.definition) with
  | .error "dyn source trait missing or ambiguous" => pure ()
  | _ => throw (IO.userError "duplicated trait source was accepted")
  let malformed := {declaration with parameters := #[]}
  let corrupted := {context with traits := {context.traits with
    traits := context.traits.traits.map fun source => if source.definition == declaration.definition then malformed else source}}
  match SourceDynMethods.minimumEntries corrupted 65536 16384 (some declaration.definition) with
  | .error "vtable minimum trait source header mismatch" => pure ()
  | _ => throw (IO.userError "corrupt trait source header was accepted")
  IO.println s!"PASS {count} material + {count} empty-prefix constructed pointer metadata fields: exact erased-region type and complete independent layout; no-principal count3, bounds and source fuel controls"
