import Miri.Input.Decoder
import Miri.Input.CompilerDiscriminantFacts
open Lean Miri.Input TypeArena
private def must (value : Except String α) : IO α :=
  match value with | .ok result => pure result | .error error => throw (IO.userError error)
private def check (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)
/-- Oracle-only projection: enum discriminants belong to the physical ADT
owner, independently of instantiated arguments. No old compiler source schema
is imported, and this reader never supplies runtime answers. -/
private def oracleInfo (raw : Json) (identity : GenericSubstitution.DefinitionIdentity) : Except String DiscriminantInfo := do
  let definitions ← (← raw.getObjVal? "definitions").getArr?
  let nodes ← (← raw.getObjVal? "types").getArr?
  let pool ← (← raw.getObjVal? "discriminants").getArr?
  let mut matchedInfos : Array DiscriminantInfo := #[]
  for node in nodes do
    let shape ← node.getObjVal? "shape"
    unless (← (← shape.getObjVal? "kind").getStr?) == "adt" do continue
    let definitionId ← (← shape.getObjVal? "def_id").getNat?
    let some definition := definitions[definitionId]? | throw "oracle ADT definition absent"
    unless (← (← definition.getObjVal? "crate").getNat?) == identity.crateIndex &&
        (← (← definition.getObjVal? "index").getNat?) == identity.index do continue
    let index ← (← (← node.getObjVal? "compiler_facts").getObjVal? "discriminants").getNat?
    let some info := pool[index]? | throw "oracle discriminant pool index absent"
    matchedInfos := matchedInfos.push (← JsonReader.run DecoderValues.parseDiscriminants info.compress)
  let some first := matchedInfos[0]? | throw "oracle physical enum owner absent"
  unless matchedInfos.all (fun info => info.hasDiscriminants == first.hasDiscriminants &&
      info.adtVariantCount == first.adtVariantCount &&
      info.values.map (fun value => (value.variant,value.bits)) == first.values.map (fun value => (value.variant,value.bits))) do
    throw "oracle enum instantiations disagree on owner discriminants"
  pure first
def main (args : List String) : IO Unit := do
  let [path,oraclePath] := args | throw (IO.userError "expected raw source and compiler catalog exports")
  let source := (← must (decodeJson (← IO.FS.readFile path))).document
  let oracle ← must (Json.parse (← IO.FS.readFile oraclePath))
  let runtime ← must ((RuntimeMetadata.ofDocument source).mapError toString)
  let context ← must (CompilerFacts.ofProgram runtime (← must (lowerProgram source)))
  let world ← must (World.ofDocument source)
  let mut count := 0
  for node in source.types do
    if let .adt data := node.shape then
      if data.kind == .enumKind then
        let some declaration := (source.definitions[data.definition]?).bind (·.adtDeclaration)
          | throw (IO.userError "raw enum declaration missing")
        if (← must (RelativeDiscriminants.values (world.pointerBytes * 8) declaration)).isSome then
          check ((node.compilerFacts.bind (·.discriminants)).isNone) "producer copied covered discriminant catalog"
          let some owner := source.definitions[data.definition]? | throw (IO.userError "source enum owner absent")
          let info ← must (oracleInfo oracle ⟨owner.crateIndex,owner.index⟩)
          for expected in info.values do
            let (actual,_) ← must ((CompilerDiscriminantFacts.discriminantValue context node.id expected.variant).run world)
            check (actual.any (fun value => value.2.toNat == expected.bits)) "production raw value differs from compiler"
            let (variant,_) ← must ((CompilerDiscriminantFacts.variantForDiscriminant context node.id (BitVec.ofNat 128 expected.bits)).run world)
            check (variant == some expected.variant) "raw reverse query differs from compiler"
          let (actualCount,_) ← must ((CompilerDiscriminantFacts.adtVariantCount context node.id).run world)
          check (actualCount == declaration.variantCount) "raw count differs"
          if data.args.isEmpty then
            let some definition := source.definitions[data.definition]? | throw (IO.userError "definition missing")
            let empty ← must (World.ofMaterial #[] #[] source.definitions world.pointerBytes)
            let (novel,fresh) ← must ((do
              let _ ← World.internType (.tuple #[])
              World.internType (.adt ⟨definition.crateIndex,definition.index⟩ #[])).run empty)
            for expected in info.values do
              let (actual,_) ← must ((CompilerDiscriminantFacts.discriminantValue context novel expected.variant).run fresh)
              check (actual.any (fun value => value.2.toNat == expected.bits)) "novel empty-prefix enum differs from compiler"
            let (layout,_) ← must ((CompilerDiscriminantFacts.discriminantLayout context novel).run fresh)
            check (layout.layout.size.bytes.toNat == world.pointerBytes || declaration.representation.integer.isSome)
              "novel default enum public discriminant is not target isize"
          if count == 0 then
            for missing in #[true,false] do
              let variants := declaration.variants.mapIdx fun i variant =>
                if i == 0 then {variant with discriminant := .relative 1} else variant
              let replacement := if missing then none else some {declaration with variants := variants}
              let definitions := source.definitions.mapIdx fun index definition =>
                if index != data.definition then definition else {definition with adtDeclaration := replacement}
              match World.ofMaterial source.types source.typeConstants definitions world.pointerBytes with
              | .error _ => pure ()
              | .ok malformed =>
                check (!((CompilerDiscriminantFacts.variantForDiscriminant context node.id 0).run malformed).isOk)
                  "missing/malformed raw enum silently borrowed residual catalog"
            let poisonedTypes := source.types.map fun original =>
              if original.id != node.id then original else
              {original with compilerFacts := original.compilerFacts.map fun facts =>
                {facts with discriminants := some ⟨false,none,#[]⟩, typeQueries := facts.typeQueries.filter (·.1 != "normalized")}}
            let poisoned ← must (World.ofMaterial poisonedTypes source.typeConstants source.definitions world.pointerBytes)
            check (((CompilerDiscriminantFacts.variantForDiscriminant context node.id 0).run poisoned).toOption.map (·.1) == some (some 0))
              "raw enum trusted poisoned material catalog"
            let (value,_) ← must ((CompilerDiscriminantFacts.discriminantValue context node.id 0).run poisoned)
            check (value.any (·.2.toNat == 0)) "raw enum required unrelated normalization answer"
          count := count + 1
  let mut explicitCount := 0
  for node in source.types do
    if let .adt data := node.shape then
      if data.kind == .enumKind then
        let some declaration := (source.definitions[data.definition]?).bind (·.adtDeclaration)
          | throw (IO.userError "explicit declaration absent")
        if (← must (RelativeDiscriminants.values (world.pointerBytes*8) declaration)).isNone then
          let some info := node.compilerFacts.bind (·.discriminants)
            | throw (IO.userError "explicit CTFE residual missing from source")
          for expected in info.values do
            let (actual,_) ← must ((CompilerDiscriminantFacts.variantForDiscriminant context node.id (BitVec.ofNat 128 expected.bits)).run world)
            check (actual == some expected.variant) "explicit material residual changed"
          for malformedInfo in #[{info with hasDiscriminants := false},
              {info with adtVariantCount := none}, {info with values := info.values.pop},
              {info with values := info.values.map fun value => {value with typeId := source.queries.primitives.bool}}] do
            let malformedTypes := source.types.map fun original =>
              if original.id != node.id then original else
              {original with compilerFacts := original.compilerFacts.map fun facts => {facts with discriminants := some malformedInfo}}
            let malformed ← must (World.ofMaterial malformedTypes source.typeConstants source.definitions world.pointerBytes)
            check (!((CompilerDiscriminantFacts.discriminantValue context node.id 0).run malformed).isOk)
              "malformed explicit enum residual silently yielded value/no-value"
            check (!((CompilerDiscriminantFacts.variantForDiscriminant context node.id 0).run malformed).isOk)
              "malformed explicit enum residual silently yielded invalid-tag result"
          let stripped := source.types.map fun original =>
            if original.id != node.id then original else
            {original with compilerFacts := original.compilerFacts.map fun facts => {facts with discriminants := none}}
          let missing ← must (World.ofMaterial stripped source.typeConstants source.definitions world.pointerBytes)
          check (!((CompilerDiscriminantFacts.variantForDiscriminant context node.id 0).run missing).isOk)
            "explicit enum fabricated missing CTFE material"
          -- Synthetic malformed binder control: omission cannot mean no enum values.
          let binderTypes := stripped.map fun original =>
            if original.id == node.id then {original with shape := .unsafeBinder node.id #[]} else original
          let binder ← must (World.ofMaterial binderTypes source.typeConstants source.definitions world.pointerBytes)
          check (!((CompilerDiscriminantFacts.variantForDiscriminant context node.id 0).run binder).isOk)
            "binder missing residual silently became non-discriminant type"
          explicitCount := explicitCount + 1
  check (explicitCount > 0) "no explicit residual controls executed"
  check (count > 0) "no relative enums compared"
  IO.println s!"PASS {count} runtime raw enums agree; {explicitCount} explicit CTFE residual/missing/binder controls"
