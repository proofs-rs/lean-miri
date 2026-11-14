import Miri.Input.Decoder
import Miri.Input.WorldSourceAutoTraits
open Lean Miri.Input Miri.Interpreter
private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error e => throw (IO.userError e)
private def reject (result : Except String α) (expected : String) : IO Unit := do
  match result with
  | .error actual => unless actual==expected do throw (IO.userError s!"wrong dyn auto residual: {actual}")
  | .ok _ => throw (IO.userError "dyn auto accepted unsupported source")
def main (args : List String) : IO Unit := do
  let [sourcePath,oraclePath] := args | throw (IO.userError "expected raw source and independent auto-trait oracle")
  let original := (← must (decodeJson (← IO.FS.readFile sourcePath))).document
  let document := {original with
    instances := #[],allocations := #[],functionAbis := #[],bodies := #[],bodyRoots := #[],
    queries := {original.queries with
      runtime := {original.queries.runtime with types := #[],instances := #[],virtualQueries := #[]},
      vtables := #[],instanceAbis := #[],shimAbis := some #[],namedShimAbis := some #[]}}
  let metadata ← must ((RuntimeMetadata.ofDocument document).mapError toString)
  let material ← must ((RuntimeArrayTypes.create metadata).mapError reprStr)
  let arena ← must (TypeArena.World.ofMaterial #[] #[] document.definitions #[] metadata.target.pointerSize.bytes.toNat)
  let instances ← must (InstanceArena.Store.ofSource arena #[])
  let empty := {material with arena,instances}
  let oracle ← must (Json.parse (← IO.FS.readFile oraclePath))
  let rows ← must ((← must (oracle.getObjVal? "queries")).getArr?)
  unless rows.size==7 do throw (IO.userError "dyn auto source oracle coverage changed")
  let mut positive := 0
  let mut negative := 0
  let mut residuals := 0
  for row in rows do
    let name ← must ((← must (row.getObjVal? "name")).getStr?)
    let term ← must (GenericMaterialCodec.readTerm 4096 (← must (row.getObjVal? "dynamic")))
    let (owner,start) ← must ((RuntimeArrayTypes.liftType (GenericInstantiationWorld.resolveType 4096 term)).run empty)
    for languageItem in #["freeze","unpin","unsafe_unpin"] do
      let expected ← must ((← must (row.getObjVal? languageItem)).getBool?)
      let (actual,after) ← must ((WorldSourceAutoTraits.query owner languageItem).run start)
      unless actual==expected do throw (IO.userError s!"source dyn {languageItem} differs from rustc for {name}")
      unless after.arena.constructedTypes==start.arena.constructedTypes &&
          after.arena.constructedConstants==start.arena.constructedConstants &&
          after.arena.constructedPredicates==start.arena.constructedPredicates && after.instances==start.instances do throw (IO.userError "dyn auto query changed identity arenas")
      if actual then positive := positive+1 else negative := negative+1
      if name=="query_plain" then
        let context := start.metadata.normalizationContext
        let #[declaration] := context.traits.traits.filter (·.langItem==some languageItem)
          | throw (IO.userError "auto trait declaration absent")
        let change := fun replacement => {start with metadata := {start.metadata with normalizationContext :=
          {context with traits := {context.traits with traits := context.traits.traits.map fun source =>
            if source.definition==declaration.definition then replacement else source}}}}
        let blanket : TraitSelection.Impl := {
          definition := declaration.definition,parameters := #[.type],
          traitRef := ⟨declaration.definition,#[.parameter .type 0]⟩,
          polarity := .positive,isDefault := false,associatedValues := #[]}
        reject ((WorldSourceAutoTraits.query owner languageItem).run
          (change {declaration with implementations := #[blanket]}))
          "dyn auto possibly applicable manual impl requires source candidate winnowing"
        let dynamicImpl := {blanket with parameters := #[],traitRef := ⟨declaration.definition,#[term]⟩}
        reject ((WorldSourceAutoTraits.query owner languageItem).run
          (change {declaration with implementations := #[dynamicImpl]}))
          "dynamic impl relevance requires principal trait classification"
        let aliasImpl := {blanket with parameters := #[],traitRef := ⟨declaration.definition,
          #[.definition .type "alias_projection_not_rigid" declaration.definition .nil]⟩}
        reject ((WorldSourceAutoTraits.query owner languageItem).run
          (change {declaration with implementations := #[aliasImpl]}))
          "dyn auto possibly applicable manual impl requires source candidate winnowing"
        let some first := declaration.implementations[0]? | throw (IO.userError "real manual impl coverage absent")
        reject ((WorldSourceAutoTraits.query owner languageItem).run
          (change {declaration with implementations := declaration.implementations.push first}))
          "dyn auto duplicate raw impl definition"
        residuals := residuals+4
  unless positive==6 && negative==15 && residuals==12 do throw (IO.userError "dyn auto control counts changed")
  IO.println "PASS 7 actual dyn objects ×3 auto traits: 6 positives,15 negatives; 3 blanket+3 dynamic+3 alias+3 duplicate-catalog residuals"
