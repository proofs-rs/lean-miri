import Miri.Frontend.FoundationSourceTypes
import Miri.Input.Decoder
import Miri.Input.SourcePhysical
open Lean Miri Miri.Input Miri.Input.SourceTypes
private def checked (value : Except String α) : IO α := match value with
  | .ok value => pure value | .error error => throw (IO.userError error)
private def matchesBound (source : SourceTypes.Material) (reference : ImportDocument)
    (bound : PatternBound) (value : MIR.TypeConst) : Bool := Id.run do
  match bound,value with
  | .constant (.value sourceType bits bytes),.Value compilerType tree =>
    let some (.primitive _ name) := source.types[sourceType]? | return false
    let some compiler := reference.types[compilerType]? | return false
    return compiler.display == name && tree.root == 0 && tree.nodes == #[.Leaf bits bytes]
  | .alias rigid kind sourceDefinition args,.Alias compilerRigid compilerKind compilerDefinition compilerArgs =>
    let some sourceDefinition := source.definitions[sourceDefinition]? | return false
    let some compilerDefinition := reference.definitions[compilerDefinition]? | return false
    return rigid == compilerRigid && kind == compilerKind && sourceDefinition.raw == compilerDefinition &&
      args.isEmpty && compilerArgs.isEmpty
  | _,_ => return false
def main (paths : List String) : IO Unit := do
  let [sourcePath,referencePath] := paths | throw (IO.userError "expected source and same-compiler reference")
  let source ← checked (Json.parse (← IO.FS.readFile sourcePath))
  let source ← checked (Frontend.Foundation.SourceTypesParser.material source)
  let reference ← checked (Input.decodeJson (← IO.FS.readFile referencePath))
  let reference := reference.document
  let some evidence := reference.runtimeTargetDataLayout | throw (IO.userError "compiler target absent")
  let target ← checked ((RuntimeMetadata.importTarget evidence).mapError toString)
  let mut layouts := 0
  let mut count := 0
  let mut aliasSeen := false
  for (expression,index) in source.types.zipIdx do
    if let .patternRange base lower upper := expression then
      let some (.primitive _ baseName) := source.types[base]? | throw (IO.userError "fixture base is not primitive")
      let found := reference.types.find? fun node => Id.run do
        let .patternType compilerBase (.range start finish) := node.shape | return false
        let some compilerBase := reference.types[compilerBase]? | return false
        let some start := reference.typeConstants[start]? | return false
        let some finish := reference.typeConstants[finish]? | return false
        return compilerBase.display == baseName && matchesBound source reference lower start && matchesBound source reference upper finish
      let some compilerNode := found | throw (IO.userError "range source/alias differs from compiler type constants")
      if let .alias .. := upper then aliasSeen := true
      if let .alias .. := upper then
        match SourceTypes.instantiate source #[] #[] index with
        | .error "Unsupported source pattern range bound witness unavailable" => pure ()
        | _ => throw (IO.userError "range demand erased its unevaluated bound")
      else
        let concrete ← checked (SourceTypes.instantiate source #[] #[] index)
        let actual ← checked (SourcePhysical.calculate source target concrete)
        let actual ← checked ((RuntimeMetadata.layout target actual).mapError toString)
        let some expected := reference.layouts[compilerNode.layoutId]? | throw (IO.userError "compiler range layout absent")
        let expected ← checked ((RuntimeMetadata.layout target expected).mapError toString)
        unless actual == expected do throw (IO.userError s!"complete concrete range layout differs: actual={reprStr actual}, compiler={reprStr expected}")
        layouts := layouts+1
      let invalid := Expr.patternRange base lower (.alias false .Anon source.definitions.size #[])
      let changed ← if h : index < source.types.size then
          pure {source with types := source.types.set index invalid h}
        else throw (IO.userError "range index absent")
      match changed.validate with
      | .error _ => pure ()
      | .ok _ => throw (IO.userError "missing bound source definition accepted")
      count := count+1
  unless count ≥ 5 && layouts ≥ 4 && aliasSeen do throw (IO.userError "literal/unevaluated/signed/full/normalized range coverage incomplete")
  for concrete in #[SourceTypes.Concrete.patternRange (.primitive "uint" "u8") 17 3,
      .patternRange (.primitive "int" "i8") 4 249] do
    match SourcePhysical.calculate source target concrete with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError "wrapping pattern range accepted")
  IO.println "PASS genuine literal/signed/full range layouts and bounds match compiler; unresolved alias, missing source and wrapping ranges reject"
