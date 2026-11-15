import Miri.Frontend.FoundationSourceMaterial

open Lean Miri Miri.Frontend.Foundation
private def checked (value : Except String α) : IO α :=
  match value with | .ok v => pure v | .error e => throw (IO.userError e)
private def check (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)
private def rejects (value : Except String α) : IO Unit :=
  match value with | .error _ => pure () | .ok _ => throw (IO.userError "invalid typed source accepted")

def main (paths : List String) : IO Unit := do
  for path in paths do
    let source ← checked (Json.parse (← IO.FS.readFile path))
    let document ← checked (decode source)
    let material ← checked (typedSourceMaterial document)
    checked material.validate
    check (material.target.triple == document.target.triple &&
      material.target.pointerSizeBits == document.target.pointerSizeBits &&
      material.target.runtimeDataLayout.isSome) "typed source target projection differs"
    let headers ← checked (sourceItemDeclarations document)
    let foreign ← checked (ForeignDeclarationSource.derive document.source)
    let callable := foreign.declarations.filter fun item =>
      item.kind == "function" || item.kind == "associated_function"
    let expected := ((headers.map (·.definition) ++ callable.map (·.definition)).toList.eraseDups).toArray
    check (material.declarations.map (·.definition) == expected && !headers.isEmpty)
      "typed source declaration coverage/order differs"
    for header in headers do
      check (material.declarations.find? (·.definition == header.definition) == some header)
        "typed source header role/identity changed"
    for item in callable do
      let some declaration := material.declarations.find? (·.definition == item.definition)
        | throw (IO.userError "typed foreign header absent")
      let kind : Input.SourceDeclarations.ItemKind :=
        if item.kind == "function" then .function else .associatedFunction
      check (declaration.path == item.path && declaration.kind == kind && declaration.parameters == item.parameters)
        "typed foreign declaration differs from independently parsed symbolic source"
    for declaration in material.declarations do
      let slots ← checked (Input.SourceDeclarations.fullParameters material.genericLayers declaration.definition)
      check (slots == declaration.parameters) "typed source full generic slots differ"
    check (material.genericMir.isSome && material.physical.isSome && material.abi.isSome &&
      material.constraints == .unsupported) "typed source components missing or constraints overclaimed"
    rejects ({material with target := {material.target with triple := ""}}.validate)
    rejects ({material with genericLayers := #[]}.validate)
    let some declaration := material.declarations[0]? | throw (IO.userError "declaration absent")
    rejects ({material with declarations := material.declarations.push declaration}.validate)
    let mismatch := {declaration with parameters := declaration.parameters.push .region}
    rejects ({material with declarations := #[mismatch]}.validate)
    let some layer := material.genericLayers[0]? | throw (IO.userError "layer absent")
    rejects ({material with genericLayers := material.genericLayers.push layer}.validate)
    for layer in material.genericLayers do
      for parameter in layer.parameters do
        if parameter.definition == layer.owner then
          check (parameter.index == 0 && parameter.kind == .typeParameter &&
            layer.flattenedParameters[0]? == some .typeParameter)
            "typed implicit Self raw identity/slot view changed"
    let some evidence := material.target.runtimeDataLayout | throw (IO.userError "target evidence absent")
    let bad := {material.target with runtimeDataLayout := some {evidence with pointerWidthBits := evidence.pointerWidthBits + 8}}
    rejects ({material with target := bad}.validate)
    IO.println s!"typed source {path}: {material.declarations.size} Item declarations, {material.genericLayers.size} lexical layers; typed MIR/types/ABI retained; unsupported constructors reject at demand"
