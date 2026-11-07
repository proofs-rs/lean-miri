import Miri.Input.Reader.Catalog
import Miri.Input.DecoderValues

namespace Miri.Input.Reader
open Lean DecoderValues

private def field (catalog : Catalog) (j : Json) (key path : String) : Except String Json := do
  catalog.inspect (← catalog.field j key path) (joinPath path key)
private def fieldString (catalog : Catalog) (j : Json) (key path : String) : Except String String := do
  catalog.string (← field catalog j key path) (joinPath path key)
private def fieldNat (catalog : Catalog) (j : Json) (key path : String) : Except String Nat := do
  catalog.natural (← field catalog j key path) (joinPath path key)
private def fieldBool (catalog : Catalog) (j : Json) (key path : String) : Except String Bool := do
  catalog.boolean (← field catalog j key path) (joinPath path key)
private def arrayField (catalog : Catalog) (j : Json) (key path : String) : Except String (Array Json) := do
  catalog.array (← field catalog j key path) (joinPath path key)
private def Catalog.status? (catalog : Catalog) (j : Json) (path : String) : Except String (Option String) := do
  match ← catalog.inspect j path with
  | .obj _ =>
    match ← catalog.optionalField j "status" path with
    | none => return none
    | some value => return (catalog.string value path).toOption
  | _ => return none

private partial def validateMirIndicesAux (catalog : Catalog) (raw : Json) (path : String)
    (localCount : Nat) (seen : Std.HashSet Nat) : Except String (Std.HashSet Nat) := do
  let shared ← catalog.sharedId? raw path
  if let some id := shared then
    if seen.contains id then return seen
  let j ← catalog.inspect raw path
  let finish := fun seen => match shared with | some id => seen.insert id | none => seen
  if (← catalog.status? j path) == some "debug_payload" then return seen
  match j with
  | .arr values =>
    let mut index := 0
    let mut seen := seen
    for value in values do
      seen ← validateMirIndicesAux catalog value s!"{path}[{index}]" localCount seen
      index := index + 1
    return finish seen
  | .obj fields =>
    let mut seen := seen
    for (key, value) in fields.toList do
      if key == "local" then
        let value ← catalog.inspect value path
        let id ← value.getNat? |>.mapError fun e => s!"{joinPath path key}: expected local index ({e})"
        if id >= localCount then throw s!"{joinPath path key}: local {id} is out of range (locals={localCount})"
      if key == "projection" then
        let value ← catalog.inspect value path
        let projections ← value.getArr? |>.mapError fun e => s!"{joinPath path key}: expected projection array ({e})"
        for (projection, index) in projections.toList.zipIdx do
          let pPath := s!"{joinPath path key}[{index}]"
          let kind ← fieldString catalog projection "kind" pPath
          if kind == "Index" then
            let id ← fieldNat catalog projection "local" pPath
            if id >= localCount then throw s!"{pPath}.local: local {id} is out of range (locals={localCount})"
          if kind == "ConstantIndex" then
            let _ ← fieldNat catalog projection "offset" pPath
            let _ ← fieldNat catalog projection "min_length" pPath
            let _ ← fieldBool catalog projection "from_end" pPath
          if kind == "Subslice" then
            let _ ← fieldNat catalog projection "from" pPath
            let _ ← fieldNat catalog projection "to" pPath
            let _ ← fieldBool catalog projection "from_end" pPath
          if kind == "Field" then
            let _ ← fieldNat catalog projection "index" pPath
            let _ ← field catalog projection "field_type" pPath
          if kind == "Downcast" then
            let _ ← fieldNat catalog projection "variant_index" pPath
          if kind == "OpaqueCast" then let _ ← field catalog projection "cast_type" pPath
          if kind == "UnwrapUnsafeBinder" then let _ ← field catalog projection "inner_type" pPath
          if isKnownProjection kind then let _ ← field catalog projection "resulting_type" pPath
      seen ← validateMirIndicesAux catalog value (joinPath path key) localCount seen
    return finish seen
  | _ => return finish seen

private def validateMirIndices (catalog : Catalog) (value : Json) (path : String)
    (localCount : Nat) : Except String Unit := do
  discard <| validateMirIndicesAux catalog value path localCount {}

private def checkBlockIndex (catalog : Catalog) (value : Json) (path : String) (blockCount : Nat) : Except String Unit := do
  let value ← catalog.inspect value path
  let id ← value.getNat? |>.mapError fun e => s!"{path}: expected basic-block index ({e})"
  if id >= blockCount then throw s!"{path}: basic block {id} is out of range (blocks={blockCount})"

private def checkRequiredEdge (catalog : Catalog) (j : Json) (key path : String) (blockCount : Nat) : Except String Unit := do
  checkBlockIndex catalog (← field catalog j key path) (joinPath path key) blockCount

private def checkOptionalEdge (catalog : Catalog) (j : Json) (key path : String) (blockCount : Nat) : Except String Unit := do
  let value ← catalog.optionalField j key path
  match ← value.mapM (fun value => catalog.inspect value path) with
  | none => throw s!"{path}: missing optional edge field `{key}`"
  | some .null => pure ()
  | some value => checkBlockIndex catalog value (joinPath path key) blockCount

private def validateUnwind (catalog : Catalog) (j : Json) (path : String) (blockCount : Nat) : Except String Unit := do
  let kind ← fieldString catalog j "kind" path
  if kind == "Cleanup" then checkRequiredEdge catalog j "target" path blockCount

private def validateTerminatorEdges (catalog : Catalog) (j : Json) (path : String) (blockCount : Nat) : Except String Unit := do
  let variant ← fieldString catalog j "variant" path
  match variant with
  | "Goto" => checkRequiredEdge catalog j "target" path blockCount
  | "SwitchInt" =>
    checkRequiredEdge catalog j "otherwise" path blockCount
    let targets ← arrayField catalog j "targets" path
    for (target, index) in targets.toList.zipIdx do
      checkRequiredEdge catalog target "target" s!"{joinPath path "targets"}[{index}]" blockCount
  | "Drop" =>
    checkRequiredEdge catalog j "target" path blockCount
    checkOptionalEdge catalog j "async_drop" path blockCount
    validateUnwind catalog (← field catalog j "unwind" path) (joinPath path "unwind") blockCount
  | "Call" =>
    checkOptionalEdge catalog j "target" path blockCount
    validateUnwind catalog (← field catalog j "unwind" path) (joinPath path "unwind") blockCount
  | "Assert" =>
    checkRequiredEdge catalog j "target" path blockCount
    validateUnwind catalog (← field catalog j "unwind" path) (joinPath path "unwind") blockCount
  | "Yield" =>
    checkRequiredEdge catalog j "resume" path blockCount
    checkOptionalEdge catalog j "drop" path blockCount
  | "FalseEdge" =>
    checkRequiredEdge catalog j "real_target" path blockCount
    checkRequiredEdge catalog j "imaginary_target" path blockCount
  | "FalseUnwind" =>
    checkRequiredEdge catalog j "real_target" path blockCount
    validateUnwind catalog (← field catalog j "unwind" path) (joinPath path "unwind") blockCount
  | _ => pure ()

private def validateBody (catalog : Catalog) (j : Json) (path : String) : Except String Unit := do
  let locals ← arrayField catalog j "locals" path
  let blocks ← arrayField catalog j "basic_blocks" path
  if locals.isEmpty then throw s!"{joinPath path "locals"}: MIR body must declare the return local"
  if blocks.isEmpty then throw s!"{joinPath path "basic_blocks"}: MIR body must contain a start block"
  let mut index := 0
  for localDecl in locals do
    let id ← fieldNat catalog localDecl "local" s!"{joinPath path "locals"}[{index}]"
    if id != index then throw s!"{joinPath path "locals"}[{index}]: local declarations must be densely ordered"
    index := index + 1
  index := 0
  for block in blocks do
    let blockPath := s!"{joinPath path "basic_blocks"}[{index}]"
    let id ← fieldNat catalog block "block" blockPath
    if id != index then throw s!"{blockPath}: basic blocks must be densely ordered"
    let statements ← arrayField catalog block "statements" blockPath
    for (statement, stmtIndex) in statements.toList.zipIdx do
      let kind ← field catalog statement "kind" s!"{blockPath}.statements[{stmtIndex}]"
      validateMirIndices catalog kind s!"{blockPath}.statements[{stmtIndex}].kind" locals.size
    let termWrapper ← field catalog block "terminator" blockPath
    if termWrapper == .null then throw s!"{blockPath}: missing terminator"
    let term ← field catalog termWrapper "kind" s!"{blockPath}.terminator"
    validateMirIndices catalog term s!"{blockPath}.terminator.kind" locals.size
    validateTerminatorEdges catalog term s!"{blockPath}.terminator.kind" blocks.size
    index := index + 1

private partial def visit (catalog : Catalog) (raw : Json) (path : String)
    (seen : Std.HashSet Nat) : Except String (Std.HashSet Nat) := do
  let id ← catalog.sharedId? raw path
  if let some id := id then
    if seen.contains id then return seen
  let j ← catalog.inspect raw path
  if (← catalog.status? j path) == some "debug_payload" then return seen
  let finish := fun seen => match id with | some id => seen.insert id | none => seen
  match j with
  | .arr values =>
    let mut seen := seen
    for (child, index) in values.toList.zipIdx do
      seen ← visit catalog child s!"{path}[{index}]" seen
    return finish seen
  | .obj fields =>
    let hasLocals := (j.getObjVal? "locals").isOk
    let hasBlocks := (j.getObjVal? "basic_blocks").isOk
    if hasLocals != hasBlocks then throw s!"{path}: body requires both locals and basic_blocks"
    if hasLocals && hasBlocks then validateBody catalog j path
    let mut seen := seen
    for (key, child) in fields.toList do
      seen ← visit catalog child (joinPath path key) seen
    return finish seen
  | _ => return finish seen

def Catalog.validateBodies (catalog : Catalog) : Except String Unit := do
  discard <| visit catalog catalog.root "$" {}

end Miri.Input.Reader
