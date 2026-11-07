import MiriTests.Input.ReferenceDecoder
import Miri.Input.CompilerConstantQueries
import Miri.Input.NormalizationBody
import Miri.Input.Reader.Catalog

open Lean Miri Miri.Input Miri.Interpreter

private def must (value : Except String A) : IO A :=
  match value with
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

private inductive Segment where
  | field (name : String)
  | index (value : Nat)

private partial def constants (input : Json) (path : Array Segment := #[]) : Array (Array Segment × Json) :=
  if ((input.getObjVal? "constant").bind (fun value => value.getObjValAs? String "kind")).toOption == some "evaluated_const" then
    #[(path,input)]
  else match input with
    | .arr values => (values.mapIdx (fun index value => constants value (path.push (.index index)))).flatten
    | .obj fields => (fields.toList.toArray.map (fun (key,value) => constants value (path.push (.field key)))).flatten
    | _ => #[]

private def atPath (input : Json) (path : Array Segment) : Except String Json :=
  path.foldlM (fun input part => match part with
    | .field name => input.getObjVal? name
    | .index index => do
      let values ← input.getArr?
      let some value := values[index]? | throw "oracle array index absent"
      pure value) input

private def wirePath (catalog : Reader.Catalog) (input : Json) (path : Array Segment) : Except String Json :=
  path.foldlM (fun input part => match part with
    | .field name => catalog.field input name "oracle"
    | .index index => do
      let values ← catalog.array input "oracle"
      let some value := values[index]? | throw "wire oracle array index absent"
      pure value) input

private def bodyWire (catalog : Reader.Catalog) (path : String) : Except String Json := do
  let mut value := catalog.root
  for segment in (path.splitOn ".").drop 1 do
    match segment.splitOn "[" with
    | [name] => value ← catalog.field value name path
    | [name,index] =>
      let some index := (index.dropEnd 1).toString.toNat? | throw "body source index malformed"
      let values ← catalog.array (← catalog.field value name path) path
      let some entry := values[index]? | throw "body wire source absent"
      value := entry
    | _ => throw "body source path malformed"
  return value

private def normalized (body : Json) (location : MIR.Location) (path : Array Segment) : Except String Json := do
  let blocks ← (← body.getObjVal? "basic_blocks").getArr?
  let some block := blocks.find? (fun block => block.getObjValAs? Nat "block" == .ok location.block) | throw "normalized block absent"
  let statements ← (← block.getObjVal? "statements").getArr?
  let envelope ← if location.statementIndex == statements.size then block.getObjVal? "terminator" else
    match statements[location.statementIndex]? with
    | some value => pure value
    | none => throw "normalized statement absent"
  atPath envelope path

def main (args : List String) : IO Unit := do
  let some path := args.head? | throw (IO.userError "usage: ConstantQueryIDs <export.json>")
  let source ← IO.FS.readFile path
  let catalog ← must (Reader.Catalog.parse (← must (Json.parse source)))
  let decoded ← must (decodeRuntimeJson source)
  let runtime ← must ((RuntimeMetadata.ofDocument decoded.document).mapError toString)
  let prepared ← must (CompilerConstantQueries.prepare (← must (RuntimeProgram.ofProgram (← must (lowerCoreProgram decoded.document)))))
  let oracle ← must (decodeRuntimeJsonReference source)
  let oracleProgram ← must (lowerCoreProgram oracle.document)
  let program := prepared.program
  let ctx := LowerContext.ofDocument oracleProgram.input
  let mut count := 0
  for (body,index) in oracleProgram.bundle.bodies.toList.zipIdx do
    let wire ← must (bodyWire catalog body.input.sourcePath)
    let query ← must (body.input.payload.getObjVal? "constant_query_context")
    let normal ← must (NormalizationBody.resolve (← must (query.getObjVal? "normalization")) body.input.payload)
    let (callee,_) ← must (CompilerInstance.decode ctx program.compilerTables query)
    for block in (← must (body.input.payload.getObjVal? "basic_blocks" >>= Json.getArr?)) do
      let blockId ← must (block.getObjValAs? Nat "block")
      let statements ← must (block.getObjVal? "statements" >>= Json.getArr?)
      let instructions := statements.push (← must (block.getObjVal? "terminator"))
      for (instruction,statement) in instructions.toList.zipIdx do
        let pathPrefix : Array Segment := if statement == statements.size then
          #[Segment.field "basic_blocks",.index blockId,.field "terminator"] else
          #[Segment.field "basic_blocks",.index blockId,.field "statements",.index statement]
        for (path,original) in constants instruction do
          let reference ← must (wirePath catalog wire (pathPrefix ++ path))
          let some id ← must (catalog.sharedId? reference "constant oracle") | throw (IO.userError "fixture has an inline constant")
          let normal ← must (normalized normal ⟨blockId,statement⟩ path)
          let (original,_) ← must (lowerCompilerConstOperand ctx program.compilerTables (← must (ctx.decodeCompilerValue original)))
          let (constant,_) ← must (lowerCompilerConstOperand ctx program.compilerTables (← must (ctx.decodeCompilerValue normal)))
          let ty ← must ((← must (normal.getObjVal? "type")).getObjValAs? Nat "type_id")
          let value ← must (lowerCompilerConstValue ctx ty (← must (ctx.decodeCompilerValue (← must ((← must (normal.getObjVal? "constant")).getObjVal? "value")))) )
          let actual ← must (CompilerConstantQueries.lookup prepared ⟨index,⟨id⟩⟩)
          unless actual.fnInstance == callee && actual.original == original.value &&
              actual.normalized == constant.value && actual.span == constant.span && actual.value == value do
            throw (IO.userError s!"constant compiler evidence changed at body {index}, constant {id}")
          count := count + 1
    unless !(CompilerConstantQueries.lookup prepared ⟨index,⟨program.input.mirTables.mir.constants.size⟩⟩).isOk do
      throw (IO.userError "out-of-bounds constant query accepted")
  unless count > 0 do throw (IO.userError "fixture contains no constant query occurrences")
  IO.println s!"constant query IDs: PASS ({count} source occurrences; body-scoped normalization/evaluation and bounds)"
