import Miri.Input.Reader.SourceSpan
import Miri.Input.Reader.AbiQueries

namespace Miri.Input.Reader
open Lean Miri.MIR

private def readOptional (catalog : Catalog) (table : SharedTable SourceSpanData)
    (input : Json) (key path : String) : Except String (Option Nat × SharedTable SourceSpanData) := do
  match ← catalog.optionalField input key path with
  | none | some .null => return (none, table)
  | some value =>
    let (id, table) ← catalog.readSourceSpan table value s!"{path}.{key}"
    return (some id, table)

private def core (catalog : Catalog) (abis : AbiTables) (table : SharedTable SourceSpanData)
    (source : BodyCore) (input : Json) (path : String) :
    Except String (BodyCore × SharedTable SourceSpanData) := do
  let (span, table) ← readOptional catalog table input "span" path
  let (definitionSpan, table) ← readOptional catalog table input "preamble_def_span" path
  let rawBlocks ← catalog.array (← catalog.field input "basic_blocks" path) s!"{path}.basic_blocks"
  unless rawBlocks.size == source.blocks.size do throw s!"{path}: block table size mismatch"
  let mut blocks := #[]
  for (raw, index) in rawBlocks.toList.zipIdx do
    let some block := source.blocks[index]? | throw s!"{path}: source block absent"
    let kind ← catalog.field (← catalog.field raw "terminator" path) "kind" path
    let callAbi ← match ← catalog.optionalField kind "resolution" path with
      | none | some .null => pure none
      | some resolution =>
        match ← catalog.optionalField resolution "fn_abi" path with
        | none | some .null => pure none
        | some value => some <$> catalog.abiReference abis value path
    blocks := blocks.push {block with callAbi}
  return ({source with span, definitionSpan, blocks}, table)

private def promoted (catalog : Catalog) (abis : AbiTables) (table : SharedTable SourceSpanData)
    (source : Array PromotedBody) (input : Json) (path : String) :
    Except String (Array PromotedBody × SharedTable SourceSpanData) := do
  let values ← match ← catalog.optionalField input "promoted_bodies" path with
    | none | some .null => pure #[]
    | some array => catalog.array array s!"{path}.promoted_bodies"
  unless values.size == source.size do throw s!"{path}: promoted body table size mismatch"
  let mut table := table
  let mut result := #[]
  for (value, index) in values.toList.zipIdx do
    let some entry := source[index]? | throw s!"{path}: promoted body entry missing"
    let childPath := s!"{path}.promoted_bodies[{index}].body"
    let updated ← match entry.body with
      | none => pure entry
      | some sourceBody =>
        let raw ← catalog.field value "body" childPath
        let (body, next) ← core catalog abis table sourceBody raw childPath
        table := next
        pure {entry with body := some body}
    result := result.push updated
  return (result, table)

private def body (catalog : Catalog) (abis : AbiTables) (table : SharedTable SourceSpanData)
    (source : Body) (input : Json) (path : String) : Except String (Body × SharedTable SourceSpanData) := do
  let (bodyCore, table) ← core catalog abis table source.toBodyCore input path
  let (children, table) ← promoted catalog abis table source.promotedBodies input path
  return ({bodyCore with promotedBodies := children}, table)

def Catalog.readSpans (catalog : Catalog) (abis : AbiTables) (bodies : Array Body) (instances : Array InstanceNode) :
    Except String (Array Body × Array InstanceNode × SharedTable SourceSpanData) := do
  let values ← catalog.array (← catalog.field catalog.root "bodies" "$") "$.bodies"
  unless values.size == bodies.size do throw "$.bodies: body table size mismatch"
  let mut table : SharedTable SourceSpanData := Array.replicate catalog.nodes.size none
  let mut result := #[]
  for (value, index) in values.toList.zipIdx do
    let some source := bodies[index]? | throw "$.bodies: body table entry missing"
    let (parsed, next) ← body catalog abis table source value s!"$.bodies[{index}]"
    table := next
    result := result.push parsed
  let values ← catalog.array (← catalog.field catalog.root "instances" "$") "$.instances"
  unless values.size == instances.size do throw "$.instances: instance table size mismatch"
  let mut instanceResult := #[]
  for (value, index) in values.toList.zipIdx do
    let some source := instances[index]? | throw "$.instances: instance table entry missing"
    let path := s!"$.instances[{index}]"
    let parsedBody ← match source.body with
      | none => pure none
      | some sourceBody =>
        let raw ← catalog.field value "body" path
        let (parsed, next) ← body catalog abis table sourceBody raw s!"{path}.body"
        table := next
        pure (some parsed)
    let (children, next) ← promoted catalog abis table source.promotedBodies value path
    table := next
    instanceResult := instanceResult.push {source with body := parsedBody, promotedBodies := children}
  return (result, instanceResult, table)

end Miri.Input.Reader
