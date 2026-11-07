import Miri.Input.Reader.MIRState
import Miri.Input.Reader.Table
import Miri.MIR.SyntaxTables

namespace Miri.Input.Reader.PlaceReader
open Lean Miri.MIR

abbrev State := MIRReader.State
abbrev Decode := MIRReader.Decode

private def typeId (catalog : Catalog) (count : Nat) (input : Json) (path : String) : Except String Nat := do
  let id ← catalog.natural (← catalog.field input "type_id" path) path
  unless id < count do throw s!"{path}: invalid type ID {id}"
  return id

private def projectionValue (catalog : Catalog) (typeCount : Nat) (input : Json) (path : String) : Except String ProjectionElem := do
  let natural := fun key => do catalog.natural (← catalog.field input key path) path
  let boolean := fun key => do catalog.boolean (← catalog.field input key path) path
  let ty := fun key => do typeId catalog typeCount (← catalog.field input key path) path
  let kind ← catalog.string (← catalog.field input "kind" path) path
  let _ ← ty "resulting_type"
  match kind with
  | "Deref" => pure .Deref
  | "Field" => return .Field (← natural "index") (← ty "field_type")
  | "Index" => return .Index (← natural "local")
  | "ConstantIndex" => return .ConstantIndex (← natural "offset") (← natural "min_length") (← boolean "from_end")
  | "Subslice" => return .Subslice (← natural "from") (← natural "to") (← boolean "from_end")
  | "Downcast" =>
    let value ← catalog.inspect (← catalog.field input "name" path) path
    let name ← if value == .null then pure none else some <$> value.getStr?
    return .Downcast name (← natural "variant_index")
  | "OpaqueCast" => return .OpaqueCast (← ty "cast_type")
  | "UnwrapUnsafeBinder" => return .UnwrapUnsafeBinder (← ty "inner_type")
  | "PhantomDeref" => pure .PhantomDeref
  | _ => throw s!"{path}: unsupported projection kind {kind}"

private def localBound : ProjectionElem → Nat
  | .Index id => id + 1
  | _ => 0

private def remember (table : SharedTable Nat) (id bound : Nat) : Except String (SharedTable Nat) := do
  let table := if table.size ≤ id then table ++ Array.replicate (id + 1 - table.size) none else table
  if index : id < table.size then return table.set id (some bound) index
  throw "projection bound slot absent"

private def projection (catalog : Catalog) (typeCount : Nat) (input : Json) (path : String) : Decode ProjectionId := do
  let id ← catalog.readCached (·.tables.projections) (fun state table => {state with tables := {state.tables with projections := table}})
    (fun input path => projectionValue catalog typeCount input path) input path
  let state ← get
  if let some (some _) := state.projectionLocals[id]? then return ⟨id⟩
  let value ← state.tables.projections.lookup id |>.mapError (fun id => s!"invalid projection {id}")
  let projectionLocals ← remember state.projectionLocals id (localBound value)
  set {state with projectionLocals}
  return ⟨id⟩

private def projections (catalog : Catalog) (typeCount : Nat) (input : Json) (path : String) : Decode ProjectionListId := do
  let id ← catalog.readCached (·.tables.projectionLists) (fun state table => {state with tables := {state.tables with projectionLists := table}})
    (fun input path => do
      let values ← catalog.array input path
      values.mapIdxM fun index value => projection catalog typeCount value s!"{path}[{index}]") input path
  let state ← get
  if let some (some _) := state.listLocals[id]? then return ⟨id⟩
  let values ← state.tables.projectionLists.lookup id |>.mapError (fun id => s!"invalid projection list {id}")
  let mut bound := 0
  for projection in values do
    let value ← state.projectionLocals.lookup projection.index |>.mapError (fun id => s!"projection local bound absent {id}")
    bound := max bound value
  let listLocals ← remember state.listLocals id bound
  set {state with listLocals}
  return ⟨id⟩

def place (catalog : Catalog) (typeCount : Nat) (input : Json) (path : String) : Decode PlaceId := do
  let id ← catalog.readCached (·.tables.places) (fun state table => {state with tables := {state.tables with places := table}})
    (fun input path => do
      catalog.requireSupported input path
      return {
      typeId := ← typeId catalog typeCount (← catalog.field input "type" path) path
      localId := ← catalog.natural (← catalog.field input "local" path) path
      projection := ← projections catalog typeCount (← catalog.field input "projection" path) path }) input path
  let state ← get
  if let some (some _) := state.placeLocals[id]? then return ⟨id⟩
  let value ← state.tables.places.lookup id |>.mapError (fun id => s!"invalid place {id}")
  let projectionBound ← state.listLocals.lookup value.projection.index |>.mapError (fun id => s!"projection list bound absent {id}")
  let placeLocals ← remember state.placeLocals id (max (value.localId + 1) projectionBound)
  set {state with placeLocals}
  return ⟨id⟩

def initial (slots : Nat) : State := MIRReader.initial slots ⟨#[], #[], #[]⟩

def validatePlace (state : State) (place : PlaceId) (locals : Nat) : Except String Unit := do
  let bound ← state.placeLocals.lookup place.index |>.mapError (fun id => s!"place bound absent {id}")
  unless bound ≤ locals do throw s!"place {place.index}: local index outside body of size {locals}"

end Miri.Input.Reader.PlaceReader
