import Miri.Input.Reader.Layout

namespace Miri.Input.Reader.AbiReader
open Lean Miri.MIR DecoderValues

structure State where
  typeCount : Nat
  layouts : SharedTable Layout
  abis : AbiTables
abbrev Decode := ReaderT Catalog (StateT State (Except String))

private def field (j : Json) (key path : String) : Decode Json := fun catalog => do
  catalog.inspect (← catalog.field j key path) (joinPath path key)

private def optionalField (j : Json) (key : String) : Decode (Option Json) := fun catalog => do
  (← catalog.optionalField j key "layout").mapM (fun value => catalog.inspect value s!"layout.{key}")

private def optionalJson (j : Json) (key : String) : Decode (Option Json) := do
  return (← optionalField j key).filter (· != .null)

private def fieldNat (j : Json) (key path : String) : Decode Nat := do
  (← field j key path).getNat?
private def fieldString (j : Json) (key path : String) : Decode String := do
  (← field j key path).getStr?
private def fieldBool (j : Json) (key path : String) : Decode Bool := do
  (← field j key path).getBool?
private def optionalNat (j : Json) (key path : String) : Decode (Option Nat) := do
  match ← optionalJson j key with
  | none => return none
  | some value => return some (← value.getNat?.mapError (fun error => s!"{joinPath path key}: {error}"))
private def optionalString (j : Json) (key path : String) : Decode (Option String) := do
  match ← optionalJson j key with
  | none => return none
  | some value => return some (← value.getStr?.mapError (fun error => s!"{joinPath path key}: {error}"))
private def jsonArray (j : Json) (path : String) : Decode (Array Json) := fun catalog =>
  catalog.array j path
private def natArray (j : Json) (path : String) : Decode (Array Nat) := fun catalog => do
  (← catalog.array j path).mapM (fun value => catalog.natural value path)
private def parseU128Natural (j : Json) (path : String) : Decode Nat := fun catalog => do
  DecoderValues.parseU128Natural (← catalog.inspect j path) path

def parseAbiTag (j : Json) (path : String) : Decode AbiTag := do
  match j with
  | .str tag => return ⟨.supported, tag⟩
  | .obj _ =>
    let tag ← match ← optionalField j "kind" with
      | some value => value.getStr? |>.mapError fun e => s!"{joinPath path "kind"}: expected string enum tag ({e})"
      | none => match ← optionalField j "variant" with
        | some value => value.getStr? |>.mapError fun e => s!"{joinPath path "variant"}: expected string enum tag ({e})"
        | none => throw s!"{path}: enum object is missing its kind tag"
    let status ← match ← optionalField j "status" with
      | none => pure .supported
      | some value => parseStatus <$> (value.getStr? |>.mapError fun e => s!"{joinPath path "status"}: expected string ({e})")
    return ⟨status, tag⟩
  | _ => throw s!"{path}: expected enum tag string or tagged object"

def parseAbiAttributes (j : Json) (path : String) : Decode AbiAttributes := do
  return {
    noAlias := ← fieldBool j "no_alias" path
    noFree := ← fieldBool j "no_free" path
    noUndef := ← fieldBool j "no_undef" path
    nonNull := ← fieldBool j "non_null" path
    readOnly := ← fieldBool j "read_only" path
    writable := ← fieldBool j "writable" path
    inRegister := ← fieldBool j "in_register" path
    regularBits := ← fieldNat j "regular_bits" path
    pointeeSizeBytes := ← fieldNat j "pointee_size_bytes" path
    pointeeAlignBytes := ← optionalNat j "pointee_align_bytes" path
    argExtension := ← parseAbiTag (← field j "arg_extension" path) (joinPath path "arg_extension")
    captures := ← parseAbiTag (← field j "captures" path) (joinPath path "captures")
  }

def parseCanonicalAbi (j : Json) (path : String) : Decode CanonicalAbi := do
  let kindNode ← parseAbiTag j path
  return {
    status := kindNode.status
    kind := canonicalAbiKind kindNode.tag
    armCall := (← optionalString j "arm_call" path).map armCallKind
    interruptKind := (← optionalString j "interrupt_kind" path).map interruptCallKind
    x86Call := (← optionalString j "x86_call" path).map x86CallKind
  }

def parseAbiHintElement (j : Json) (path : String) : Decode AbiHintElement := do
  let tag ← parseAbiTag j path
  let kind ← match tag.tag with
  | "integer" =>
    let kind ← fieldString j "integer_kind" path
    pure (AbiHintKind.integer (integerTypeTag kind) (← fieldBool j "signed" path))
  | "float" => pure (.float (floatTypeTag (← fieldString j "float_kind" path)))
  | "pointer" => pure (.pointer (← fieldNat j "address_space" path))
  | other => pure (.unsupported other)
  return ⟨tag.status, kind⟩

def parseAbiRegister (j : Json) (path : String) : Decode AbiRegister := do
  let kindNode ← field j "kind" path
  let kindTag ← fieldString kindNode "kind" (joinPath path "kind")
  let hintElement ← match ← optionalJson kindNode "hint_element" with
    | none => pure none
    | some value => pure (some (← parseAbiHintElement value (joinPath path "kind.hint_element")))
  return {
    kind := abiRegisterKind kindTag
    sizeBits := ← fieldNat j "size_bits" path
    hintElement := hintElement
  }

def parseAbiCastTarget (j : Json) (path : String) : Decode AbiCastTarget := do
  let prefixJson ← jsonArray (← field j "prefix_registers" path) (joinPath path "prefix_registers")
  let mut prefixRegisters := #[]
  for (register, index) in prefixJson.toList.zipIdx do
    prefixRegisters := prefixRegisters.push (← parseAbiRegister register s!"{joinPath path "prefix_registers"}[{index}]")
  return {
    prefixRegisters := prefixRegisters
    restOffsetBytes := ← optionalNat j "rest_offset_bytes" path
    restRegister := ← parseAbiRegister (← field j "rest_register" path) (joinPath path "rest_register")
    restTotalBytes := ← fieldNat j "rest_total_bytes" path
    restIsConsecutive := ← fieldBool j "rest_is_consecutive" path
    attributes := ← parseAbiAttributes (← field j "attributes" path) (joinPath path "attributes")
  }

def parseAbiPassMode (j : Json) (path : String) : Decode AbiPassMode := do
  let tag ← fieldString j "kind" path
  let mut attributes := #[]
  for key in ["attributes", "first", "second", "metadata_attributes"] do
    if let some attr ← optionalJson j key then
      if key == "attributes" || key == "metadata_attributes" then
        attributes := attributes.push (← parseAbiAttributes attr (joinPath path key))
      else if key == "first" || key == "second" then
        attributes := attributes.push (← parseAbiAttributes attr (joinPath path key))
  let castTarget ← match ← optionalJson j "target" with
    | none => pure none
    | some value => pure (some (← parseAbiCastTarget value (joinPath path "target")))
  let indirectMode ← match ← optionalJson j "mode" with
    | none => pure none
    | some value => pure (some (← parseAbiTag value (joinPath path "mode")))
  let padI32Count ← optionalNat j "pad_i32_count" path
  let addressSpace ← optionalNat j "address_space" path
  let kind := passModeKind tag
  match kind with
  | .cast => if castTarget.isNone || padI32Count.isNone then throw s!"{path}: Cast pass mode is missing target/padding data"
  | .indirect => if indirectMode.isNone then throw s!"{path}: Indirect pass mode is missing its mode tag"
  | .direct | .pair | .indirectUnsized | .ignore | .unknown _ => pure ()
  return {
    kind := kind
    attributes := attributes
    castTarget := castTarget
    padI32Count := padI32Count
    addressSpace := addressSpace
    indirectMode := indirectMode
  }

private def argument (input : Json) (path : String) : Decode Nat := fun catalog =>
  catalog.readCached (·.abis.arguments) (fun state table => {state with abis := {state.abis with arguments := table}})
    (fun input path => do
      let type ← catalog.field input "type" path
      let typeId ← catalog.natural (← catalog.field type "type_id" path) s!"{path}.type"
      unless typeId < (← get).typeCount do throw s!"{path}: invalid argument type ID {typeId}"
      let layoutId ← match ← catalog.optionalField input "layout" path with
        | none | some .null => pure none
        | some raw =>
          let state ← get
          let (id, table) ← catalog.readLayout state.layouts raw s!"{path}.layout"
          set {state with layouts := table}
          pure (some id)
      return {
        typeId := typeId
        layoutId := layoutId
        mode := ← parseAbiPassMode (← catalog.field input "mode" path) s!"{path}.mode" catalog }) input path

private def argumentList (input : Json) (path : String) : Decode Nat := fun catalog =>
  catalog.readCached (·.abis.argumentLists) (fun state table => {state with abis := {state.abis with argumentLists := table}})
    (fun input path => do
      let raw ← catalog.array input path
      let mut result := #[]
      for (value, index) in raw.toList.zipIdx do
        result := result.push (← argument value s!"{path}[{index}]" catalog)
      return result) input path

private def functionValue (input : Json) (path : String) : Decode FunctionAbiData := fun catalog => do
  return {
    arguments := ← argumentList (← catalog.field input "arguments" path) s!"{path}.arguments" catalog
    returnValue := ← argument (← catalog.field input "return" path) s!"{path}.return" catalog
    callingConvention := ← parseCanonicalAbi
      (← catalog.inspect (← catalog.field input "calling_convention" path) s!"{path}.calling_convention")
      s!"{path}.calling_convention" catalog
    canUnwind := ← catalog.boolean (← catalog.field input "can_unwind" path) s!"{path}.can_unwind"
    cVariadic := ← catalog.boolean (← catalog.field input "c_variadic" path) s!"{path}.c_variadic"
    fixedCount := ← catalog.natural (← catalog.field input "fixed_count" path) s!"{path}.fixed_count" }

private def candidate (input : Json) : Bool :=
  ["arguments", "return", "calling_convention", "can_unwind", "c_variadic", "fixed_count"].all
    (fun key => (input.getObjVal? key).isOk)

private def parse (catalog : Catalog) : StateT State (Except String) Unit := do
  for bound : index in [:catalog.nodes.size] do
    let raw := catalog.nodes[index]
    unless candidate raw do continue
    let outcome ← try pure (.ok (← functionValue raw s!"$.shared_payloads.nodes[{index}]" catalog))
      catch error => pure (.error error)
    let state ← get
    if valid : index < state.abis.functions.size then
      set {state with abis := {state.abis with functions := state.abis.functions.set index (some outcome) valid}}
    else throw "ABI table not initialized"

end Miri.Input.Reader.AbiReader

namespace Miri.Input.Reader
open Lean Miri.MIR

def Catalog.readAbis (catalog : Catalog) (layouts : SharedTable Layout) :
    Except String (SharedTable Layout × AbiTables) := do
  let empty := fun {α : Type} => (Array.replicate catalog.nodes.size none : SharedTable α)
  let typeCount := (← catalog.array (← catalog.field catalog.root "types" "$") "$.types").size
  let initial : AbiReader.State := {typeCount, layouts, abis := {arguments := empty, argumentLists := empty, functions := empty}}
  let (_, state) ← (AbiReader.parse catalog).run initial
  return (state.layouts, state.abis)

end Miri.Input.Reader
