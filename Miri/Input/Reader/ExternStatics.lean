import Miri.Input.Reader.Regions

namespace Miri.Input.Reader.ExternStaticReader
open Lean Miri.ABI Miri.Interpreter
abbrev Decode := MIRReader.Decode

private def statusResult (catalog : Catalog) (query : Json) (path : String) : Except String Json := do
  match ← catalog.string (← catalog.field query "status" path) path with
  | "supported" => catalog.field query "value" path
  | "unsupported" =>
    throw ((do catalog.string (← catalog.field query "reason" path) path).toOption.getD
      "compiler extern-static query unavailable")
  | status => throw s!"unknown compiler extern-static status `{status}`"

private def size (n : Nat) : Except String Size := do
  unless n < 2^64 do throw "size: u64 overflow"
  return Size.ofBytes (UInt64.ofNat n)
private def alignment (n : Nat) : Except String Align := do
  unless n != 0 do throw "alignment: zero alignment"
  unless n < 2^64 do throw "alignment: u64 overflow"
  Align.fromBytes (UInt64.ofNat n) |>.mapError toString

private def linkage (catalog : Catalog) (raw : Json) (path : String) : Except String ExternStatic.ImportLinkage := do
  let kind ← catalog.string (← catalog.field raw "kind" path) path
  match kind with
  | "none" => pure .none
  | "external_weak" => pure .externalWeak
  | "other" => pure .other
  | _ => throw s!"unknown compiler extern-static import linkage `{kind}`"

private def declaration (catalog : Catalog) (typeCount : Nat) (raw : Json) (path : String) : Decode ExternStaticDeclarationData := do
  let field := fun key => catalog.field raw key path
  let text : String → Except String String := fun key => do catalog.string (← field key) path
  let boolean : String → Except String Bool := fun key => do catalog.boolean (← field key) path
  let id ← RegionReader.definition catalog (← field "definition") path
  let result : Except String (String × Size × Align × ExternStatic.ImportLinkage × Bool) := do
    unless (← text "status") == "supported" do
      throw ((text "reason").toOption.getD "compiler extern-static declaration query unavailable")
    unless (← text "typing_env") == "fully_monomorphized" do
      throw "extern-static declaration has a non-canonical typing environment"
    let ty ← catalog.natural (← catalog.field (← field "type") "type_id" path) path
    unless ty < typeCount do throw "extern-static declaration references absent compiler type"
    let layout ← field "layout"
    let size ← size (← catalog.natural (← catalog.field layout "size_bytes" path) path)
    let align ← alignment (← catalog.natural (← catalog.field layout "abi_align_bytes" path) path)
    let mutable ← boolean "decl_is_mut"
    let definitionMutability ← text "definition_mutability"
    let typeIsFreeze ← boolean "type_is_freeze"
    let sourceMutability ← match definitionMutability with
      | "mutable" => pure true
      | "immutable" => pure (!typeIsFreeze)
      | other => throw s!"unknown source static mutability `{other}`"
    unless mutable == sourceMutability do
      throw "extern-static declaration mutability disagrees with definition mutability and Freeze query"
    return (← text "symbol",size,align,← linkage catalog (← field "import_linkage") path,mutable)
  match result with
  | .ok (symbol,size,align,linkage,mutable) => return ⟨id,symbol,size,align,linkage,mutable,.ok ()⟩
  | .error reason => return ⟨id,(text "symbol").toOption.getD "",.ZERO,.ONE,.other,false,.error reason⟩

private def winner (catalog : Catalog) (typeCount allocationCount : Nat) (raw : Json) (path : String) : Decode ExternStaticWinnerData := do
  let field := fun key => catalog.field raw key path
  let text : String → Except String String := fun key => do catalog.string (← field key) path
  let status ← text "status"
  if status == "ambiguous" then
    return ⟨none,"ambiguous",none,status,(text "reason").toOption.getD "ambiguous exported symbol"⟩
  if status != "supported" then
    return ⟨none,"unknown",none,status,(text "reason").toOption.getD "exported symbol query unavailable"⟩
  let definition ← RegionReader.definition catalog (← field "definition") path
  let kind ← text "kind"
  if kind != "static" then return ⟨some definition,kind,none,status,""⟩
  let embedded ← declaration catalog typeCount (← field "declaration") path
  unless embedded.definition == definition do throw "selected exported static declaration DefId differs from its winner"
  unless embedded.symbol == (← text "symbol") do throw "selected exported static declaration symbol differs from its winner"
  if let .error reason := embedded.result then return ⟨some definition,kind,none,"unsupported",reason⟩
  let allocation : Except String Nat := do
    let allocation ← statusResult catalog (← field "allocation") path
    let id ← catalog.natural (← catalog.field allocation "allocation_id" path) path
    unless id < allocationCount do throw "selected exported static allocation is absent from compiler graph"
    return id
  match allocation with
  | .ok id => return ⟨some definition,kind,some id,status,""⟩
  | .error reason => return ⟨some definition,kind,none,"unsupported",reason⟩

private def queries (catalog : Catalog) (typeCount allocationCount : Nat) : Decode ExternStaticsData := do
  let path := "$.compiler_runtime_queries.foreign_symbols"
  let foreign := do catalog.field (← catalog.field catalog.root "compiler_runtime_queries" "$") "foreign_symbols" path
  let source : Except String Json := do
    let source ← statusResult catalog (← catalog.field (← foreign) "extern_statics" path) path
    unless (← catalog.string (← catalog.field source "typing_env" path) path) == "fully_monomorphized" do
      throw "extern-static table has a non-canonical typing environment"
    return source
  let target : Except String CompilerTargetFactsData := do
    let target ← statusResult catalog (← catalog.field (← foreign) "target" path) path
    let text := fun key => do catalog.string (← catalog.field target key path) path
    let os ← text "os"
    let env ← text "env"
    let binaryFormat ← text "binary_format"
    let families ← catalog.array (← catalog.field target "families" path) path
    let mut parsed := #[]
    for family in families do
      let family ← catalog.string family path
      if parsed.contains family then throw "duplicate rustc target family"
      parsed := parsed.push family
    return ⟨os,env,binaryFormat,parsed⟩
  match source with
  | .error reason => return ⟨.error reason,target,#[],#[]⟩
  | .ok source =>
    let mut declarations := #[]
    let mut selected := #[]
    for raw in ← catalog.array (← catalog.field source "declarations" path) path do
      let entry ← declaration catalog typeCount raw path
      if let some old := declarations.find? (·.definition == entry.definition) then
        unless old == entry do throw "conflicting exact extern-static declaration queries"
      else declarations := declarations.push entry
    for raw in ← catalog.array (← catalog.field source "selected_exported" path) path do
      let symbol ← catalog.string (← catalog.field raw "symbol" path) path
      if selected.any (·.symbol == symbol) then throw "duplicate selected exported symbol row"
      selected := selected.push (⟨symbol,← winner catalog typeCount allocationCount raw path⟩ : ExternStaticSelectedData)
    return ⟨.ok (),target,declarations,selected⟩

def read (catalog : Catalog) (typeCount allocationCount : Nat) : Decode (Except String ExternStaticsData) := do
  let original ← get
  match (queries catalog typeCount allocationCount).run original with
  | .error reason => pure (.error reason)
  | .ok (value,next) => set next; pure (.ok value)

end Miri.Input.Reader.ExternStaticReader
