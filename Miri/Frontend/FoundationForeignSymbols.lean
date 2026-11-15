import Miri.Input.Model.Catalogs

/-! Target/linkage inputs and the pinned allocator-shim construction from
rustc_codegen_ssa::base::allocator_shim_contents. Foreign export selection and
static allocation evidence are deliberately absent and remain fail closed. -/
namespace Miri.Frontend.Foundation
open Lean

private def selector (j : Json) (key : String) : Except String (Option String) := do
  let result ← j.getObjValAs? (Option String) key
  if let some kind := result then
    unless kind == "global" || kind == "default" do throw "unknown allocator linkage selector"
  return result

/-- Fixed ASCII subset of rustc v0::push_ident used by allocator symbols. -/
private def internalSymbol (namespacePrefix name : String) : String :=
  namespacePrefix ++ toString name.utf8ByteSize ++ "_" ++ name

/-- Compute fixed allocator symbol identities and dispatch from finite session
linkage selectors. Optional foreign lookup evidence stays absent. -/
def foreignSymbols (document : Json) : Except String Input.Catalog.ForeignSymbols := do
  let source ← document.getObjVal? "foreign_symbol_material"
  let namespacePrefix ← source.getObjValAs? String "internal_symbol_namespace"
  unless namespacePrefix.startsWith "_RNvC" && namespacePrefix.endsWith "7___rustc" do
    throw "unexpected compiler internal-symbol namespace"
  let allocator ← selector source "allocator_kind"
  let handler ← selector source "alloc_error_handler_kind"
  if allocator.isSome && handler.isNone then throw "allocator linkage lacks error handler selection"
  let mut shims := #[]
  if allocator == some "default" then
    for method in #["alloc", "dealloc", "realloc", "alloc_zeroed"] do
      shims := shims.push (internalSymbol namespacePrefix ("__rust_" ++ method), .special method)
  if allocator.isSome && handler == some "default" then
    shims := shims.push (internalSymbol namespacePrefix "__rust_alloc_error_handler",
      .redirect (internalSymbol namespacePrefix "__rdl_alloc_error_handler"))
  return {
    os := ← source.getObjValAs? String "os"
    env := ← source.getObjValAs? String "env"
    binaryFormat := ← source.getObjValAs? String "binary_format"
    families := ← source.getObjValAs? (Array String) "families"
    noAllocShimSymbol := internalSymbol namespacePrefix "__rust_no_alloc_shim_is_unstable_v2"
    allocatorShims := shims
    exportedCandidates := none, selectedForeignFallbacks := none
    externDeclarations := none, selectedExports := none }

end Miri.Frontend.Foundation
