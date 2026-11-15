import Miri.Frontend.FoundationPrimitiveCatalog
import Miri.Frontend.FoundationAbi

open Lean Miri Miri.Frontend.Foundation

private def expect (r : Except String α) : IO α :=
  match r with | .ok a => pure a | .error e => throw (IO.userError e)
private def check (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: FoundationPrimitiveCatalog FOUNDATION_JSON")
  let text ← IO.FS.readFile path
  let document ← expect (Json.parse text >>= decode)
  let initial := PhysicalTypeRegistry.start document
  let (r, catalog) ← expect (physicalPrimitiveCatalog initial)
  check initial.types.isEmpty "input registry mutated"
  let (again, repeated) ← expect (physicalPrimitiveCatalog r)
  check (repeated == catalog && again.types.size == r.types.size) "catalog not canonical"
  for id in #[catalog.u8,catalog.u16,catalog.u32,catalog.u64,catalog.u128,
      catalog.i8,catalog.i16,catalog.i32,catalog.i64,catalog.i128,catalog.bool,
      catalog.pointerTagInteger,catalog.usize,catalog.isize,catalog.unit,
      catalog.unitPointerConst,catalog.unitPointerMut,catalog.immU8Pointer,
      catalog.immU8PointerPointer,catalog.typeNameResultType] do
    let _ ← expect (r.runtimeLayout id)
  check (catalog.pointerTagInteger == catalog.u64) "pointer tag integer identity"
  let (pointerNode, _) ← expect (r.lookup catalog.immU8PointerPointer)
  match pointerNode.shape with
  | .rawPointer inner .Not => check (inner == catalog.immU8Pointer) "nested primitive pointer"
  | _ => throw (IO.userError "nested primitive pointer shape")
  let (nameNode, nameLayout) ← expect (r.lookup catalog.typeNameResultType)
  match nameNode.shape with
  | .reference strId .Not .Erased =>
    let (strNode, strLayout) ← expect (r.lookup strId)
    check (strNode.shape.kind == .str && strLayout.sizeBytes == some 0) "str identity"
    check (strLayout.randomizationSeed == 0xc1325f37d127be22) "str seed"
    let some backend := strLayout.backendRepresentation | throw (IO.userError "str backend absent")
    check (backend.kind == .memory && backend.sized == some false) "str unsized memory"
  | _ => throw (IO.userError "type_name result identity")
  check (nameLayout.sizeBytes == some 16 && nameLayout.abiAlignBytes == some 8) "wide reference size"
  check (nameLayout.backendReprKind == some .scalarPair && nameLayout.randomizationSeed == 16) "wide reference backend seed"
  let some backend := nameLayout.backendRepresentation | throw (IO.userError "wide backend absent")
  let some first := backend.first | throw (IO.userError "wide data absent")
  let some second := backend.second | throw (IO.userError "wide metadata absent")
  check (first.validRange == some (1, 2^64-1) && second.validRange == some (0, 2^64-1)) "wide ranges"
  check (backend.secondOffsetBytes == some 8 && nameLayout.largestNiche.isSome) "wide offset niche"
  match r.intern (.array (.primitive "str" "") 2) with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "unsized array element accepted")
  match rustModeShape document.target "x86_64" false (.primitive "str" "") with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "unsized str incorrectly received call ABI")
  IO.println "foundation primitive catalog: canonical identities and str/wide reference conversion passed"
