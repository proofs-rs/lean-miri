import Miri.Frontend.FoundationPhysicalRegistry

open Lean Miri Miri.Frontend.Foundation

private def expect (r : Except String α) : IO α :=
  match r with
  | .ok a => pure a
  | .error e => throw (IO.userError e)

private def check (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)

private def scalar (row : Input.Layout) : IO Input.ScalarLayout := do
  let some value := row.backendRepresentation >>= (·.scalar)
    | throw (IO.userError "pointer scalar absent")
  return value

def main (paths : List String) : IO Unit := do
  let target := ABI.RuntimeTargetDataLayout.default
  let byte := ConcreteType.primitive "uint" "u8"
  let raw := ConcreteType.pointer "raw_pointer_const" byte
  let mutable := ConcreteType.pointer "raw_pointer_mut" byte
  let reference := ConcreteType.pointer "reference_erased_const" byte
  let row ← expect (physicalLayoutOfRuntime target raw)
  let value ← scalar row
  check (value.primitive.kind == .pointer && value.primitive.addressSpace == some 0) "source address space"
  check (value.validRange == some (0, 2^64-1) && row.largestNiche.isNone) "raw full range"
  let splitTarget := { target with
    defaultAddressSpace := ⟨1⟩,
    addressSpaceInfo := #[(ABI.AddressSpace.ZERO, ⟨ABI.Size.ofBytes 4, ⟨2⟩, ABI.Size.ofBytes 4, false⟩)] }
  let split ← expect (physicalLayoutOfRuntime splitTarget raw)
  check (split.sizeBytes == some 4 && split.abiAlignBytes == some 4) "address-space-zero layout"
  let _ ← expect ((Input.RuntimeMetadata.layout splitTarget split).mapError toString)
  let refRow ← expect (physicalLayoutOfRuntime target reference)
  let refValue ← scalar refRow
  check (refValue.validRange == some (1, 2^64-1) && refRow.largestNiche.isSome) "reference nonnull range"
  check (row.randomizationSeed != refRow.randomizationSeed) "pointer seed distinction"
  for layout in #[row, refRow] do
    let _ ← expect ((Input.RuntimeMetadata.layout target layout).mapError toString)
  for kind in #["raw_pointer", "reference", "raw", "reference_bound_const"] do
    match physicalLayoutOfRuntime target (.pointer kind byte) with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError "ambiguous pointer accepted")
  match physicalLayoutOfRuntime target (.pointer "raw_pointer_const" (.tuple #[byte])) with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "unsupported pointee accepted")
  let [path] := paths | throw (IO.userError "usage: FoundationPointers FOUNDATION_JSON")
  let json ← IO.FS.readFile path
  let document ← expect (Json.parse json >>= decode)
  -- Synthetic source material exercises retention, not compiler correspondence.
  let byteRow := Json.mkObj [("shape", Json.mkObj [("kind", toJson "uint"), ("name", toJson "u8")])]
  let refRow := Json.mkObj [("shape", Json.mkObj [("kind", toJson "reference"),
    ("pointee", toJson (0 : Nat)), ("mutable", toJson true), ("region", toJson "static")])]
  let sourceDocument := {document with types := #[byteRow, refRow]}
  let resolved ← expect (typeExpr sourceDocument 1 >>= instantiate #[] #[])
  check (sameConcrete 20 resolved (.pointer "reference_static_mut" byte)) "source pointer identity lost"
  let (r, rawId) ← expect ((PhysicalTypeRegistry.start document).intern raw)
  let (r, mutId) ← expect (r.intern mutable)
  let (r, refId) ← expect (r.intern reference)
  let (r, staticId) ← expect (r.intern (.pointer "reference_static_const" byte))
  check (rawId != mutId && refId != staticId && r.types.size == 5) "mutability/region identity"
  let (node, _) ← expect (r.lookup mutId)
  match node.shape with
  | .rawPointer 0 .Mut => pure ()
  | _ => throw (IO.userError "raw pointer shape mismatch")
  let (node, _) ← expect (r.lookup staticId)
  match node.shape with
  | .reference 0 .Not .Static => pure ()
  | _ => throw (IO.userError "reference shape mismatch")
  let (r, nestedId) ← expect (r.intern (.pointer "raw_pointer_const" raw))
  let (node, _) ← expect (r.lookup nestedId)
  match node.shape with
  | .rawPointer child .Not => check (child == rawId) "nested child identity"
  | _ => throw (IO.userError "nested pointer shape mismatch")
  for id in [:r.types.size] do
    let _ ← expect (r.runtimeLayout id)
  IO.println "foundation pointers: exact identity, scalar ranges and physical conversion passed"
