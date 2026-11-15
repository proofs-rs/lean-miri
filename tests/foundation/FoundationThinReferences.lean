import Miri.Frontend.FoundationSignatureFnAbi
import Miri.Frontend.FoundationPrimitiveFacts

open Lean Miri Miri.Frontend.Foundation
private def expect (r : Except String α) : IO α :=
  match r with | .ok a => pure a | .error e => throw (IO.userError e)
private def check (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)
private def rejects (r : Except String α) : IO Unit :=
  match r with | .error _ => pure () | .ok _ => throw (IO.userError "unsupported reference ABI accepted")

def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "usage: FoundationThinReferences BYTES_FOUNDATION_JSON")
  let text ← IO.FS.readFile path
  let d ← expect (Json.parse text >>= decode)
  let some sourceBody := d.bodies[0]? | throw (IO.userError "source body missing")
  let definition ← expect (sourceBody.getObjValAs? Nat "definition")
  let localTypes ← expect ((← expect (sourceBody.getObjValAs? (Array Nat) "locals")).mapM fun id => do
    eraseRegions (← instantiate #[] #[] (← typeExpr d id)))
  let signature ← expect (functionHeaderSource d definition >>= fun header => header.getObjVal? "signature")
  let output ← expect (signature.getObjValAs? Nat "output")
  let sourceType ← expect (typeExpr d output >>= instantiate #[] #[])
  let array := ConcreteType.array (.primitive "uint" "u8") 4
  let static := ConcreteType.pointer "reference_static_const" array
  let erased := ConcreteType.pointer "reference_erased_const" array
  check (sameConcrete 64 sourceType static) "source static region lost"
  check (sameConcrete 64 (← expect (eraseRegions sourceType)) erased) "pure source erasure"
  let some localType := localTypes[0]? | throw (IO.userError "return local missing")
  check (sameConcrete 64 localType erased) "executable local not canonical erased"
  let (r, abi) ← expect (rustFunctionAbiOfSourceSignature d definition #[])
  check (abi.arguments.isEmpty && abi.returnValue.mode.kind == .direct) "thin return mode"
  let some attrs := abi.returnValue.mode.attributes[0]? | throw (IO.userError "return attributes missing")
  check (attrs.regularBits == 144 && attrs.pointeeSizeBytes == 0 && attrs.pointeeAlignBytes.isNone)
    "OptLevel::No reference return attributes"
  let r ← expect r.withPrimitiveFacts
  let (node, _) ← expect (r.lookup abi.returnValue.typeId)
  let .reference pointee .Not .Erased := node.shape | throw (IO.userError "ABI type not erased shared reference")
  let some facts := node.compilerFacts | throw (IO.userError "reference facts missing")
  check (facts.booleanQueries.contains ("has_erasable_regions", false) &&
    facts.typeQueries.contains ("builtin_deref_implicit", some pointee) &&
    facts.typeQueries.contains ("builtin_deref_explicit", some pointee)) "reference compiler leaves"
  let (s, staticId) ← expect ((PhysicalTypeRegistry.start d).intern static)
  let s ← expect s.withPrimitiveFacts
  let (node, _) ← expect (s.lookup staticId)
  let some facts := node.compilerFacts | throw (IO.userError "static reference facts missing")
  check (facts.booleanQueries.contains ("has_erasable_regions", true)) "static free-region flag missing"
  let some (_, some normalized) := facts.typeQueries.find? (·.1 == "normalized")
    | throw (IO.userError "normalized type missing")
  check (facts.typeQueries.contains ("metadata_tail", some normalized)) "metadata tail failed to normalize regions"
  check (normalized != staticId) "static normalized identity conflated"
  let some normalizedEntry := s.registry.entries[normalized]? | throw (IO.userError "normalized row missing")
  check (sameConcrete 64 normalizedEntry.type erased) "normalization failed to erase regions"
  rejects (rustPassMode d.target "x86_64" true erased)
  rejects (rustPassMode d.target "x86_64" true erased (some "Aggressive"))
  let argument ← expect (rustPassMode d.target "x86_64" false erased (some "No"))
  check (argument.kind == .direct && argument.attributes == abi.returnValue.mode.attributes) "optNo shared argument attributes"
  rejects (rustPassMode d.target "x86_64" false erased (some "Aggressive"))
  rejects (rustPassMode d.target "x86_64" true (.pointer "reference_erased_mut" array) (some "No"))
  let some sourceRow := d.types[output]? | throw (IO.userError "source reference row absent")
  let shape ← expect (sourceRow.getObjVal? "shape")
  let mutated := sourceRow.setObjVal! "shape" (shape.setObjVal! "mutable" (toJson true))
  rejects (rustFunctionAbiOfSourceSignature {d with types := d.types.set! output mutated} definition #[])
  IO.println "thin shared references: pure erasure, exact optNo return ABI and compiler leaves passed"
