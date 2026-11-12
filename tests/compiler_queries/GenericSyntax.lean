import Miri.Input.GenericSyntax

open Miri.Input GenericSubstitution

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def main : IO Unit := do
  let parameter := Term.parameter .type 0
  let policy : GenericSyntax.Policy := {parameters := #[.type]}
  let good := Term.node .type "raw_pointer" "mutable" (#[parameter] : Array Term)
  ensure ((GenericSyntax.validate policy 64 .type good).isOk) "valid raw pointer rejected"
  let malformed : Array Term := #[
    .node .type "imaginary" "" .nil,
    .node .type "function_pointer" "" (#[parameter] : Array Term),
    .node .type "tuple" "" (#[parameter,.node .type "imaginary" "" .nil] : Array Term),
    .definition .type "alias_unknown_rigidity" ⟨0,1⟩ (#[parameter] : Array Term),
    .node .type "array" "" (#[parameter,.atom .region "static" ""] : Array Term),
    .node .type "slice" "" (#[parameter,parameter] : Array Term),
    .node .type "raw_pointer" "unknown" (#[parameter] : Array Term),
    .parameter .type 1,
    .placeholder .type 1 0 .anonymous,
    .inference .type 0,
    .bound .type (.Bound 0) 0 .anonymous]
  for value in malformed do
    ensure (!(GenericSyntax.validate policy 64 .type value).isOk)
      "malformed or forbidden type syntax accepted"
  let header := "{\"abi_packed\":0,\"safe\":true,\"c_variadic\":false,\"splatted\":null}"
  let region := Term.bound .region (.Bound 0) 0 .anonymous
  let reference := Term.node .type "reference" "immutable"
    (#[region,.atom .type "uint" "u8"] : Array Term)
  let signature := Term.binder #[.region .anonymous]
    (.node .aggregate "signature" header (#[reference,reference] : Array Term))
  ensure ((GenericSyntax.validate {} 64 .signature signature).isOk)
    "owned higher-ranked region rejected"
  let escaping := Term.node .type "reference" "immutable"
    (#[region,.atom .type "uint" "u8"] : Array Term)
  ensure (!(GenericSyntax.validate {} 64 .type escaping).isOk) "escaping bound region accepted"
  let wrongIdentity := Term.binder #[.region .anonymous]
    (.node .aggregate "signature" header
      (#[.node .type "reference" "immutable"
        (#[.bound .region (.Bound 0) 0 (.namedForPrinting "wrong"),
            .atom .type "uint" "u8"] : Array Term),.atom .type "bool" ""] : Array Term))
  ensure (!(GenericSyntax.validate {} 64 .signature wrongIdentity).isOk)
    "bound variable identity mismatch accepted"
  ensure ((GenericSyntax.validate {inference := true} 64 .type (.inference .type 2)).isOk)
    "query-state inference syntax rejected"
  ensure (!(GenericSyntax.validate {inference := true} 64 .signature (.inference .aggregate 2)).isOk)
    "aggregate inference variable accepted as a signature"
  ensure (!(GenericSyntax.validate policy 0 .type good).isOk) "exhausted validation accepted"
  IO.println "PASS typed generic syntax, malformed closed subtrees, binder scopes and solver syntax policies"
