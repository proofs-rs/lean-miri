import Miri.Input.BinderRegions
open Miri.Input Miri.Input.GenericSubstitution
private def expectError (value : Except String α) : IO Unit := do
  if value.isOk then throw (IO.userError "malformed local binder accepted")
def main : IO Unit := do
  let missing : Term := .binder #[.region .anonymous] (.bound .region (.Bound 0) 1 .anonymous)
  expectError (BinderRegions.eraseAndAnonymizeOpen 128 missing)
  let mismatch : Term := .binder #[.region .closureEnvironment] (.bound .region (.Bound 0) 0 .anonymous)
  expectError (BinderRegions.eraseAndAnonymizeOpen 128 mismatch)
  let escaped : Term := .binder #[.region .anonymous] (.bound .region (.Bound 1) 3 .closureEnvironment)
  let .ok result := BinderRegions.eraseAndAnonymizeOpen 128 escaped
    | throw (IO.userError "open escaping source rejected")
  unless result == .binder #[] (.bound .region (.Bound 1) 3 .closureEnvironment) do
    throw (IO.userError "escaping source was incorrectly anonymized")
  expectError (BinderRegions.eraseAndAnonymize 128 escaped)
  IO.println "PASS missing local owner and identity mismatch reject; escaping identity retained only in open hash normalization"
