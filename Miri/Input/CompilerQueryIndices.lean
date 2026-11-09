import Miri.Input.Model

namespace Miri.Input.CompilerQueryIndices
open Miri.ABI

structure Covariance where
  rows : Std.HashMap (Nat × Nat) (Array Catalog.CovarianceQuery) := {}

def covariance (queries : Array Catalog.CovarianceQuery) : Covariance := Id.run do
  let mut rows := {}
  for query in queries do
    let key := (query.sourceType, query.targetType)
    rows := rows.insert key ((rows.getD key #[]).push query)
  return ⟨rows⟩

def covarianceRows (index : Covariance) (source target : Nat) : Array Catalog.CovarianceQuery :=
  index.rows.getD (source, target) #[]

private def safetyKey : MIR.Safety → String
  | .Safe => "safe"
  | .Unsafe => "unsafe"

private def signatureKey (inputs : Array Nat) (output : Nat) (abi : ABI.ExternAbi)
    (safety : MIR.Safety) (cVariadic splatted : Bool) : String :=
  let encodedInputs := String.intercalate "," (inputs.toList.map toString)
  s!"{encodedInputs}|{output}|{reprStr abi}|{safetyKey safety}|{cVariadic}|{splatted}"

structure SignatureAbi where
  rows : Std.HashMap String (Array Catalog.HelperSignature) := {}

def signatureAbi (queries : Array Catalog.HelperSignature) : SignatureAbi := Id.run do
  let mut rows := {}
  for query in queries do
    let sig := query.signature
    let key := signatureKey sig.inputs sig.output sig.abi sig.safety sig.cVariadic query.splatted
    rows := rows.insert key ((rows.getD key #[]).push query)
  return ⟨rows⟩

def signatureAbiRows (index : SignatureAbi) (key : String) : Array Catalog.HelperSignature :=
  index.rows.getD key #[]

def signatureRequestKey (inputs : Array MIR.TyId) (output : MIR.TyId)
    (abi : ABI.ExternAbi) (safety : MIR.Safety) (cVariadic splatted : Bool) : String :=
  signatureKey inputs output abi safety cVariadic splatted

end Miri.Input.CompilerQueryIndices
