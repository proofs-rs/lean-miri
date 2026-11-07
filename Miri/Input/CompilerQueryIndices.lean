import Miri.Input.RuntimeMetadata
import Miri.Input.CompilerExternAbi
import Miri.Input.CallResolution
import Miri.Input.Decoder
import Miri.Interpreter.FunctionCalls

/-! Preparation-time lookup indices for exact covariance and generated-call ABI
queries. The indices retain source row order and the first malformed global
row; consumers still decide query-specific matches and error precedence. -/
namespace Miri.Input.CompilerQueryIndices
open Lean Miri.ABI Miri.Interpreter

private def covarianceKey (source target : Nat) : String := s!"{source}:{target}"

structure CovarianceData where
  headerError : Option String := none
  rows : Std.HashMap String (Array (Nat × CovarianceQuery)) := {}

private def buildCovariance (queries : Except String (Array CovarianceQuery)) : CovarianceData := Id.run do
  let entries ← match queries with
    | .ok entries => pure entries
    | .error error => return {headerError := some error}
  let mut rows : Std.HashMap String (Array (Nat × CovarianceQuery)) := {}
  for (entry,index) in entries.toList.zipIdx do
    let key := covarianceKey entry.source entry.target
    rows := rows.insert key ((rows.getD key #[]).push (index,entry))
  return {rows}

structure Covariance (queries : Except String (Array CovarianceQuery)) where
  private mk ::
  data : CovarianceData
  exact : data = buildCovariance queries

def covariance (queries : Except String (Array CovarianceQuery)) : Covariance queries :=
  ⟨buildCovariance queries,rfl⟩

private def safetyKey : MIR.Safety → String
  | .Safe => "safe"
  | .Unsafe => "unsafe"

private def signatureKey (inputs : Array Nat) (output : Nat) (abi : ABI.ExternAbi)
    (safety : MIR.Safety) (cVariadic splatted : Bool) : String :=
  let encodedInputs := String.intercalate "," (inputs.toList.map toString)
  s!"{encodedInputs}|{output}|{reprStr abi}|{safetyKey safety}|{cVariadic}|{splatted}"

structure SignatureAbiRow where
  index : Nat
  record : SignatureAbiQuery
  abiId : Except String Nat
  parsedAbi : Except String (FnAbi MIR.TyId)

structure SignatureAbiData where
  headerError : Option String := none
  firstRowError : Option (Nat × String) := none
  rows : Std.HashMap String (Array SignatureAbiRow) := {}

private def buildSignatureAbi (runtime : RuntimeMetadata)
    (abiCache : Option (CallResolution.FunctionAbiCache runtime)) : SignatureAbiData := Id.run do
  let records ← match runtime.source.abiQueries.signatures with
    | .ok records => pure records
    | .error error => return {headerError := some error}
  let mut rows : Std.HashMap String (Array SignatureAbiRow) := {}
  for (source,index) in records.toList.zipIdx do
    let key := signatureKey source.inputs source.output source.externAbi source.safety source.cVariadic source.splatted
    let parsedAbi := source.abi.bind (fun id => CallResolution.functionAbiId runtime id abiCache)
    let row : SignatureAbiRow := ⟨index,source,source.abi,parsedAbi⟩
    rows := rows.insert key ((rows.getD key #[]).push row)
  return { rows }

structure SignatureAbi (runtime : RuntimeMetadata) where
  private mk ::
  abiCache : Option (CallResolution.FunctionAbiCache runtime)
  data : SignatureAbiData
  exact : data = buildSignatureAbi runtime abiCache

def signatureAbi (runtime : RuntimeMetadata)
    (abiCache : Option (CallResolution.FunctionAbiCache runtime) := none) : SignatureAbi runtime :=
  ⟨abiCache,buildSignatureAbi runtime abiCache,rfl⟩

def covarianceRows {queries : Except String (Array CovarianceQuery)} (index : Covariance queries) (source target : Nat) : Array (Nat × CovarianceQuery) :=
  index.data.rows.getD (covarianceKey source target) #[]

def signatureRows {runtime : RuntimeMetadata}
    (index : SignatureAbi runtime) (key : String) : Array (Nat × SignatureAbiQuery) :=
  (index.data.rows.getD key #[]).map fun row => (row.index,row.record)

/-- Internal query path selecting predecoded ABI outcomes while retaining each
source row's index and raw record for exact duplicate checks. -/
def signatureAbiRows {runtime : RuntimeMetadata}
    (index : SignatureAbi runtime) (key : String) : Array SignatureAbiRow :=
  index.data.rows.getD key #[]

def signatureRequestKey (inputs : Array MIR.TyId) (output : MIR.TyId)
    (abi : ABI.ExternAbi) (safety : MIR.Safety) (cVariadic splatted : Bool) : String :=
  signatureKey inputs output abi safety cVariadic splatted

end Miri.Input.CompilerQueryIndices
