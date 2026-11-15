import Miri.Input.SourceAbi
import Miri.Input.SourceCompilerWorld
import Miri.Input.AbiConversion

/-! ABI availability is independent of executable MIR. These operations always
read the current canonical World; a derived ABI appends no body and cannot turn
identityOnly into instanceMir. This is a demand cache, not producer evidence. -/
namespace Miri.Input.SourceCompilerWorld
open Miri.Interpreter

private def abiRequest (world : World) (callee : CallInstance) (extra : Array MIR.TyId) : Except String Unit := do
  let value ← node world callee
  if let .LlvmIntrinsic _ := value.instanceKind then throw "source LLVM intrinsic has no ordinary instance ABI"
  for id in extra do
    let some type := world.canonical.types[id]? | throw "source instance ABI extra type absent"
    unless type.id == id do throw "source instance ABI extra type identity mismatch"

/-- Read the full-instance/ordered-extra-type key from the current World. A
missing record is a demand for source derivation, never a default ABI. -/
def existingInstanceAbi (world : World) (callee : CallInstance) (extra : Array MIR.TyId) :
    Except String (Option Nat) := do
  abiRequest world callee extra
  let mut found : Option Nat := none
  let records := if world.canonical.sourceMaterial.isSome then world.derivedInstanceAbis else world.canonical.queries.instanceAbis
  for record in records do
    if record.instanceId == callee && record.extraArgumentTypes == extra then
      unless record.abiId < world.canonical.functionAbis.size do throw "source instance ABI record absent"
      if let some previous := found then
        unless previous == record.abiId do throw "conflicting source full-instance ABI records"
      found := some record.abiId
  if world.canonical.sourceMaterial.isSome then
    if let some derived := found then
      for record in world.canonical.queries.instanceAbis do
        if record.instanceId == callee && record.extraArgumentTypes == extra then
          unless record.abiId == derived do throw "source derived/canonical ABI identity conflict"
  return found

private def checkAbi (world : World) (abi : FunctionAbi) : Except String Unit := do
  LocalValidation.validateFunctionAbi abi "source derived ABI"
  unless abi.fixedCount ≤ abi.arguments.size do throw "source ABI fixed argument count invalid"
  for argument in abi.arguments.push abi.returnValue do
    let some type := world.canonical.types[argument.typeId]? | throw "source derived ABI type absent"
    unless type.id == argument.typeId do throw "source derived ABI type identity mismatch"
    unless argument.layoutId < world.canonical.layouts.size do throw "source derived ABI physical layout absent"

/-- Record one source-derived ABI after its type/layout pools have been
extended. Existing full-instance answers must agree. All instance identities and
body capabilities are retained exactly, including identityOnly. -/
def attachInstanceAbi (world : World) (callee : CallInstance) (extra : Array MIR.TyId)
    (abi : FunctionAbi) : Except String (World × Nat) := do
  abiRequest world callee extra
  checkAbi world abi
  if let some existing ← existingInstanceAbi world callee extra then
    let some previous := world.canonical.functionAbis[existing]? | throw "source existing ABI absent"
    unless previous == abi do throw "source demanded ABI conflicts with existing canonical answer"
    return (world,existing)
  -- Imported source-mode rows are not demand answers, but contradictory
  -- canonical data must still reject instead of being silently overwritten.
  let mut imported : Option Nat := none
  for record in world.canonical.queries.instanceAbis do
    if record.instanceId == callee && record.extraArgumentTypes == extra then
      if let some previous := imported then
        unless previous == record.abiId do throw "conflicting canonical instance ABI rows"
      let some actual := world.canonical.functionAbis[record.abiId]? | throw "canonical ABI row absent"
      unless actual == abi do throw "derived source ABI conflicts with canonical ABI data"
      imported := some record.abiId
  let existing := imported.orElse (fun _ => world.canonical.functionAbis.findIdx? (· == abi))
  let index := existing.getD world.canonical.functionAbis.size
  let abis := if existing.isSome then world.canonical.functionAbis else world.canonical.functionAbis.push abi
  let record := Catalog.InstanceAbi.mk callee extra index
  let queries := if imported.isSome then world.canonical.queries else
    {world.canonical.queries with instanceAbis := world.canonical.queries.instanceAbis.push record}
  let derived := if world.canonical.sourceMaterial.isSome then world.derivedInstanceAbis.push record else world.derivedInstanceAbis
  return ({world with canonical := {world.canonical with functionAbis := abis,queries},derivedInstanceAbis := derived},index)

/-- Interpret ABI type/layout IDs against the same updated canonical pools
that supplied the record. The original World snapshot is never consulted. -/
def instanceAbi (world : World) (callee : CallInstance) (extra : Array MIR.TyId) :
    Except String (ABI.FnAbi MIR.TyId) := do
  let some index ← existingInstanceAbi world callee extra | throw "source instance ABI has not been derived"
  let runtime ← (RuntimeMetadata.ofDocument world.canonical).mapError toString
  AbiConversion.functionAbiId runtime index

/-- Current original function signature. Existing exact normalized evidence is
retained; newly source-created native function shapes carry their own signature.
Unknown aliases without source normalization evidence remain unavailable. -/
def functionSignature (world : World) (typeId : MIR.TyId) : Except String (Nat × ABI.ExternAbi) := do
  let some node := world.canonical.types[typeId]? | throw "World function signature type absent"
  unless node.id == typeId do throw "World function signature type identity mismatch"
  match node.shape with
  | .functionDefinition _ _ signature _ | .functionPointer signature _ =>
    return (signature.inputs.size,signature.abi)
  | _ => throw "World original function signature unavailable"

/-- Read a pointer ABI against the current canonical pools, never a saved
Prepared.functions view. No ordinary Item is substituted for a runtime target. -/
def functionPointerAbi (world : World) (typeId : MIR.TyId) (extra : Array MIR.TyId) :
    Except String (ABI.FnAbi MIR.TyId) := do
  unless world.canonical.sourceMaterial.isNone do throw "typed source function-pointer ABI derivation unavailable"
  let some node := world.canonical.types[typeId]? | throw "World function pointer type absent"
  unless node.id == typeId do throw "World function pointer type identity mismatch"
  let functions := world.canonical.queries.functionFacts.types.filter (·.typeId == typeId)
  unless functions.size ≤ 1 do throw "World pointer function evidence ambiguous"
  if let some function := functions[0]? then
    unless function.instanceId.isNone do throw "World pointer ABI requested for function definition"
  else
    match node.shape with
    | .functionPointer .. => pure ()
    | _ => throw "World pointer ABI type kind unavailable"
  let rows := world.canonical.queries.functionFacts.pointerAbis.filter fun row => row.typeId == typeId && row.extraArgumentTypes == extra
  unless rows.size == 1 do throw "World exact pointer ABI unavailable or ambiguous"
  let some row := rows[0]? | throw "World pointer ABI absent"
  for type in extra do
    let some node := world.canonical.types[type]? | throw "World pointer ABI extra type absent"
    unless node.id == type do throw "World pointer ABI extra type identity mismatch"
  let runtime ← (RuntimeMetadata.ofDocument world.canonical).mapError toString
  AbiConversion.functionAbiId runtime row.abiId

private def query (value : Except String A) : EStateM StepError S A :=
  match value with | .ok value => pure value | .error reason => throw (.unsupported reason)

/-- Signature consumer over the current state World. -/
def demandFunctionSignature (access : Access S) (typeId : MIR.TyId) :
    EStateM StepError S (Nat × ABI.ExternAbi) := do
  let some world := access.get (← get) | throw (.unsupported "source compiler World is unavailable")
  query (functionSignature world typeId)

/-- FnPtr consumer over the current state World. Missing derived ABI remains
Unsupported; no saved compiler snapshot supplies an accidental stale answer. -/
def demandFunctionPointerAbi (access : Access S) (typeId : MIR.TyId) (extra : Array MIR.TyId) :
    EStateM StepError S (ABI.FnAbi MIR.TyId) := do
  let some world := access.get (← get) | throw (.unsupported "source compiler World is unavailable")
  query (functionPointerAbi world typeId extra)

/-- Shared interpreter ABI leaf. The current state World supplies both cache and
source derivation; missing source fails at demand. No frozen Prepared table is
consulted, and successful ABI derivation cannot promote a body capability. -/
def demandInstanceAbi (access : Access S) (callee : CallInstance) (extra : Array MIR.TyId) :
    EStateM StepError S (ABI.FnAbi MIR.TyId) := do
  let state ← get
  let some world := access.get state | throw (.unsupported "source compiler World is unavailable")
  if (← query (existingInstanceAbi world callee extra)).isSome then
    return ← query (instanceAbi world callee extra)
  let (updated,abi) ← query (SourceAbi.derive world callee extra)
  let (updated,_) ← query (attachInstanceAbi updated callee extra abi)
  let result ← query (instanceAbi updated callee extra)
  set (access.put state updated)
  return result

end Miri.Input.SourceCompilerWorld
