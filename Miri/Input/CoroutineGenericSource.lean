import Miri.Input.Model.Coroutine
import Miri.Input.GenericMaterialCodec
import Miri.Input.GenericSyntax

namespace Miri.Input.CoroutineGenericSource
open GenericSubstitution

private def terms : Terms → Array Term
  | .nil => #[]
  | .cons head tail => #[head] ++ terms tail

/-- Structural checks on raw source declarations. This does not certify the
compiler source or supply a physical layout; callers still select and instantiate
one exact physical owner and derive its child layouts in their own World. -/
def validate (source : CoroutineGenericSource) : Except String Unit := do
  unless source.parameters.size == source.parentCount + 5 &&
      source.parameters.drop source.parentCount == Array.replicate 5 ArgSort.type do
    throw "coroutine generic source: synthetic argument domain mismatch"
  unless source.witnessParameters.size ≤ source.parentCount &&
      source.parameters.take source.witnessParameters.size == source.witnessParameters do
    throw "coroutine generic source: witness/typeck prefix mismatch"
  GenericSyntax.validate {parameters := source.parameters, erasedRegions := true, lateRegions := true}
    4096 .type source.typeExpression
  GenericMaterialCodec.validateParameters source.parameters 4096 source.typeExpression
  let .definition .type "coroutine" owner children := source.typeExpression |
    throw "coroutine generic source: declaration has wrong type constructor"
  let arguments := terms children
  unless owner == source.owner && arguments.size == source.parameters.size do
    throw "coroutine generic source: declaration owner/argument count mismatch"
  for (argument,sort) in arguments.zip source.parameters do
    unless argument.sort == sort do throw "coroutine generic source: declaration argument sort mismatch"
  unless arguments[source.parentCount]? == some source.identityKind do
    throw "coroutine generic source: identity kind differs from declaration"
  let kind ← CoroutineBodyDispatch.kindOfTerm source.identityKind
  if let some moved := source.byMoveOwner then
    unless moved != source.owner && (kind == .fnShared || kind == .fnMut) do
      throw "coroutine generic source: invalid by-move owner declaration"
  unless source.physicalOwner == source.owner || source.byMoveOwner == some source.physicalOwner do
    throw "coroutine generic source: unrelated physical owner"
  unless source.layout.variants.size == source.layout.variantSources.size &&
      source.layout.variants.size ≥ 3 do
    throw "coroutine generic source: state/source domain mismatch"
  unless source.layout.storageConflicts.size == source.layout.fields.size do
    throw "coroutine generic source: conflict matrix dimension mismatch"
  for field in source.layout.fields do
    unless field.typeId.sort == .type do throw "coroutine generic source: saved field is not a type"
    GenericSyntax.validate {parameters := source.parameters, erasedRegions := true, lateRegions := true}
      4096 .type field.typeId
    GenericMaterialCodec.validateParameters source.parameters 4096 field.typeId
  for row in source.layout.storageConflicts do
    unless row.all (· < source.layout.fields.size) && row.toList.eraseDups.length == row.size do
      throw "coroutine generic source: invalid conflict matrix row"
  for row in source.layout.variants do
    unless row.all (· < source.layout.fields.size) && row.toList.eraseDups.length == row.size do
      throw "coroutine generic source: invalid state saved-field relation"

def validateCatalog (sources : Array CoroutineGenericSource) : Except String Unit := do
  let mut seen : Array (DefinitionIdentity × DefinitionIdentity) := #[]
  for source in sources do
    validate source
    let key := (source.owner,source.physicalOwner)
    unless !seen.contains key do throw "coroutine generic source: duplicate physical owner"
    seen := seen.push key
    let peers := sources.filter (·.owner == source.owner)
    unless peers.all (fun peer => peer.typeckOwner == source.typeckOwner &&
        peer.parentCount == source.parentCount && peer.parameters == source.parameters &&
        peer.witnessParameters == source.witnessParameters &&
        peer.typeExpression == source.typeExpression && peer.identityKind == source.identityKind &&
        peer.byMoveOwner == source.byMoveOwner) do
      throw "coroutine generic source: inconsistent logical owner declarations"
    unless peers.any (·.physicalOwner == source.owner) do
      throw "coroutine generic source: ordinary physical owner missing"
    if let some moved := source.byMoveOwner then
      unless peers.any (·.physicalOwner == moved) do
        throw "coroutine generic source: generated physical owner missing"

end Miri.Input.CoroutineGenericSource
