import Miri.Input.Model.SourceAllocationIdentity
import Miri.Input.Model.SourceAllocations
import Miri.Input.Model.SourceMir
import Miri.Input.Model.SourceConstValues
import Miri.Input.Model.SourceDeclarations
import Miri.Input.Model.SourceMirUses
import Miri.Input.Model.SourceTraitImpls
import Miri.Input.Model.SourceAbi
import Miri.Input.Model.SourceTypes
import Miri.Input.SourceTypeQueries

/-! Evaluation-local typed finite source. Declaration identities, lexical layers,
target evidence and optional typed syntax components remain immutable. Presence
of source syntax establishes neither an executable body nor an ABI: each demand
checks its supported constructor domain and extends the current World purely.
No JSON value or precomputed instance/query answer is retained here. -/
namespace Miri.Input
namespace SourceMaterial
abbrev ItemKind := SourceDeclarations.ItemKind
abbrev ItemRole := SourceDeclarations.ItemRole
abbrev ItemDeclaration := SourceDeclarations.ItemDeclaration
abbrev Target := SourceDeclarations.Target
abbrev GenericParameter := SourceDeclarations.GenericParameter
abbrev GenericLayer := SourceDeclarations.GenericLayer

/-- Explicit absence, with no constructor pretending unsupported material is
an empty known source body/type/constraint table. -/
inductive Unavailable where
  | unsupported
  deriving Repr, DecidableEq
/-- Complete selected declaration identity/name; initializer capability is
separate and may remain unavailable until actual predicate demand. -/
structure LinkSectionDeclaration where
  name : String
  definition : DefinitionId
  span : SourceSymbols.Span
  initializer : Unavailable := .unsupported
  deriving Repr, DecidableEq
end SourceMaterial

structure SourceMaterial where
  target : SourceMaterial.Target
  declarations : Array SourceMaterial.ItemDeclaration
  genericLayers : Array SourceMaterial.GenericLayer
  /-- None is unknown coverage; Some retains the complete ordered declaration list. -/
  linkSections : Option (Array SourceMaterial.LinkSectionDeclaration) := none
  mirUses : Option SourceMirUses.Material := none
  traitImpls : Option SourceTraitImpls.Material := none
  abi : Option SourceAbi.Material := none
  genericMir : Option SourceMir.Material := none
  physical : Option SourceTypes.Material := none
  constantValues : Option SourceConstValues.Material := none
  allocations : Option SourceAllocations.Material := none
  allocationIdentity : Option SourceAllocationIdentity.Material := none
  constraints : SourceMaterial.Unavailable := .unsupported
  deriving Repr, DecidableEq

namespace SourceMaterial

def validate (material : Input.SourceMaterial) : Except String Unit := do
  if let some allocations := material.allocations then SourceAllocations.validate allocations
  if let some identity := material.allocationIdentity then
    let some physical := material.physical | throw "allocation identity source types unavailable"
    identity.validate physical.types.size
  let target := material.target
  unless !target.triple.isEmpty && !target.architecture.isEmpty &&
      !target.dataLayout.isEmpty && target.pointerSizeBits > 0 && target.pointerSizeBits % 8 == 0 &&
      (target.endian == "little" || target.endian == "big") do
    throw "typed source target declaration invalid"
  if let some evidence := target.runtimeDataLayout then
    unless evidence.llvmDataLayout == target.dataLayout && evidence.pointerWidthBits == target.pointerSizeBits &&
        evidence.endian == target.endian do throw "typed source target evidence disagrees with declaration"
  if let some physical := material.physical then
    physical.validate
    physical.validateTarget target.pointerSizeBits
  let mut seen : Array DefinitionId := #[]
  for declaration in material.declarations do
    unless declaration.definition.crateIndex < 2^32 && declaration.definition.index < 2^32 &&
        !declaration.path.isEmpty && !seen.contains declaration.definition do
      throw "typed source Item declaration identity/path invalid or duplicated"
    let parameters ← SourceDeclarations.fullParameters material.genericLayers declaration.definition
    unless parameters == declaration.parameters do throw "typed source Item full generic slots disagree"
    seen := seen.push declaration.definition
  let mut layerOwners : Array DefinitionId := #[]
  for layer in material.genericLayers do
    unless !layerOwners.contains layer.owner do throw "typed source generic layer owner duplicated"
    layerOwners := layerOwners.push layer.owner
  if let some sections := material.linkSections then
    for entry in sections do
      unless !entry.name.isEmpty && entry.definition.crateIndex < 2^32 && entry.definition.index < 2^32 &&
          entry.span.lo ≤ entry.span.hi do throw "typed source link-section declaration invalid"
  return ()

end SourceMaterial
end Miri.Input
