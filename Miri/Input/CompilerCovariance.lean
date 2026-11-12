import Miri.Input.CompilerProviders
import Miri.Input.TypeArenaWorld

/-! eval_context.rs:184–212 mir_assign_valid_types. Equal canonical types
short-circuit the relation and distinct rigid heads fail structurally. Remaining
pairs require exact rustc Covariant evidence. Successful relations retain the
source layout-equality assertion. -/
namespace Miri.Input.CompilerCovariance
open Lean Miri.ABI Miri.Interpreter
/-- rustc_type_ir/src/relate.rs, pinned 8144389c895d,
`structurally_relate_tys`: distinct rigid constructor heads reach `Sorts`.
Aliases must normalize first; pattern/binder handling is deliberately deferred.
This is a type relation rule, independent of physical layout. -/
def rigidHead (kind : TypeShapeKind) : Bool :=
  match kind with
  | .alias | .patternType | .unsafeBinder => false
  | _ => true

def rigidMismatch (source target : TypeShapeKind) : Bool :=
  rigidHead source && rigidHead target && source != target

def relationWithIndex (index : CompilerQueryIndices.Covariance)
    (source target : MIR.TyId) : Except String Bool := do
  if source == target then return true
  let mut found := none
  for entry in CompilerQueryIndices.covarianceRows index source target do
    if let some old := found then
      unless old == entry.value do
        throw s!"conflicting compiler covariance query results (source={source}, target={target})"
    found := some entry.value
  let some value := found |
    throw s!"missing exact rustc covariance relation query (source={source}, target={target})"
  pure value

def relationInWorld (index : CompilerQueryIndices.Covariance) (world : TypeArena.World)
    (source target : MIR.TyId) : Except String Bool := do
  let sourceKind ← world.shapeKind source
  let targetKind ← world.shapeKind target
  if rigidMismatch sourceKind targetKind then return false
  relationWithIndex index source target

def relation (p : CompilerProviders.Prepared) (source target : MIR.TyId) : Except String Bool := do
  if source == target then return true
  let some sourceNode := p.program.input.types[source]? |
    throw s!"covariance source type is absent from material prefix: {source}"
  let some targetNode := p.program.input.types[target]? |
    throw s!"covariance target type is absent from material prefix: {target}"
  if rigidMismatch sourceNode.shape.kind targetNode.shape.kind then return false
  relationWithIndex p.covarianceIndex source target

def compatible (p : CompilerProviders.Prepared) (debugAssertions : Bool)
    (source target : LocalLayout) : Except StepError Bool := do
  let related ← relation p source.ty target.ty |>.mapError StepError.unsupported
  if !related then return false
  if debugAssertions || source.ty != target.ty then
    unless source.layout == target.layout do
      throw (.invalidProgram "covariant MIR assignment has unequal layouts")
  pure true

def hook (p : CompilerProviders.Prepared) (access : RuntimeArrayQueries.Access S)
    (debugAssertions : Bool) (source target : LocalLayout) : EStateM StepError S Bool := do
  let world ← RuntimeArrayQueries.snapshot access
  let related ← match relationInWorld p.covarianceIndex world source.ty target.ty with
    | .ok value => pure value | .error error => throw (.unsupported error)
  if !related then return false
  if debugAssertions || source.ty != target.ty then
    unless source.layout == target.layout do
      throw (.invalidProgram "covariant MIR assignment has unequal layouts")
  pure true
end Miri.Input.CompilerCovariance
