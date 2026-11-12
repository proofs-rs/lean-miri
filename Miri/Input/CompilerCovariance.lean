import Miri.Input.CompilerProviders
import Miri.Input.TypeArenaWorld
import Miri.Input.VarianceMaterial

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

private def constructor (world : TypeArena.World) (id : MIR.TyId) :
    Except String (Option TypeArena.Constructor) := do
  match ← world.lookupType id with
  | .constructed value => pure (some value)
  | .material value => world.materialKey value

/-- `relate_types` builds an inference context with `ignoring_regions`.
Static and erased regions therefore impose no relation obligation. Bound,
parameter, inference and placeholder families retain explicit residuals here. -/
private def ignoredRegion : MIR.Region → Bool
  | .Static | .Erased => true
  | _ => false

/-- A query-local relation over raw World constructors. Ambient variance is
composed at every child; mutable pointees remain invariant even below nominal
contravariance. Unsupported declaration families return no structural answer. -/
private def structuralIn (world : TypeArena.World) : Nat → MIR.Variance →
    MIR.TyId → MIR.TyId → Except String (Option Bool)
  | 0, _, _, _ => throw "structural covariance traversal exhausted"
  | fuel + 1, ambient, source, target => do
    let sourceKind ← world.shapeKind source
    let targetKind ← world.shapeKind target
    if source == target || ambient == .Bivariant then return some true
    if rigidMismatch sourceKind targetKind then return some false
    let some left ← constructor world source | return none
    let some right ← constructor world target | return none
    if left == right then return some true
    let child := fun variance a b =>
      structuralIn world fuel (VarianceInference.compose ambient variance) a b
    match left, right with
    | .rawPointer a am, .rawPointer b bm =>
      if am != bm then return some false
      child (if am == .Mut then .Invariant else .Covariant) a b
    | .reference a am ar, .reference b bm br =>
      unless ignoredRegion ar && ignoredRegion br do return none
      if am != bm then return some false
      child (if am == .Mut then .Invariant else .Covariant) a b
    | .slice a, .slice b => child .Covariant a b
    | .array a ac, .array b bc =>
      let av ← world.lookupConstant ac
      let bv ← world.lookupConstant bc
      if av != bv then return none
      child .Covariant a b
    | .tuple a, .tuple b =>
      if a.size != b.size then return some false
      let mut unresolved := false
      for (a,b) in a.zip b do
        match ← child .Covariant a b with
        | some false => return some false
        | some true => pure ()
        | none => unresolved := true
      return if unresolved then none else some true
    | .adt a aa, .adt b ba =>
      if a != b then return some false
      if aa.size != ba.size then throw "nominal covariance generic arity mismatch"
      -- Declaration coverage is independent of the requested relation. An
      -- unsupported raw family retains the existing exact residual domain.
      let .ok variances := VarianceMaterial.query world.definitions a | return none
      unless variances.size == aa.size do throw "nominal covariance variance arity mismatch"
      let mut unresolved := false
      for ((a,b),variance) in (aa.zip ba).zip variances do
        let answer ← match a,b with
          | .Type a, .Type b => child variance a b
          | .Lifetime a, .Lifetime b =>
            pure (if ignoredRegion a && ignoredRegion b then some true else none)
          | .Const a, .Const b =>
            pure (if (← world.lookupConstant a) == (← world.lookupConstant b) then some true else none)
          | _, _ => throw "nominal covariance generic argument sort mismatch"
        match answer with
        | some false => return some false
        | some true => pure ()
        | none => unresolved := true
      return if unresolved then none else some true
    | .integer .., .integer .. | .float .., .float .. => return some false
    | .foreign a, .foreign b => return some (a == b)
    | _, _ => return none

def structural (world : TypeArena.World) (fuel : Nat) (source target : MIR.TyId) :
    Except String (Option Bool) :=
  structuralIn world fuel .Covariant source target

def relationInWorld (index : CompilerQueryIndices.Covariance) (world : TypeArena.World)
    (source target : MIR.TyId) : Except String Bool := do
  if let some answer ← structural world 16384 source target then return answer
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
