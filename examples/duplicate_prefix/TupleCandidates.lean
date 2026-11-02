import duplicate_prefix.RootScalarQueries
namespace DuplicatePrefix.TupleCandidates
open Miri Miri.Input Miri.ABI Miri.Interpreter
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def candidates (nodes : Array TypeNode) (elements : Array TypeId) : Except RuntimeMetadataError (Array TypeId) := do
  let mut result := #[]
  for node in nodes do
    if node.shapeKind == .tuple && node.shapeStatus == .supported then
      let shape ← RuntimeMetadata.jsonField node.payload "shape"
      let values ← RuntimeMetadata.array shape "elements"
      let ids ← values.mapM fun value => RuntimeMetadata.number value "type_id"
      if ids == elements then result := result.push node.id
  return result

theorem tuple_eq (metadata : RuntimeMetadata) (elements : Array TypeId) :
    metadata.tupleLayout elements = (do
      let values ← candidates metadata.source.types elements
      unless values.size == 1 do throw (.unsupported "ambiguous or absent exact tuple type")
      metadata.lookup (← RuntimeMetadata.require values[0]? "tuple type")) := by
  unfold RuntimeMetadata.tupleLayout candidates
  simp only [bind, Except.bind, pure, Except.pure]
  split <;> simp_all

theorem actual_candidates : candidates RootMetadataQueries.context.runtime.source.types #[5,0] = .ok #[205] := by
  with_unfolding_all rfl

theorem find_kind_of_projection (metadata : RuntimeMetadata) (kind : TypeShapeKind) (ty : TypeId)
    (size : (metadata.source.types.filter (·.shapeKind == kind)).size = 1)
    (entry : ((metadata.source.types.filter (·.shapeKind == kind))[0]?).map (·.id) = some ty) :
    metadata.findKind kind = metadata.lookup ty := by
  unfold RuntimeMetadata.findKind
  dsimp only
  rw [size]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, bind, Except.bind]
  cases found : (metadata.source.types.filter (·.shapeKind == kind))[0]? with
  | none => simp [found] at entry
  | some node =>
    simp only [found, Option.map_some, Option.some.injEq] at entry
    simp [RuntimeMetadata.require, pure, Except.pure, entry]

#print axioms actual_candidates
end DuplicatePrefix.TupleCandidates
