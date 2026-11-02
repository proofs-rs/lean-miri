import duplicate_prefix.ProjectionMetadataFacts

namespace DuplicatePrefix.DuplicatePrefixTypeCacheOrigins
open Miri Miri.Input Miri.ABI Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

set_option autoImplicit false in
/-- The identity/shape part of runtime array-cache consistency. Compiler
aliases refer to actual ARRAY compiler nodes; freshly constructed array IDs
are disjoint from every compiler ID. This does not require an empty cache,
nor does it assume any successful projection/layout query. Layout correctness,
key uniqueness and next-ID headroom are separate consistency obligations. -/
def EntryOrigin (world : RuntimeArrayTypes.World) (entry : RuntimeArrayTypes.Entry) : Prop :=
  match entry.origin with
  | .compiler id => entry.value.ty = id ∧ ∃ node,
      world.metadata.source.types.find? (·.id == id) = some node ∧ node.shapeKind = .array
  | .runtimeConstructor => world.metadata.source.types.any (·.id == entry.value.ty) = false

def Origins (world : RuntimeArrayTypes.World) : Prop :=
  ∀ entry ∈ world.entries, EntryOrigin world entry

/-- A compiler non-array ID cannot be shadowed by a coherent runtime ARRAY
cache. This derives absence rather than imposing absence of the target ID. -/
theorem exclude_nonarray (world : RuntimeArrayTypes.World) (origins : Origins world)
    (id : TypeId) (node : TypeNode)
    (lookup : world.metadata.source.types.find? (·.id == id) = some node)
    (nonarray : node.shapeKind ≠ .array) : world.entries.any (·.value.ty == id) = false := by
  apply Array.any_eq_false'.mpr
  intro entry member hit
  have equal : entry.value.ty = id := by simpa using hit
  have raw := origins entry member
  cases origin : entry.origin with
  | compiler declared =>
    simp only [EntryOrigin, origin] at raw
    obtain ⟨value, found, present, array⟩ := raw
    have sameId : declared = id := value.symm.trans equal
    rw [sameId, lookup] at present
    have same : node = found := Option.some.inj present
    exact nonarray (same ▸ array)
  | runtimeConstructor =>
    simp only [EntryOrigin, origin] at raw
    rw [equal] at raw
    have has : world.metadata.source.types.any (·.id == id) = true :=
      Array.any_eq_true'.mpr ⟨node, Array.mem_of_find?_eq_some lookup, Array.find?_some (p := fun item : TypeNode => item.id == id) lookup⟩
    rw [raw] at has
    cases has

theorem slice_source :
    (PreparedReflection.actual.runtime.source.types.find? (·.id == 4)).map TypeNode.shapeKind =
      some .slice := by
  with_unfolding_all rfl

/-- The old ty=4 cache-absence side condition follows from general origin
consistency and the actual compiler slice shape. Other array cache entries
may remain present. No pre-call construction history is required. -/
theorem slice_not_constructed (world : RuntimeArrayTypes.World)
    (metadata : world.metadata = PreparedReflection.actual.runtime) (origins : Origins world) :
    world.entries.any (·.value.ty == 4) = false := by
  have fact := slice_source
  cases lookup : PreparedReflection.actual.runtime.source.types.find? (·.id == 4) with
  | none => simp [lookup] at fact
  | some node =>
    have shape : node.shapeKind = .slice := by simpa only [lookup, Option.map_some, Option.some.injEq] using fact
    apply exclude_nonarray world origins 4 node
    · simpa only [metadata] using lookup
    · rw [shape]
      intro impossible
      cases impossible

/-- The production slice field query now accepts a populated coherent array
cache without assuming its target-ID absence or the query's success. -/
theorem world_slice_field (cmp : ProjectionMetadataFacts.NullComparator)
    (world : RuntimeArrayTypes.World) (metadata : world.metadata = PreparedReflection.actual.runtime)
    (origins : Origins world) :
    EvalProjectionMachine.field world ProjectionMetadataFacts.sliceLayout 0 =
      .ok CopyCompilerFacts.byteLayout :=
  ProjectionMetadataFacts.world_slice_field cmp world metadata (slice_not_constructed world metadata origins)

open CanonicalConfigFacts in
/-- The same derived absence condition feeds the actual dynamic-layout hook
used by the interpreter, with the real prestate left unchanged. -/
theorem dynamic_field_at (cmp : ProjectionMetadataFacts.NullComparator)
    (options : EvalPlaceConstruction.Options) (table : RootRawVTable)
    (choice : Unit) (state : RootState)
    (metadata : (EvalProjectionMachine.arrays.get state).metadata = PreparedReflection.actual.runtime)
    (origins : Origins (EvalProjectionMachine.arrays.get state)) :
    (EvalPlaceConstruction.dynamic PreparedReflection.actual.compiler options table).field choice
      ProjectionMetadataFacts.sliceLayout 0 state = .ok CopyCompilerFacts.byteLayout state :=
  ProjectionMetadataFacts.dynamic_field_at cmp options table choice state metadata
    (slice_not_constructed _ metadata origins)

end DuplicatePrefix.DuplicatePrefixTypeCacheOrigins
