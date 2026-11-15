import Miri.Input.Model.SourceTypes

/-! One finite, observation-only compiler allocation-map snapshot. Raw compiler
numbers are neither source graph indices nor evaluation-local allocation IDs.
Only the vtable key family currently has structural equality capability; other
families retain occupied raw identities and explicitly unavailable key syntax.
The producer must capture all globals/dedup entries at a serial boundary and
verify that serialization did not change the observed allocation state. -/
namespace Miri.Input.SourceAllocationIdentity
inductive Kind where
  | memory | static | function | vtable | typeId
  deriving Repr, DecidableEq
structure Global where
  rawId : UInt64
  kind : Kind
  deriving Repr, DecidableEq
inductive Key where
  | vtable (type dynamicType : SourceTypes.TypeRef)
  | unavailable (kind : Kind)
  deriving Repr, DecidableEq
structure Dedup where
  rawId : UInt64
  salt : UInt64
  key : Key
  deriving Repr, DecidableEq
structure Material where
  /-- The next raw number, read without reserving a sentinel allocation. -/
  frontier : UInt64
  globals : Array Global
  dedup : Array Dedup
  deriving Repr, DecidableEq

/-- Evaluation-local canonical key; raw number remains compiler-owned. -/
structure CanonicalVTable where
  type : Nat
  predicates : Array Nat
  salt : UInt64
  rawId : UInt64
  deriving Repr, DecidableEq

def Key.kind : Key → Kind
  | .vtable .. => .vtable
  | .unavailable kind => kind

/-- Boundary validation. Completeness is a producer observation contract, not
inferred from an empty list. Unsupported key families cannot witness equality. -/
def Material.validate (material : Material) (typeCount : Nat) : Except String Unit := do
  unless material.frontier.toNat > 0 do throw "allocation identity frontier exhausted"
  let mut globals : Array UInt64 := #[]
  for global in material.globals do
    unless global.rawId.toNat > 0 && global.rawId < material.frontier &&
        !globals.contains global.rawId do throw "allocation identity global raw ID invalid/duplicated"
    globals := globals.push global.rawId
  let mut dedupIds : Array UInt64 := #[]
  let mut vtableKeys : Array (SourceTypes.TypeRef × SourceTypes.TypeRef × UInt64) := #[]
  for entry in material.dedup do
    let some global := material.globals.find? (·.rawId == entry.rawId)
      | throw "allocation identity dedup target absent from global map"
    unless global.kind == entry.key.kind && !dedupIds.contains entry.rawId do
      throw "allocation identity dedup kind/unique target mismatch"
    dedupIds := dedupIds.push entry.rawId
    match entry.key with
    | .vtable type dynamicType =>
      unless !vtableKeys.contains (type,dynamicType,entry.salt) do
        throw "duplicate allocation identity vtable key/salt"
      vtableKeys := vtableKeys.push (type,dynamicType,entry.salt)
      unless type < typeCount && dynamicType < typeCount do
        throw "allocation identity vtable source type reference absent"
    | .unavailable .vtable => throw "complete allocation identity snapshot omitted a vtable key"
    | .unavailable _ => pure ()
end Miri.Input.SourceAllocationIdentity
