import Miri.Input.GenericInstantiationWorld
import Miri.Input.WorldTypeHash
import Miri.Input.WorldTypeFlags
open Miri.Input Miri.Input.TypeArena Miri.Input.GenericSubstitution
private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def scalar (bits : Nat) : Term :=
  .node .constant "value" "" (.cons (.atom .type "uint" "u8")
    (.cons (.atom .aggregate "scalar" ("{\"bytes\":1,\"bits\":" ++ toString bits ++ "}")) .nil))
private def interval (start finish : Nat) : Term :=
  .node .aggregate "pattern_range" "" (.cons (scalar start) (.cons (scalar finish) .nil))
private def patterned (pattern : Term) : Term :=
  .node .type "pattern" "" (.cons (.atom .type "uint" "u8") (.cons pattern .nil))

def main : IO Unit := do
  let initial ← must (World.ofMaterial #[] #[] #[] #[] 8)
  let notNull : Term := .node .type "pattern" "" (.cons
    (.node .type "raw_pointer" "immutable" (.cons (.atom .type "uint" "u8") .nil))
    (.cons (.atom .aggregate "pattern_not_null" "") .nil))
  let node := fun id shape => ({id,shape,display := "pattern source",layoutId := 0} : TypeNode)
  let source ← must (World.ofMaterial #[node 0 (.uint (.known .u8)),node 1 (.rawPointer 0 .Not),
    node 2 (.patternType 1 .notNull)] #[] #[] #[] 8)
  let (materialId,material) ← must ((GenericInstantiationWorld.resolveType 4096 notNull).run source)
  check (materialId == 2 && material.constructedTypes.isEmpty) "complete material pattern identity was not reused"
  let duplicate ← must (World.ofMaterial #[node 0 (.uint (.known .u8)),node 1 (.rawPointer 0 .Not),
    node 2 (.patternType 1 .notNull),node 3 (.patternType 1 .notNull)] #[] #[] #[] 8)
  check (!((GenericInstantiationWorld.resolveType 4096 notNull).run duplicate).isOk)
    "ambiguous material pattern identities were accepted"
  let terms := #[notNull,patterned (interval 1 7),patterned (.node .aggregate "pattern_or" ""
    (Terms.ofArray #[interval 1 3,interval 5 7]))]
  let mut world := initial
  for term in terms do
    let (id,next) ← must ((GenericInstantiationWorld.resolveType 4096 term).run world)
    world := next
    check ((← must (GenericInstantiationWorld.ofType world 4096 id)) == term)
      "pattern constructor lost raw source syntax"
    let (reused,next) ← must ((GenericInstantiationWorld.resolveType 4096 term).run world)
    check (id == reused && next.typeCount == world.typeCount && next.constantCount == world.constantCount)
      "identical pattern source did not reuse canonical syntax"
    check ((← must (world.shapeKind id)) == .patternType) "constructed pattern has wrong shape"
    check (← must (WorldTypeFlags.query world "is_monomorphic" 4096 id)) "closed pattern rejected by type flags"
    check ((WorldTypeHash.query world 4096 id).isOk) "raw pattern hash unavailable outside material prefixes"
  let (first,next) ← must ((GenericInstantiationWorld.resolveType 4096 (patterned (interval 1 7))).run world)
  let (different,afterDifferent) ← must ((GenericInstantiationWorld.resolveType 4096 (patterned (interval 2 7))).run next)
  check (first != different) "different pattern endpoints collided"
  let (base,afterBase) ← must ((World.internType (.integer false .u8)).run afterDifferent)
  world := afterBase
  check (!((World.internType (.patternType base (.or #[.range 999999 999999]))).run world).isOk)
    "nested pattern accepted missing endpoint constants"
  let malformed := patterned (.node .aggregate "pattern_range" "" (.cons (scalar 1) .nil))
  check (!((GenericInstantiationWorld.resolveType 4096 malformed).run world).isOk) "malformed pattern accepted"
  check (!((GenericInstantiationWorld.resolveType 0 notNull).run world).isOk) "pattern traversal ignored fuel exhaustion"
  check (world.materialTypes.isEmpty && world.materialConstants.isEmpty) "novel pattern acquired source/result prefixes"
  IO.println "PASS novel NotNull/Range/Or pattern roundtrips, exact reuse, endpoint distinction, flags, missing constants, malformed syntax, fuel, raw hash availability"
