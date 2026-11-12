import Miri.Input.WorldTypeMetadata
import Miri.Input.StructuralDiscriminantType

namespace Miri.Input.WorldDiscriminantType
open TypeArena
structure Context where
  primitive : String → WorldM TypeId
  normalize : Nat → TypeId → WorldM TypeId
private def lift [Monad m] [MonadExceptOf String m] (value : Except String A) : m A :=
  match value with | .ok result => pure result | .error error => throw error

def query (context : Context) : Nat → TypeId → WorldM TypeId
  | 0, _ => throw "world discriminant type traversal exhausted"
  | fuel + 1, id => do
    let world ← get
    let view ← lift (world.lookupType id)
    match ← lift (world.shapeKind id) with
    | .adt =>
      let declaration ← WorldTypeMetadata.adtDeclaration id
      let key ← if declaration.kind == .enumKind then lift (StructuralDiscriminantType.enumKey declaration.representation)
        else pure "u8"
      context.primitive key
    | .coroutine => context.primitive "u32"
    | .alias =>
      let normalized ← context.normalize fuel id
      if normalized == id then throw "world discriminant alias remained unresolved"
      query context fuel normalized
    | .patternType =>
      let .material source := view | throw "constructed pattern discriminant source unavailable"
      let .patternType child _ := source.shape | throw "pattern discriminant source kind mismatch"
      query context fuel child
    | .unsafeBinder =>
      let .material source := view | throw "constructed binder erasure requires its source algorithm"
      let some facts := source.compilerFacts | throw "world discriminant binder erasure material absent"
      unless facts.typingEnvironment == "fully_monomorphized" do throw "world discriminant binder environment mismatch"
      let some (_,some child) := facts.typeQueries.find? (·.1 == "unsafe_binder_erased")
        | throw "world discriminant residual binder erasure absent"
      unless child < world.materialTypes.size do throw "world binder erasure source escapes its prefix"
      query context fuel child
    | _ => context.primitive "u8"

end Miri.Input.WorldDiscriminantType
