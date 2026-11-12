import Miri.Input.TypeArenaWorld

namespace Miri.Input.WorldTrivialAutoTraits
open TypeArena
private abbrev QueryM := StateT (Std.HashMap TypeId Bool) (Except String)
private def visit (world : World) : Nat → TypeId → QueryM Bool
  | 0, _ => throw "world trivial auto-trait traversal exhausted"
  | fuel + 1, id => do
    if let some result := (← get)[id]? then return result
    let result ← do
      let view ← liftM (world.lookupType id)
      let children ← match view with
        | .material source => match source.shape with
          | .int _ | .uint _ | .float _ | .bool | .char | .str | .never
          | .reference .. | .rawPointer .. | .functionDefinition .. | .functionPointer .. => return true
          | .tuple children => pure (some children)
          | .patternType child _ | .slice child | .array child .. => pure (some #[child])
          | _ => pure none
        | .constructed constructor => match constructor with
          | .integer .. | .float _ | .bool | .char | .str | .never
          | .reference .. | .rawPointer .. | .functionDefinition .. | .functionPointer .. => return true
          | .tuple children => pure (some children)
          | .patternType child _ | .slice child | .array child _ => pure (some #[child])
          | _ => pure none
      let some children := children | return false
      for child in children do unless ← visit world fuel child do return false
      pure true
    modify fun memo => memo.insert id result
    pure result

/-- True is the pinned structural fast-path proof. False is only unknown.
The memo is fresh for this query and never enters the type universe. -/
def query (world : World) (fuel : Nat) (id : TypeId) : Except String Bool := do
  let (result,_) ← (visit world fuel id).run {}
  pure result

end Miri.Input.WorldTrivialAutoTraits
