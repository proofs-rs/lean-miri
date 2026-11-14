import Miri.Input.TypeArenaWorld
import Miri.Input.ConstIntegerPrinter
namespace Miri.Input.WorldConstantName
open TypeArena
private def lift (value : Except String A) : WorldM A :=
  match value with | .ok value => pure value | .error error => throw error
private def integerShape (pointerBytes : Nat) : MIR.IntegerKind → Bool × Bool × Nat
  | .i8 => (true,false,1) | .i16 => (true,false,2) | .i32 => (true,false,4)
  | .i64 => (true,false,8) | .i128 => (true,false,16) | .isize => (true,true,pointerBytes)
  | .u8 => (false,false,1) | .u16 => (false,false,2) | .u32 => (false,false,4)
  | .u64 => (false,false,8) | .u128 => (false,false,16) | .usize => (false,true,pointerBytes)
def query (id : TypeConstantId) : WorldM String := do
  let world ← get
  let .Value type tree ← lift (world.lookupConstant id)
    | throw "constant printing requires evaluated ConstKind::Value"
  let some (.Leaf bits bytes) := tree.nodes[tree.root]?
    | throw "constant aggregate printing is not implemented"
  let constructor ← match ← lift (world.lookupType type) with
    | .constructed value => pure value
    | .material node =>
      let some value ← lift (world.materialKey node)
        | throw "constant source type printing is not implemented"
      pure value
  match constructor with
  | .bool => lift (ConstIntegerPrinter.boolean bytes bits)
  | .integer signed kind =>
    let (expectedSigned,pointer,expectedBytes) := integerShape world.pointerBytes kind
    unless signed == expectedSigned && bytes == expectedBytes do
      throw "integer constant type and ScalarInt representation differ"
    lift (ConstIntegerPrinter.scalar signed pointer bytes bits)
  | _ => throw "constant scalar type printing is not implemented"
end Miri.Input.WorldConstantName
