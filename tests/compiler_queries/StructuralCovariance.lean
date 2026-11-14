import Miri.Input.CompilerCovariance
import Miri.Input.Decoder

open Miri.Input

private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)

private def check (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)

def main (args : List String) : IO Unit := do
  let some path := args.head? | throw (IO.userError "expected pinned compiler export")
  let decoded ← must (decodeJson (← IO.FS.readFile path))
  let document := decoded.document
  let mut world ← must (TypeArena.World.ofDocument document)
  let mut compared := 0
  for row in document.queries.covariance do
    if let some answer ← must (CompilerCovariance.structural world 16384 row.sourceType row.targetType) then
      check (answer == row.value) s!"rustc covariance mismatch: {row.sourceType}/{row.targetType}"
      compared := compared + 1
  let boolTy := document.queries.primitives.bool
  let u8Ty := document.queries.primitives.u8
  let (left,after) ← must ((TypeArena.World.internType (.rawPointer boolTy .Mut)) world)
  world := after
  let (right,after) ← must ((TypeArena.World.internType (.rawPointer u8Ty .Mut)) world)
  world := after
  check ((← must (CompilerCovariance.relationInWorld {} world left right)) == false)
    "novel mutable pointees bypassed invariant relation"
  let (leftTuple,after) ← must ((TypeArena.World.internType (.tuple #[left,boolTy])) world)
  world := after
  let (rightTuple,after) ← must ((TypeArena.World.internType (.tuple #[right,boolTy])) world)
  world := after
  check ((← must (CompilerCovariance.relationInWorld {} world leftTuple rightTuple)) == false)
    "nested constructor relation depended on result catalog"
  check ((← must (CompilerCovariance.relationInWorld {} world leftTuple leftTuple)) == true)
    "novel identity relation failed"
  check (!(CompilerCovariance.structural world 0 left right).isOk)
    "exhausted traversal was accepted"
  check (!(CompilerCovariance.structural world 2 world.typeCount world.typeCount).isOk)
    "unknown identical type IDs were accepted"
  if let some oraclePath := args[1]? then
    let mut types := #[boolTy,u8Ty,document.queries.primitives.u16]
    for ctor in #[TypeArena.Constructor.rawPointer boolTy .Not,
        .rawPointer boolTy .Mut, .rawPointer u8Ty .Mut,
        .reference boolTy .Not .Erased, .reference boolTy .Mut .Erased,
        .reference u8Ty .Mut .Erased] do
      let (id,after) ← must ((TypeArena.World.internType ctor) world)
      world := after
      types := types.push id
    for element in #[boolTy,u8Ty] do
      let (constant,after) ← must ((TypeArena.World.internConstant
        (.Value document.queries.primitives.usize
          ⟨#[.Leaf 7 world.pointerBytes],0⟩)) world)
      world := after
      let (id,after) ← must ((TypeArena.World.internType (.array element constant)) world)
      world := after
      types := types.push id
    for ctor in #[TypeArena.Constructor.slice boolTy, .slice u8Ty,
        .tuple #[left,boolTy], .tuple #[right,boolTy], .tuple #[left]] do
      let (id,after) ← must ((TypeArena.World.internType ctor) world)
      world := after
      types := types.push id
    let oracle ← must (Lean.Json.parse (← IO.FS.readFile oraclePath))
    let rows ← must oracle.getArr?
    check (rows.size == 256) "incomplete structural covariance oracle matrix"
    for row in rows do
      let a ← must ((← must (row.getObjVal? "left")).getNat?)
      let b ← must ((← must (row.getObjVal? "right")).getNat?)
      let expected ← must ((← must (row.getObjVal? "value")).getBool?)
      let some a := types[a]? | throw (IO.userError "oracle left type index")
      let some b := types[b]? | throw (IO.userError "oracle right type index")
      check ((← must (CompilerCovariance.relationInWorld {} world a b)) == expected)
        s!"independent rustc structural covariance mismatch: {a}/{b}"
    IO.println "independent rustc 16x16 covariance matrix passed with an empty answer catalog"
  IO.println s!"structural covariance: {compared} compiler rows and novel nested/invariant controls"
