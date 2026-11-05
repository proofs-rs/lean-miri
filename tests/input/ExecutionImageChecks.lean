import Miri.Input.Decoder
import Miri.Input.LowerMIR

open Lean Miri.Input
private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def required (value : Option α) (message : String) : Except String α :=
  match value with | some value => pure value | none => throw message
private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def rowJson : ExecutionImage.Row → Json
  | .null => toJson (#[0] : Array Nat)
  | .boolean b => toJson (#[if b then 2 else 1] : Array Nat)
  | .number n => .arr #[toJson (3 : Nat), .num n]
  | .string s => .arr #[toJson (4 : Nat), .str s]
  | .array ids => .arr #[toJson (5 : Nat), toJson ids]
  | .object fields => .arr #[toJson (6 : Nat), .arr (fields.map fun (a,b) => toJson #[a,b])]
private def imageJson (image : ExecutionImage.Image) : Json := Json.mkObj [
  ("schema", .str "lean-miri-prepared-image"), ("schema_version", toJson (1 : Nat)),
  ("fields", toJson image.fields), ("nodes", .arr (image.nodes.map rowJson)),
  ("root", toJson image.root)]

private def parity (image : ExecutionImage.Image) : IO Unit := do
  match JsonTraversalCache.resolve (imageJson image), JsonTraversalCache.resolveImageChecked image with
  | .error a, .error b => check (a == b) s!"native graph first error changed: {a} / {b}"
  | .ok (a,an), .ok (b,bn) =>
    check (a.root == b.root && a.nodes == b.nodes && an.key.digest == bn.node.key.digest)
      "native graph source/digest differs"
  | _, _ => throw (IO.userError "native graph acceptance differs")

-- Only used by this parity test to present retained JSON rows to the new native
-- typed interface. It does not participate in production input construction.
private def parseImage (raw : Json) : Except String ExecutionImage.Image := do
  let fields ← (← (← raw.getObjVal? "fields").getArr?).mapM Json.getStr?
  let rows ← (← raw.getObjVal? "nodes").getArr?
  let nodes ← rows.mapM fun row => do
    let row ← row.getArr?
    let some tag := row[0]? | throw "empty retained row"
    let item := fun (i : Nat) => required row[i]? "missing retained row item"
    match ← tag.getNat? with
    | 0 => pure ExecutionImage.Row.null
    | 1 => pure (.boolean false)
    | 2 => pure (.boolean true)
    | 3 => do
      let Json.num n ← item 1 | throw "not numeric"
      pure (.number n)
    | 4 => pure (.string (← (← item 1).getStr?))
    | 5 => pure (.array (← (← (← item 1).getArr?).mapM Json.getNat?))
    | 6 =>
      let fields ← (← (← item 1).getArr?).mapM fun entry => do
        let pair ← entry.getArr?
        pure (← (← required pair[0]? "missing field").getNat?,
          ← (← required pair[1]? "missing child").getNat?)
      pure (.object fields)
    | _ => throw "unknown retained row"
  pure ⟨fields,nodes,← (← raw.getObjVal? "root").getNat?⟩

def main (args : List String) : IO Unit := do
  let base : ExecutionImage.Image := ⟨#["x", "y"],
    #[.number 17, .array #[0,0], .object #[(0,1),(1,1)]], 2⟩
  parity base
  for row in [ExecutionImage.Row.array #[100], .object #[(100,0)],
      .object #[(0,0),(0,0)], .object #[(1,0),(0,0)]] do
    -- Unused rows are validated, too.
    parity { base with nodes := base.nodes.push row }
  parity { base with fields := #["x","x"] }
  parity { base with root := 100 }
  parity { base with root := 0 }
  parity ⟨#["$lean_miri_shared_ref"], #[.null, .object #[(0,0)]], 1⟩
  parity ⟨#["shared_payloads"], #[.null, .object #[(0,0)]], 1⟩
  check ((ExecutionImage.scalar 7 "").isOk == false) "invalid scalar tag accepted"
  check ((ExecutionImage.scalar 3 "true").isOk == false) "invalid number accepted"
  for path in args do
    let image ← must (parseImage (← must (Json.parse (← IO.FS.readFile path))))
    parity image
    match decodeRuntimeImageProfiled image, decodeRuntimeJson (imageJson image).compress with
    | .error a, .error b => check (a == b) "semantic first error changed"
    | .ok a, .ok b =>
      check (a.blockingObligations == b.blockingObligations &&
        a.executionInput.isSome == b.executionInput.isSome) "strict readiness changed"
      let ap ← must (lowerCoreProgram a.document)
      let bp ← must (lowerCoreProgram b.document)
      check (ap.roots == bp.roots && ap.instances == bp.instances &&
        ap.bundle.spans == bp.bundle.spans &&
        ap.bundle.bodies.map (·.body) == bp.bundle.bodies.map (·.body)) "canonical MIR changed"
    | _, _ => throw (IO.userError "semantic acceptance changed")
  IO.println "native execution image: graph errors, unused rows, source/hash, readiness and canonical MIR parity PASS"
