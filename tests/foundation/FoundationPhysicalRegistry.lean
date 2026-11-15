import Miri.Frontend.FoundationPhysicalRegistry

open Lean Miri Miri.Frontend.Foundation

private def expect (r : Except String α) : IO α :=
  match r with
  | .ok a => pure a
  | .error e => throw (IO.userError e)

private def check (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: FoundationPhysicalRegistry FOUNDATION_JSON")
  let source ← IO.FS.readFile path
  let document ← expect (Json.parse source >>= decode)
  let initial := PhysicalTypeRegistry.start document
  let ty := ConcreteType.array (.array (.primitive "bool" "") 3) 2
  let (r, id) ← expect (initial.intern ty)
  check (initial.types.isEmpty && initial.registry.entries.isEmpty) "initial mutated"
  check (r.types.size == 4 && r.layouts.size == 4 && r.typeConstants.size == 2) "child-first pools"
  check (id == 3) "parent ID"
  let (again, idAgain) ← expect (r.intern ty)
  check (idAgain == id && again.types.size == r.types.size && again.typeConstants.size == 2) "repeated demand"
  let (inner, _) ← expect (r.lookup 2)
  match inner.shape with
  | .array child length ctor =>
    check (child == 0 && length == 0 && ctor.count == 3) "inner array references"
  | _ => throw (IO.userError "inner array shape")
  match r.typeConstants[0]? with
  | some (Miri.MIR.TypeConst.Value usizeId tree) =>
    check (usizeId == 1) "usize type ID"
    let target ← expect (runtimeTargetOfTarget document.target)
    check (tree.nodes == #[.Leaf 3 (target.base.pointerWidth.bits.toNat / 8)]) "typed length leaf"
  | _ => throw (IO.userError "length constant absent")
  for index in [:r.types.size] do
    let value ← expect (r.runtimeLayout index)
    check (value.ty == index) "runtime identity"
  let (more, _) ← expect (r.intern (.array (.primitive "uint" "u16") 3))
  check (more.typeConstants.size == 2) "length constants not deduplicated"
  let (fresh, freshId) ← expect (initial.intern (.primitive "bool" ""))
  check (freshId == 0 && fresh.types.size == 1) "fresh document identities"
  match r.intern (.tuple #[.primitive "bool" ""]) with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "unsupported aggregate accepted")
  IO.println "foundation physical registry: canonical child/constant IDs and runtime converter passed"
