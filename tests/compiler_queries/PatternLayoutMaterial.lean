import Miri.Input.PatternLayoutMaterial

/-! Component-only raw endpoint validation; actual rustc layout correspondence
is checked separately by PatternLayouts.lean. -/
open Miri.Input
private def rawEndpoint (ty bits bytes : Nat) : Miri.MIR.TypeConst := .Value ty ⟨#[.Leaf bits bytes],0⟩
example : PatternLayoutMaterial.endpoint (fun _ => .ok (rawEndpoint 4 255 1)) 4 1 0 = .ok (BitVec.ofNat 128 255) := by decide
example : (PatternLayoutMaterial.endpoint (fun _ => .ok (rawEndpoint 5 1 1)) 4 1 0).isOk = false := by decide
example : (PatternLayoutMaterial.endpoint (fun _ => .ok (rawEndpoint 4 256 1)) 4 1 0).isOk = false := by decide
example : (PatternLayoutMaterial.endpoint (fun _ => .ok (rawEndpoint 4 1 2)) 4 1 0).isOk = false := by decide
example : (PatternLayoutMaterial.endpoint (fun _ => .ok (.Value 4 ⟨#[.Leaf 1 1,.Leaf 2 1],0⟩)) 4 1 0).isOk = false := by decide
example : (PatternLayoutMaterial.endpoint (fun _ => .ok (.Param 0 "N" none)) 4 1 0).isOk = false := by decide
example : (PatternLayoutMaterial.endpoint (fun _ => .error "absent") 4 1 0).isOk = false := by decide
