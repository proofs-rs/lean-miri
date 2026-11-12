import Miri.Input.SequenceLayoutMaterial
open Miri.Input

private def usize : TypeNode := { id := 0, shape := .uint (.known .usize), display := "", layoutId := 0 }
private def node (id : Nat) : Except String TypeNode :=
  if id == 0 then .ok usize else .error "absent source type"
private def count (value : Miri.MIR.TypeConst) (id : Nat) : Except String Miri.MIR.TypeConst :=
  if id == 0 then .ok value else .error "absent source constant"
private def leaf (bits bytes : Nat) : Miri.MIR.TypeConst := .Value 0 ⟨#[.Leaf bits bytes],0⟩
private def run (value : Miri.MIR.TypeConst) (expected : Nat) (canonical := true)
    (bytes := 8) := SequenceLayoutMaterial.arrayCount node (count value) bytes 0 ⟨expected,canonical⟩
private def check (value : Bool) (reason : String) : IO Unit :=
  unless value do throw (IO.userError reason)

def main : IO Unit := do
  check (run (leaf 3 8) 3 == .ok 3) "canonical usize value changed"
  check (run (leaf 0 4) 0 true 4 == .ok 0) "target32 zero length rejected"
  check (!(run (leaf 3 8) 4).isOk) "count summary replaced source value"
  check (!(run (leaf 3 8) 3 false).isOk) "noncanonical length used summarized count"
  check (!(run (leaf 3 4) 3).isOk) "source scalar byte width mismatch accepted"
  check (!(run (leaf (2^32) 4) (2^32) true 4).isOk) "target usize overflow accepted"
  check (!(run (.Value 0 ⟨#[.Branch #[]],0⟩) 0).isOk) "aggregate value accepted as usize"
  check (!(run (.Value 0 ⟨#[.Leaf 0 8],1⟩) 0).isOk) "absent valtree root accepted"
  check (!(run (.Value 0 ⟨#[.Leaf 0 8,.Leaf 0 8],0⟩) 0).isOk) "noncanonical scalar valtree accepted"
  check (!(run (.Param 0 "N" none) 0).isOk) "unevaluated parameter accepted as raw usize value"
  check (!(run (leaf 0 8) 0 true 0).isOk) "zero target pointer width accepted"
  IO.println "PASS 11 raw sequence value controls (count identity, canonical shape, width, bounds, missing/evaluation failures)"
