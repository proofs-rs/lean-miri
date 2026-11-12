import Miri.ABI.SignatureSeeds
open Miri.ABI
private def cases : Array (SignatureSeed Nat × Array Nat) := #[
  (⟨#[0,1],8,.Rust,false⟩,#[]),
  (⟨#[0],8,.C false,true⟩,#[2,3]),
  (⟨#[0],8,.C false,false⟩,#[2]),
  (⟨#[0,100],8,.RustCall,false⟩,#[]),
  (⟨#[101],8,.RustCall,false⟩,#[]),
  (⟨#[0,100],8,.RustCall,false⟩,#[2]),
  (⟨#[0,100],8,.RustCall,true⟩,#[]),
  (⟨#[],8,.RustCall,false⟩,#[]),
  (⟨#[0,1],8,.RustCall,false⟩,#[]),
  (⟨#[],8,.C false,true⟩,#[2])]
def main : IO Unit := do
  for (seed,extra) in cases do
    for caller in #[none,some 9] do
      let tuple (ty : Nat) := if ty == 100 then some #[2,3]
        else if ty == 101 then some #[] else none
      match seed.plan extra caller tuple with
      | .error _ => IO.println "error"
      | .ok result => IO.println s!"ok:{String.intercalate "," (result.inputs.toList.map toString)}:{result.fixedCount}"
