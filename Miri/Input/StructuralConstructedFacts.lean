import Miri.Input.Model.Types

/-! Facts for genuinely new pointer/reference/value-length array constructors.
Pinned rustc inhabitedness/mod.rs::OpsemInhabitedCtx (289–314) recurses through
references and nonempty arrays, but raw pointers are always opsem-inhabited.
This differs from layout inhabitedness, where references are always inhabited.
`is_monomorphic_enough` is `!has_param`: these constructors add no type/const
parameter, erased references add no region parameter, and the array count is a
closed target-usize value. Material leaves retain their original compiler fact.
No general ADT inhabitedness or parameter-flag solver is asserted here. -/
namespace Miri.Input.StructuralConstructedFacts

def query (lookup : TypeId → Except String TypeShape)
    (material : TypeId → String → Except String Bool) (materialSize : Nat) (key : String) :
    Nat → TypeId → Except String (Option Bool)
  | 0, _ => .error "constructed compiler fact recursion exhausted"
  | fuel + 1, id => do
    unless key == "opsem_inhabited" || key == "is_monomorphic_enough" do return none
    if id < materialSize then return some (← material id key)
    match ← lookup id with
    | .rawPointer child _ =>
      if key == "opsem_inhabited" then return some true
      query lookup material materialSize key fuel child
    | .reference child .. => query lookup material materialSize key fuel child
    | .array child _ constructor =>
      unless constructor.canonicalValueConstructor do
        throw "constructed array lacks canonical value-length material"
      if key == "opsem_inhabited" && constructor.count == 0 then return some true
      query lookup material materialSize key fuel child
    | _ => pure none

end Miri.Input.StructuralConstructedFacts
