import Miri.ABI.PrimitiveLayout

/-! Pinned rustc 8144389c895da997dbdecaa635e41d6a50be6ffd,
`rustc_abi/src/layout.rs::layout_of_array_like` and
`rustc_ty_utils/src/layout.rs` Array/Slice/Str dispatch. The raw constant
constructor and source element type are validated by the caller. This module
accepts no exported layout answer and performs target object-size arithmetic.
-/
namespace Miri.ABI.SequenceLayout

/-- `None` distinguishes an unsized slice from a sized zero-length array. -/
def arrayLike (target : RuntimeTargetDataLayout) (element : LayoutData)
    (count : Option UInt64) : Except String LayoutData := do
  let layout ← PrimitiveLayout.arrayLike target element (match count with | none => 0 | some value => value)
  return {layout with backendRepr := .Memory (sized := count.isSome)}

def slice (target : RuntimeTargetDataLayout) (element : LayoutData) :
    Except String LayoutData := do
  let layout ← arrayLike target element none
  return {layout with randomizationSeed := 0x2dcba99c39784102}

def str (target : RuntimeTargetDataLayout) : Except String LayoutData := do
  let element ← PrimitiveLayout.compute target "u8"
  let layout ← arrayLike target element none
  return {layout with randomizationSeed := 0xc1325f37d127be22}

end Miri.ABI.SequenceLayout
