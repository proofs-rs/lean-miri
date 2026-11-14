import Miri.ABI.UnionLayout

/-! Layout composition for the pinned core `MaybeUninit<T>` declaration:
`union { uninit: (), value: ManuallyDrop<T> }`, with the transparent
`ManuallyDrop<T>` declaration. Representation inputs must come from those raw
ADT declarations, including their definition-derived shuffle seeds. This leaf
accepts no completed wrapper layout or niche answer. -/
namespace Miri.ABI.MaybeUninitLayout

def compute (target : RuntimeTargetDataLayout) (value : LayoutData)
    (manuallyDrop maybeUninit : UnivariantLayout.Representation) : Except String LayoutData := do
  unless manuallyDrop.flags == 4 && !manuallyDrop.integerRepresentation &&
      manuallyDrop.align.isNone && manuallyDrop.pack.isNone do
    throw "ManuallyDrop source representation differs from pinned transparent declaration"
  unless maybeUninit.flags == 4 && !maybeUninit.integerRepresentation &&
      maybeUninit.align.isNone && maybeUninit.pack.isNone do
    throw "MaybeUninit source representation differs from pinned transparent declaration"
  let unit ← UnivariantLayout.compute target #[]
  let wrapped ← UnivariantLayout.compute target #[value] manuallyDrop .maybeUnsized
  UnionLayout.compute target #[unit,wrapped] maybeUninit

end Miri.ABI.MaybeUninitLayout
