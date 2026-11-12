import Miri.ABI.UnivariantLayout

/-! Pinned rustc 8144389c895da997dbdecaa635e41d6a50be6ffd,
`rustc_abi/src/layout.rs::layout_of_union`. Common field representations are
converted to union scalars before comparison; initialized ranges and niches
never survive merely because two fields have equal sizes. -/
namespace Miri.ABI.UnionLayout

private def maxOption (left right : Option Align) : Option Align :=
  match left,right with
  | some a,some b => some (a.max b)
  | some a,none | none,some a => some a
  | none,none => none

def compute (target : RuntimeTargetDataLayout) (fields : Array LayoutData)
    (repr : UnivariantLayout.Representation := {}) : Except String LayoutData := do
  let mut align := if repr.pack.isSome then target.i8Align else target.aggregateAlign
  let mut maxReprAlign := repr.align
  let mut size := Size.ZERO
  let mut mismatch := repr.flags &&& 1 != 0
  let mut common : Option (BackendRepr × Align) := none
  for field in fields do
    if field.isUnsized then throw "unsized union field"
    align := align.max field.align.abi
    maxReprAlign := maxOption maxReprAlign field.maxReprAlign
    if field.size.bytes > size.bytes then size := field.size
    if field.size.bytes == 0 then continue
    if !mismatch then
      let fieldAbi := field.backendRepr.toUnion
      if let some (commonAbi,commonAlign) := common then
        if commonAbi != fieldAbi then mismatch := true
        else
          match commonAbi with
          | .Memory => pure ()
          | _ => unless commonAlign == field.align.abi do
              throw "matching non-memory union field ABI has differing alignment"
      else common := some (fieldAbi,field.align.abi)
  align := repr.pack.map (align.min ·) |>.getD align
  let unadjustedAbiAlign := align
  align := repr.align.map (align.max ·) |>.getD align
  let mut backend := BackendRepr.Memory (sized := true)
  if !mismatch then
    if let some (commonAbi,_) := common then
      let accepted ← match commonAbi with
        | .Scalar _ | .ScalarPair => do
          let platform ← commonAbi.scalarPlatformAlign target |>.mapError reprStr
          let some platform := platform | throw "scalar union field ABI has no alignment"
          pure (platform == align)
        | .SimdVector (element := element) => do
          let elementAlign ← element.defaultAlign target |>.mapError reprStr
          pure (elementAlign.abi.pow2 <= align.pow2)
        | _ => pure true
      if accepted then backend := commonAbi
  if fields.isEmpty then throw "empty union"
  size ← size.alignTo align |>.mapError toString
  return {
    variants := .Single 0, fields := .Union fields.size, backendRepr := backend,
    largestNiche := none, uninhabited := false, align := .new align, size,
    maxReprAlign, unadjustedAbiAlign,
    reprC := repr.flags &&& 1 != 0 ||
      (repr.flags &&& 4 != 0 && fields.any (·.reprC)),
    randomizationSeed := fields.foldl (fun seed field => seed + field.randomizationSeed)
      repr.fieldShuffleSeed }

end Miri.ABI.UnionLayout
