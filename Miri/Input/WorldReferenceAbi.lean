import Miri.Input.WorldSourceAutoTraits

/-! Source pointee information for top-level references, pinned layout.rs:1067
and abi.rs:318. Trait questions use the raw source solver, never result rows. -/
namespace Miri.Input.WorldReferenceAbi
open Miri.ABI GenericSubstitution

def classify (policy : AbiSessionMaterial) (definition : Option FunctionAbiMaterial) (isReturn : Bool) (layout : TyAndLayout TypeId)
    (pointee : TypeId) (mutability : Miri.MIR.Mutability) :
    RuntimeArrayTypes.CompilerM (ArgAbi TypeId) := do
  let .Scalar (.Initialized (value := .Pointer _) (validRange := range)) := layout.layout.backendRepr
    | throw "reference ABI requires an initialized scalar pointer layout"
  let world ← get
  let child ← RuntimeArrayTypes.liftType (RuntimeMetadata.layoutInWorld world.metadata pointee)
  unless child.layout.isSized do throw "thin reference ABI requires a sized pointee"
  let permitted ← if policy.optimization == .no then pure false
    else if mutability == .Not then WorldSourceAutoTraits.query pointee "freeze"
    else do
      if !(← WorldSourceAutoTraits.query pointee "unpin") then pure false
      else WorldSourceAutoTraits.query pointee "unsafe_unpin"
  let mut regular : UInt16 := 128 ||| (if range.contains 0 then 0 else 16)
  if permitted && !isReturn then
    regular := regular ||| 8 ||| 512
    if mutability == .Not then regular := regular ||| 32 ||| 4
    else if policy.llvmWritable && definition.any (! ·.rustcNoWritable) then regular := regular ||| 256
  -- On x86_64 max_reliable_alignment is Align::MAX. The sole lower limit in
  -- pinned Target::max_reliable_alignment is x86-32 Windows (outside admission).
  let align := child.layout.align.abi
  pure (ArgAbi.new layout fun _ _ =>
    { regular := regular
      argExt := .None
      pointeeSize := if permitted then child.layout.size else Size.ZERO
      pointeeAlign := if align.pow2 > 0 then some align else none })

end Miri.Input.WorldReferenceAbi
