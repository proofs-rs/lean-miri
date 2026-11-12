import Miri.ABI.CallConv

open Miri.ABI

private def scalar : Scalar := .Union (value := .Int .I8 false)
private def layout (repr : BackendRepr) (bytes : UInt64) : TyAndLayout Nat := ⟨0, {
  fields := .Primitive, variants := .Single 0, backendRepr := repr,
  largestNiche := none, uninhabited := false, align := AbiAlign.new Align.EIGHT,
  size := Size.ofBytes bytes, maxReprAlign := none, unadjustedAbiAlign := Align.EIGHT,
  reprC := false, randomizationSeed := 0 }⟩

private def attrs (a : ArgAttributes) : String :=
  let extension := match a.argExt with | .None => 0 | .Zext => 1 | .Sext => 2
  s!"{a.regular.toNat}/{a.pointeeSize.bytes}/{(a.pointeeAlign.map (fun x => x.pow2)).getD 99}/{extension}"
private def mode : PassMode → String
  | .Ignore => "ignore"
  | .Direct a => "direct:" ++ attrs a
  | .Pair a b => "pair:" ++ attrs a ++ ":" ++ attrs b
  | .Indirect a none .Pointer => "indirect:" ++ attrs a
  | .IndirectUnsized a b => "unsized:" ++ attrs a ++ ":" ++ attrs b
  | _ => "unexpected"

private def cases : Array (TyAndLayout Nat) := #[
  layout (.Memory (sized := true)) 0,
  layout (.Memory (sized := true)) 24,
  layout (.Memory (sized := false)) 0,
  layout (.Scalar scalar) 1,
  layout (.ScalarPair (a := scalar) (b := scalar) (bOffset := Size.ofBytes 8)) 16,
  layout (.SimdVector (element := scalar) (count := ⟨4⟩)) 4,
  layout (.SimdScalableVector (element := scalar) (count := ⟨4⟩)
    (numberOfVectors := ⟨2⟩)) 0]

def main : IO Unit := do
  unless (ArgAbi.nonPointerScalar (layout (.Memory (sized := true)) 8) 32).toOption.isNone do
    throw (IO.userError "scalar ABI recipe accepted aggregate layout")
  unless (ArgAbi.nonPointerScalar
      (layout (.Scalar (.Union (value := .Pointer .ZERO))) 8) 32).toOption.isNone do
    throw (IO.userError "scalar ABI recipe inferred pointer attributes")
  for l in cases do
    IO.println (mode (ArgAbi.initial l).mode)
    IO.println (mode (ArgAbi.new l (fun _ offset =>
      { ArgAttributes.new with regular := UInt16.ofNat (offset.bytes.toNat + 1) })).mode)

  for (primitive, bool_) in #[(Primitive.Int .I8 false,true), (.Int .I8 false,false),
      (.Int .I8 true,false), (.Int .I32 true,false), (.Float .F64,false)] do
    for initialized in #[true,false] do
      for bits in #[0,8,32,64] do
        let scalar := if initialized then
          Scalar.Initialized (value := primitive)
            (validRange := ⟨0, if bool_ then 1 else 255⟩)
          else Scalar.Union (value := primitive)
        match ArgAbi.nonPointerScalar (layout (.Scalar scalar) 8) bits with
        | .ok arg => IO.println (mode arg.mode)
        | .error reason => throw (IO.userError reason)
