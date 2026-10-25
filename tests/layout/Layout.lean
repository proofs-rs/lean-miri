import Miri.ABI.Layout
open Miri.ABI

#eval do
  unless (FieldsShape.Primitive.indexByIncreasingOffset == Except.ok #[0]) do throw (IO.userError "runtime assertion failed")
#eval do
  unless ((FieldsShape.Array (Size.ofBytes 4) 3).offset 2 == Except.ok (Size.ofBytes 8)) do throw (IO.userError "runtime assertion failed")
#eval do
  unless ((FieldsShape.Array (Size.ofBytes 4) 3).offset 3 =
    Except.error (LayoutError.fieldOutOfBounds 3 3)) do throw (IO.userError "runtime assertion failed")
#eval do
  unless ((FieldsShape.Union 0).validate == Except.error LayoutError.invalidUnionCount) do throw (IO.userError "runtime assertion failed")
#eval do
  unless ((FieldsShape.Arbitrary #[Size.ofBytes 8, Size.ZERO] #[1, 0]).indexByIncreasingOffset =
    Except.ok #[1, 0]) do throw (IO.userError "runtime assertion failed")
#eval do
  unless ((FieldsShape.Arbitrary #[Size.ZERO, Size.ofBytes 8] #[0, 0]).validate =
    Except.error LayoutError.invalidMemoryOrder) do throw (IO.userError "runtime assertion failed")
#eval do
  unless ((FieldsShape.Arbitrary #[Size.ZERO, Size.ofBytes 8] #[1, 0]).validate =
    Except.error LayoutError.invalidMemoryOrder) do throw (IO.userError "runtime assertion failed")

private def fixture : LayoutData := {
  fields := .Arbitrary #[] #[], variants := .Single 0,
  backendRepr := .Memory (sized := true), largestNiche := none,
  uninhabited := false, align := .new Align.ONE, size := Size.ZERO,
  maxReprAlign := none, unadjustedAbiAlign := Align.ONE, reprC := false,
  randomizationSeed := 0 }
#eval do
  unless (fixture.eqAbi { fixture with randomizationSeed := 123, reprC := true } == true) do throw (IO.userError "runtime assertion failed")
#eval do
  unless (VariantLayout.fromLayout { fixture with fields := .Primitive } =
    Except.error LayoutError.expectedArbitraryVariant) do throw (IO.userError "runtime assertion failed")

private def outputOffset (shape : FieldsShape) (index : Nat) : String :=
  match shape.offset index with | Except.ok size => toString size.bytes | Except.error _ => "error"

def main : IO Unit := do
  IO.println s!"primitive_count={FieldsShape.Primitive.count}"
  for index in [0, 1, 2] do
    IO.println s!"union_{index}={outputOffset (.Union 3) index}"
    IO.println s!"array_{index}={outputOffset (.Array (Size.ofBytes 4) 3) index}"
    IO.println s!"arbitrary_{index}={outputOffset (.Arbitrary #[Size.ofBytes 8, Size.ZERO, Size.ofBytes 4] #[1, 2, 0]) index}"

example : FieldsShape.Primitive.count = 0 := rfl
example : fixture.isZst = true := rfl
example : fixture.is1zst = true := rfl
example : fixture.isAggregate = true := rfl
example : fixture.isSsaStandalone = true := rfl
example : fixture.isVariantUninhabited 1 = true := rfl
example : { fixture with backendRepr := .Memory (sized := false) }.isZst = false := rfl
