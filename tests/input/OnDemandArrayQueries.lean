import Miri.Input.Decoder
import Miri.Input.RuntimeArrayTypes

/-! Demand computation regressions. Supply a current exporter document with
metadata; target and primitive layouts below are synthetic test data, and the
test constructors have no exported layout rows. -/
open Miri Miri.ABI Miri.Input

private def must [Repr ε] (value : Except ε α) : IO α :=
  match value with
  | .ok value => pure value
  | .error error => throw (IO.userError (reprStr error))

private def check (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected current exporter input")
  let decoded ← must (decodeJson (← IO.FS.readFile path))
  let target : RuntimeTargetDataLayout := {
    base := ⟨.little, .w64⟩
    i1Align := .ONE, i8Align := .ONE, i16Align := ⟨1⟩, i32Align := ⟨2⟩
    i64Align := ⟨3⟩, i128Align := ⟨4⟩
    f16Align := ⟨1⟩, f32Align := ⟨2⟩, f64Align := ⟨3⟩, f128Align := ⟨4⟩
    aggregateAlign := .ONE, vectorAlign := #[]
    defaultAddressSpace := ⟨0⟩
    defaultAddressSpacePointerSpec := ⟨Size.ofBytes 8, ⟨3⟩, Size.ofBytes 8, false⟩
    addressSpaceInfo := #[], instructionAddressSpace := ⟨0⟩, cEnumMinSize := .I32 }
  let runtime : RuntimeMetadata := ⟨{ decoded.document with types := #[], layouts := #[] }, target⟩
  let byte : LayoutData := {
    fields := .Primitive, variants := .Single 0, backendRepr := .Memory (sized := true)
    largestNiche := none, uninhabited := false, align := ⟨.ONE⟩
    size := Size.ofBytes 1, maxReprAlign := none, unadjustedAbiAlign := .ONE
    reprC := false, randomizationSeed := 0 }
  let initial : RuntimeArrayTypes.World := {
    metadata := runtime, byteLayout := ⟨0, byte⟩
    wideLayout := ⟨1, {byte with size := Size.ofBytes 2, align := ⟨⟨1⟩⟩}⟩
    entries := #[], aliases := #[], nextId := 2, obligations := #[] }
  let first := initial.nextId
  let second := first + 1
  let world := { initial with aliases := #[
    (⟨.compiler first, 3⟩, second), (⟨.u8, 7⟩, first)], nextId := second + 1 }
  let nested ← must (RuntimeArrayTypes.lookup world second)
  check (nested.ty == second && nested.layout.size.bytes == 21)
    "nested array layout did not follow constructor dependencies"
  check world.entries.isEmpty "pure lookup mutated its input world"
  let (interned, updated) ← must (RuntimeArrayTypes.internElement world first 3)
  check (interned == nested && updated.nextId == world.nextId)
    "constructor failed to reuse exact compiler identity"
  let (again, repeated) ← must (RuntimeArrayTypes.internElement updated first 3)
  check (again == interned && repeated.entries.size == updated.entries.size)
    "repeat constructor allocated a second identity"
  let (key, element) ← must (RuntimeArrayTypes.arrayInfo world second)
  check (key.count == 3 && element.ty == first && element.layout.size.bytes == 7)
    "array projection failed before interning its parent"
  let cycle := { world with aliases := #[(⟨.compiler second, 1⟩, first),
    (⟨.compiler first, 1⟩, second)] }
  check (!(RuntimeArrayTypes.lookup cycle first).isOk)
    "cyclic graph produced a successful layout"
  let missing := { world with aliases := #[(⟨.compiler (second + 100), 1⟩, first)] }
  check (!(RuntimeArrayTypes.lookup missing first).isOk)
    "missing graph dependency produced a successful layout"
  let narrowBase := { world.metadata.target.base with pointerWidth := .w32 }
  let narrowTarget := { world.metadata.target with base := narrowBase }
  let narrowMetadata := { world.metadata with target := narrowTarget }
  let narrow := { world with metadata := narrowMetadata, aliases := #[(⟨.u8, UInt64.ofNat (2^32)⟩, first)] }
  check (!(RuntimeArrayTypes.lookup narrow first).isOk)
    "array count outside target usize produced a successful layout"
  let unrelated := { world with aliases := world.aliases.push (⟨.compiler (second + 100), 1⟩, second + 10) }
  let stillNested ← must (RuntimeArrayTypes.lookup unrelated second)
  check (stillNested == nested) "unrelated unresolved query blocked demanded layout"
  let other := { world with aliases := #[(⟨.u8, 2⟩, first)] }
  let changed ← must (RuntimeArrayTypes.lookup other first)
  check (changed.layout.size.bytes == 2)
    "separate immutable worlds shared a stale query result"
  IO.println "PASS pure on-demand array queries, canonical reuse, projection, cycles, missing dependencies, target overflow and world isolation"
