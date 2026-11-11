import Miri.Input.CallCompatibility
import Miri.Input.TableTail
import Miri.Input.CompilerExternAbi

open Miri Miri.Input

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def must (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def reprOptions (bits : Nat) (integer : Option ReprInteger := none)
    (pack : Option Nat := none) : ReprOptions :=
  ⟨integer, none, pack, bits, none, 0⟩

def main : IO Unit := do
  let plain := reprOptions 0
  check (plain.rust && !plain.c && !plain.simd && !plain.transparent && !plain.linear &&
    !plain.scalable && !plain.packed && !plain.inhibitEnumLayoutOptimization &&
    !plain.inhibitNewtypeAbiOptimization && !plain.inhibitStructFieldReordering &&
    !plain.canRandomizeTypeLayout) "default repr properties changed"
  let c := reprOptions 17
  check (c.c && !c.rust && c.inhibitEnumLayoutOptimization &&
    c.inhibitNewtypeAbiOptimization && c.inhibitStructFieldReordering &&
    !c.canRandomizeTypeLayout) "C must inhibit randomization and ABI/layout optimization"
  let simd := reprOptions 18
  check (simd.simd && !simd.rust && !simd.inhibitEnumLayoutOptimization &&
    simd.inhibitNewtypeAbiOptimization && simd.inhibitStructFieldReordering &&
    !simd.canRandomizeTypeLayout) "SIMD repr properties changed"
  let linear := reprOptions 24
  check (linear.linear && linear.rust && !linear.inhibitEnumLayoutOptimization &&
    !linear.inhibitNewtypeAbiOptimization && linear.inhibitStructFieldReordering &&
    !linear.canRandomizeTypeLayout) "linear remains Rust but inhibits field reordering"
  let scalable := reprOptions 80
  check (scalable.scalable && !scalable.rust && !scalable.inhibitNewtypeAbiOptimization &&
    scalable.inhibitStructFieldReordering && !scalable.canRandomizeTypeLayout)
    "scalable repr properties changed"
  let elementOnly := {plain with scalableElement := some (.elementCount 4)}
  check (!elementOnly.scalable && elementOnly.rust)
    "scalable element metadata replaced the independent scalable flag"
  let transparent := reprOptions 20
  check (transparent.transparent && !transparent.rust &&
    !transparent.inhibitStructFieldReordering && transparent.canRandomizeTypeLayout)
    "transparent must not invent field-reordering inhibition"
  let integer := reprOptions 16 (some (.pointerSized false))
  check (integer.rust && integer.inhibitEnumLayoutOptimization &&
    integer.inhibitStructFieldReordering && !integer.inhibitNewtypeAbiOptimization &&
    !integer.canRandomizeTypeLayout) "explicit integer repr properties changed"
  let packed := reprOptions 16 none (some 1)
  check (packed.packed && packed.rust && packed.canRandomizeTypeLayout)
    "packed repr lost its independent pack field"
  check ((reprOptions 32).rust && !(reprOptions 32).inhibitStructFieldReordering)
    "unrelated non-Rustic-ABI bit changed repr classification"

  for bits in #[0, 1, 2, 4, 6, 7, 8, 16, 32, 64, 128, 256, 512, 65535] do
    let text := "{\"regular_bits\":" ++ toString bits ++ ",\"pointee_size_bytes\":0,\"pointee_align_bytes\":null,\"arg_extension\":{\"kind\":\"none\"}}"
    let parsed ← must (JsonReader.run (DecoderValues.parseAbiAttributes "attributes") text)
    let .ok actual := CallCompatibility.attributes parsed
      | throw (IO.userError "canonical regular bits rejected")
    check (actual.regular.toNat == bits) "regular bits changed during runtime conversion"
    for captureMask in #[4, 6, 7] do
      check (actual.contains (UInt16.ofNat captureMask) == (bits &&& captureMask == captureMask))
        "overlapping capture masks changed during runtime conversion"
    check (actual.contains 64 == (bits &&& 64 == 64)) "InReg no longer comes from canonical bits"
  let oversized : AbiAttributes := ⟨65536, 0, none, .none⟩
  check (!(CallCompatibility.attributes oversized).isOk) "u16 regular bits overflow accepted"
  let cAbi ← must (JsonReader.run CompilerExternAbi.decode "{\"kind\":\"c\",\"unwind\":false}")
  let system ← must (JsonReader.run CompilerExternAbi.decode "{\"kind\":\"system\",\"unwind\":false}")
  let unwind ← must (JsonReader.run CompilerExternAbi.decode "{\"kind\":\"c\",\"unwind\":true}")
  check (cAbi != system && cAbi != unwind && system != unwind)
    "ABI kind or unwind distinction collapsed without source_spelling"
  check (!(JsonReader.run CompilerExternAbi.decode "{\"kind\":\"c\",\"unwind\":null}").isOk)
    "missing C unwind flag accepted"
  check (!(JsonReader.run CompilerExternAbi.decode "{\"kind\":\"rust\",\"unwind\":false}").isOk)
    "Rust accepted an inapplicable unwind flag"

  let typeText := "{\"type_id\":7,\"display\":\"bool\",\"layout\":0,\"layout_query_input_type\":3,\"shape\":{\"kind\":\"bool\"}}"
  let node ← must (JsonReader.run DecoderValues.parseTypeNode typeText)
  check (node.id == 7 && node.layoutQueryInputTypeId == some 3)
    "original and region-erased query type identities collapsed"
  IO.println "canonical wire fields preserve repr, ABI flags, unwind and query type distinctions"
