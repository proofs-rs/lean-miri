import Miri.Frontend.FoundationPhysicalTypes

open Miri Miri.Frontend.Foundation

private def expect (r : Except String α) : IO α :=
  match r with
  | .ok a => pure a
  | .error e => throw (IO.userError e)

private def check (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)

def main : IO Unit := do
  let target := ABI.RuntimeTargetDataLayout.default
  let b ← expect (physicalLayoutOfRuntime target (.primitive "bool" ""))
  check (b.sizeBytes == some 1 && b.backendReprKind == some .scalar) "bool representation"
  let some scalar := b.backendRepresentation >>= (·.scalar) | throw (IO.userError "scalar absent")
  check (scalar.validRange == some (0, 1)) "bool range"
  check (b.randomizationSeed == 281483566645249) "bool seed"
  check (b.largestNiche.isSome) "bool niche"
  let c ← expect (physicalLayoutOfRuntime target (.primitive "char" ""))
  let some charScalar := c.backendRepresentation >>= (·.scalar) | throw (IO.userError "char absent")
  check (charScalar.validRange == some (0, 0x10ffff)) "char range"
  let u ← expect (physicalLayoutOfRuntime target (.primitive "uint" "u128"))
  check u.largestNiche.isNone "full-range integer niche"
  let arr ← expect (physicalLayoutOfRuntime target (.array (.primitive "bool" "") 3))
  check (arr.sizeBytes == some 3 && arr.randomizationSeed == b.randomizationSeed + 3) "array seed/size"
  check (arr.backendReprKind == some .memory && arr.largestNiche.isSome) "array backend/niche"
  let z ← expect (physicalLayoutOfRuntime target (.array (.primitive "bool" "") 0))
  check z.largestNiche.isNone "empty array niche"
  let unit ← expect (physicalLayoutOfRuntime {target with aggregateAlign := ⟨2⟩} (.tuple #[]))
  check (unit.abiAlignBytes == some 4) "unit aggregate alignment"
  for row in #[b, c, u, arr, z] do
    let _ ← expect ((Input.RuntimeMetadata.layout target row).mapError toString)
  let n ← expect (physicalTypeNode (.primitive "uint" "usize") 7 8)
  check (n.id == 7 && n.layoutId == 8 && n.compilerFacts.isNone) "local IDs"
  match physicalLayoutOfRuntime target (.pointer "raw" (.primitive "bool" "")) with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "unsupported pointer accepted")
  IO.println "foundation physical layouts: scalar, array, tuple and converter checks passed"
