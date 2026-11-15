import Miri.Frontend.Foundation
import Miri.Input.Model.Catalogs

/-! Pure session queries from finite compiler option inputs. The equations match
pinned rustc_session/src/session.rs:1085-1095. Source capture remains a compiler
trust boundary; these functions do not query rustc or enumerate instances. -/
namespace Miri.Frontend.Foundation
open Lean

structure SessionInputs where
  internalTargetFeatures : Array String
  isLikeWasm : Bool
  targetArch : String
  debugAssertions : Bool
  ubChecks : Option Bool
  contractChecks : Option Bool
  overflowChecks : Option Bool
  deriving Repr, DecidableEq

private def optionalBool (source : Json) (name : String) : Except String (Option Bool) := do
  let value ← source.getObjVal? name
  if value == Json.null then return none
  return some (← fromJson? value)

/-- Every input is required, including null for an absent override. Missing
session fields and inconsistent architecture summaries fail closed. -/
def sessionInputs (document : Document) : Except String SessionInputs := do
  let source ← document.source.getObjVal? "session"
  let features ← source.getObjValAs? (Array String) "internal_target_features"
  let mut seen : Array String := #[]
  for feature in features do
    if feature.isEmpty || seen.contains feature then
      throw "foundation session has empty or duplicate target feature"
    seen := seen.push feature
  let arch ← source.getObjValAs? String "target_arch"
  unless !arch.isEmpty && arch == document.target.architecture do
    throw "foundation session architecture disagrees with target material"
  return {
    internalTargetFeatures := features
    isLikeWasm := ← source.getObjValAs? Bool "is_like_wasm"
    targetArch := arch
    debugAssertions := ← source.getObjValAs? Bool "debug_assertions"
    ubChecks := ← optionalBool source "ub_checks"
    contractChecks := ← optionalBool source "contract_checks"
    overflowChecks := ← optionalBool source "overflow_checks" }

/-- rootSpan must be the physical ID of captured DUMMY_SP in the source registry.
The source relocation layer owns that identity; no span is invented here. -/
def SessionInputs.toSession (inputs : SessionInputs) (rootSpan : Input.SpanId) :
    Input.Catalog.Session := {
  internalTargetFeatures := inputs.internalTargetFeatures
  isLikeWasm := inputs.isLikeWasm
  targetArch := inputs.targetArch
  rootSpan
  runtimeChecks := #[
    (.UbChecks, inputs.ubChecks.getD inputs.debugAssertions),
    (.ContractChecks, inputs.contractChecks.getD false),
    (.OverflowChecks, inputs.overflowChecks.getD inputs.debugAssertions)] }

def sessionOfDocument (document : Document) (rootSpan : Input.SpanId) :
    Except String Input.Catalog.Session := do
  return (← sessionInputs document).toSession rootSpan

end Miri.Frontend.Foundation
