import Miri.Input.Reader.Catalog
import Miri.Input.Model.Types

namespace Miri.Input.Reader
open Lean

def Catalog.readCovariance (catalog : Catalog) (count : Nat) : Except String (Array CovarianceQuery) := do
  let values ← catalog.array (← catalog.field catalog.root "compiler_covariance_queries" "$") "covariance queries"
  values.mapIdxM fun index input => do
    let path := s!"$.compiler_covariance_queries[{index}]"
    let typeId := fun key => do
      let id ← catalog.natural (← catalog.field (← catalog.field input key path) "type_id" path) path
      unless id < count do throw s!"{path}: invalid covariance type {id}"
      pure id
    let source ← typeId "source_type"
    let target ← typeId "target_type"
    let outcome := do
      unless (← catalog.string (← catalog.field input "typing_env" path) path) == "fully_monomorphized" &&
          (← catalog.string (← catalog.field input "variance" path) path) == "covariant" do
        throw s!"{path}: covariance environment mismatch"
      catalog.requireSupported input path
      catalog.boolean (← catalog.field input "value" path) path
    return ⟨source,target,outcome⟩

end Miri.Input.Reader
