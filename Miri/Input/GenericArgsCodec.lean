import Lean
import Miri.MIR.Syntax

/-! Typed local generic arguments. References are serialization-local IDs;
parsing does not expand the type, definition, or type-constant tables. -/
namespace Miri.Input.GenericArgsCodec
open Lean Miri.MIR
private def field (j : Json) (key : String) : Except String Json := j.getObjVal? key
private def natural (j : Json) (key : String) : Except String Nat := do (← field j key).getNat?
private def text (j : Json) (key : String) : Except String String := do (← field j key).getStr?
private def tag (j : Json) : Except String String := text j "kind"

def boundIndex (j : Json) : Except String BoundVarIndexKind := do
  match ← tag j with
  | "bound" => return .Bound (← natural j "debruijn_index")
  | "canonical" => pure .Canonical
  | _ => throw "unknown bound index kind"

def boundRegion (j : Json) : Except String BoundRegionKind := do
  match ← tag j with
  | "anonymous" => pure .Anon
  | "named_for_printing" => return .NamedForPrinting (← text j "name")
  | "named" => return .Named (← natural j "def_id")
  | "closure_environment" => pure .ClosureEnv
  | _ => throw "unknown bound region kind"

def boundVariable (j : Json) : Except String BoundVariableKind := do
  match ← tag j with
  | "type" =>
    let value ← field j "type_kind"
    match ← tag value with
    | "anonymous" => pure (.Type .Anon)
    | "parameter" => return .Type (.Param (← natural value "def_id"))
    | _ => throw "unknown bound type kind"
  | "region" => return .Region (← boundRegion (← field j "region_kind"))
  | "const" => pure .Const
  | _ => throw "unknown bound variable kind"

def region (j : Json) : Except String Region := do
  match ← tag j with
  | "early_parameter" => return .EarlyParameter (← natural j "index") (← text j "name")
  | "bound" => return .Bound (← boundIndex (← field j "index_kind")) (← natural j "variable_index") (← boundRegion (← field j "bound_kind"))
  | "late_parameter" =>
    let p ← field j "parameter"
    let parameter : LateParamRegionKind ← match ← tag p with
      | "anonymous" => pure (LateParamRegionKind.Anon (← natural p "index"))
      | "named_anonymous" => pure (.NamedAnon (← natural p "index") (← text p "name"))
      | "named" => pure (.Named (← natural p "def_id"))
      | "closure_environment" => pure .ClosureEnv
      | _ => throw "unknown late parameter region"
    return .LateParameter (← natural j "scope_def_id") parameter
  | "static" => pure .Static
  | "placeholder" => return .Placeholder (← natural j "universe") (← natural j "variable_index") (← boundRegion (← field j "bound_kind"))
  | "erased" => pure .Erased
  | _ => throw "unknown region"

def decode (j : Json) : Except String (Array GenericArg) := do
  let values ← j.getArr?
  values.mapM fun value => do
    let payload ← field value "value"
    match ← tag value with
    | "type" => return .Type (← payload.getNat?)
    | "const" => return .Const (← payload.getNat?)
    | "lifetime" => return .Lifetime (← region payload)
    | _ => throw "unknown generic argument kind"

end Miri.Input.GenericArgsCodec
