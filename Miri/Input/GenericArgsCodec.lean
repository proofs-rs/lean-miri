import Miri.Input.JsonReader
import Miri.MIR.Syntax

namespace Miri.Input.GenericArgsCodec
open JsonReader

open Miri.MIR

private structure boundIndexFields where
  «kind» : Option (String) := none
  «debruijn_index» : Option (Nat) := none

def boundIndex  : Parser (BoundVarIndexKind) := do
  let s ← object (boundIndexFields.mk none none) fun s key => do
    match key with
    | "kind" => return { s with «kind» := some (← string) }
    | "debruijn_index" => return { s with «debruijn_index» := some (← natural) }
    | _ => skipValue; pure s
  let variant ← required s.«kind» "kind"
  if s.«debruijn_index».isSome && !(variant == "bound") then fail s!"incompatible field `debruijn_index` for variant `{variant}`"
  match (← required s.«kind» "kind") with
  | "bound" => return .Bound (← required s.«debruijn_index» "debruijn_index")
  | "canonical" => pure .Canonical
  | _ => fail "unknown bound index kind"

private structure boundRegionFields where
  «kind» : Option (String) := none
  «name» : Option (String) := none
  «def_id» : Option (Nat) := none

def boundRegion  : Parser (BoundRegionKind) := do
  let s ← object (boundRegionFields.mk none none none) fun s key => do
    match key with
    | "kind" => return { s with «kind» := some (← string) }
    | "name" => return { s with «name» := some (← string) }
    | "def_id" => return { s with «def_id» := some (← natural) }
    | _ => skipValue; pure s
  let variant ← required s.«kind» "kind"
  if s.«name».isSome && !(variant == "named_for_printing") then fail s!"incompatible field `name` for variant `{variant}`"
  if s.«def_id».isSome && !(variant == "named") then fail s!"incompatible field `def_id` for variant `{variant}`"
  match (← required s.«kind» "kind") with
  | "anonymous" => pure .Anon
  | "named_for_printing" => return .NamedForPrinting (← required s.«name» "name")
  | "named" => return .Named (← required s.«def_id» "def_id")
  | "closure_environment" => pure .ClosureEnv
  | _ => fail "unknown bound region kind"

private structure boundTypeFields where
  «kind» : Option (String) := none
  «def_id» : Option (Nat) := none

private def boundType  : Parser (BoundTypeKind) := do
  let s ← object (boundTypeFields.mk none none) fun s key => do
    match key with
    | "kind" => return { s with «kind» := some (← string) }
    | "def_id" => return { s with «def_id» := some (← natural) }
    | _ => skipValue; pure s
  let variant ← required s.«kind» "kind"
  if s.«def_id».isSome && !(variant == "parameter") then fail s!"incompatible field `def_id` for variant `{variant}`"
  match (← required s.«kind» "kind") with
  | "anonymous" => pure .Anon
  | "parameter" => return .Param (← required s.«def_id» "def_id")
  | _ => fail "unknown bound type kind"

private structure boundVariableFields where
  «kind» : Option (String) := none
  «type_kind» : Option (BoundTypeKind) := none
  «region_kind» : Option (BoundRegionKind) := none

def boundVariable  : Parser (BoundVariableKind) := do
  let s ← object (boundVariableFields.mk none none none) fun s key => do
    match key with
    | "kind" => return { s with «kind» := some (← string) }
    | "type_kind" => return { s with «type_kind» := some (← boundType) }
    | "region_kind" => return { s with «region_kind» := some (← boundRegion) }
    | _ => skipValue; pure s
  let variant ← required s.«kind» "kind"
  if s.«type_kind».isSome && !(variant == "type") then fail s!"incompatible field `type_kind` for variant `{variant}`"
  if s.«region_kind».isSome && !(variant == "region") then fail s!"incompatible field `region_kind` for variant `{variant}`"
  match (← required s.«kind» "kind") with
  | "type" => return .Type (← required s.«type_kind» "type_kind")
  | "region" => return .Region (← required s.«region_kind» "region_kind")
  | "const" => pure .Const
  | _ => fail "unknown bound variable kind"

private structure lateParameterFields where
  «kind» : Option (String) := none
  «index» : Option (Nat) := none
  «name» : Option (String) := none
  «def_id» : Option (Nat) := none

private def lateParameter  : Parser (LateParamRegionKind) := do
  let s ← object (lateParameterFields.mk none none none none) fun s key => do
    match key with
    | "kind" => return { s with «kind» := some (← string) }
    | "index" => return { s with «index» := some (← natural) }
    | "name" => return { s with «name» := some (← string) }
    | "def_id" => return { s with «def_id» := some (← natural) }
    | _ => skipValue; pure s
  let variant ← required s.«kind» "kind"
  if s.«index».isSome && !(variant == "anonymous" || variant == "named_anonymous") then fail s!"incompatible field `index` for variant `{variant}`"
  if s.«name».isSome && !(variant == "named_anonymous") then fail s!"incompatible field `name` for variant `{variant}`"
  if s.«def_id».isSome && !(variant == "named") then fail s!"incompatible field `def_id` for variant `{variant}`"
  match (← required s.«kind» "kind") with
  | "anonymous" => return .Anon (← required s.«index» "index")
  | "named_anonymous" => return .NamedAnon (← required s.«index» "index") (← required s.«name» "name")
  | "named" => return .Named (← required s.«def_id» "def_id")
  | "closure_environment" => pure .ClosureEnv
  | _ => fail "unknown late parameter region"

private structure regionFields where
  «kind» : Option (String) := none
  «index» : Option (Nat) := none
  «name» : Option (String) := none
  «index_kind» : Option (BoundVarIndexKind) := none
  «variable_index» : Option (Nat) := none
  «bound_kind» : Option (BoundRegionKind) := none
  «scope_def_id» : Option (Nat) := none
  «parameter» : Option (LateParamRegionKind) := none
  «universe» : Option (Nat) := none

def region  : Parser (Region) := do
  let s ← object (regionFields.mk none none none none none none none none none) fun s key => do
    match key with
    | "kind" => return { s with «kind» := some (← string) }
    | "index" => return { s with «index» := some (← natural) }
    | "name" => return { s with «name» := some (← string) }
    | "index_kind" => return { s with «index_kind» := some (← boundIndex) }
    | "variable_index" => return { s with «variable_index» := some (← natural) }
    | "bound_kind" => return { s with «bound_kind» := some (← boundRegion) }
    | "scope_def_id" => return { s with «scope_def_id» := some (← natural) }
    | "parameter" => return { s with «parameter» := some (← lateParameter) }
    | "universe" => return { s with «universe» := some (← natural) }
    | _ => skipValue; pure s
  let variant ← required s.«kind» "kind"
  if s.«index».isSome && !(variant == "early_parameter") then fail s!"incompatible field `index` for variant `{variant}`"
  if s.«name».isSome && !(variant == "early_parameter") then fail s!"incompatible field `name` for variant `{variant}`"
  if s.«index_kind».isSome && !(variant == "bound") then fail s!"incompatible field `index_kind` for variant `{variant}`"
  if s.«variable_index».isSome && !(variant == "bound" || variant == "placeholder") then fail s!"incompatible field `variable_index` for variant `{variant}`"
  if s.«bound_kind».isSome && !(variant == "bound" || variant == "placeholder") then fail s!"incompatible field `bound_kind` for variant `{variant}`"
  if s.«scope_def_id».isSome && !(variant == "late_parameter") then fail s!"incompatible field `scope_def_id` for variant `{variant}`"
  if s.«parameter».isSome && !(variant == "late_parameter") then fail s!"incompatible field `parameter` for variant `{variant}`"
  if s.«universe».isSome && !(variant == "placeholder") then fail s!"incompatible field `universe` for variant `{variant}`"
  match (← required s.«kind» "kind") with
  | "early_parameter" => return .EarlyParameter (← required s.«index» "index") (← required s.«name» "name")
  | "bound" => return .Bound (← required s.«index_kind» "index_kind") (← required s.«variable_index» "variable_index") (← required s.«bound_kind» "bound_kind")
  | "late_parameter" => return .LateParameter (← required s.«scope_def_id» "scope_def_id") (← required s.«parameter» "parameter")
  | "static" => pure .Static
  | "placeholder" => return .Placeholder (← required s.«universe» "universe") (← required s.«variable_index» "variable_index") (← required s.«bound_kind» "bound_kind")
  | "erased" => pure .Erased
  | _ => fail "unknown region"

private inductive ArgumentPayload where
  | id : Nat → ArgumentPayload
  | lifetime : Region → ArgumentPayload

private def argumentPayload : Parser ArgumentPayload := do
  if (← Std.Internal.Parsec.peek!) == '{' then
    .lifetime <$> region
  else .id <$> natural

private structure argumentFields where
  «kind» : Option (String) := none
  «value» : Option (ArgumentPayload) := none

private def argument  : Parser (GenericArg) := do
  let s ← object (argumentFields.mk none none) fun s key => do
    match key with
    | "kind" => return { s with «kind» := some (← string) }
    | "value" => return { s with «value» := some (← argumentPayload) }
    | _ => skipValue; pure s
  match (← required s.«kind» "kind"), (← required s.«value» "value") with
  | "type", .id id => pure (.Type id)
  | "const", .id id => pure (.Const id)
  | "lifetime", .lifetime value => pure (.Lifetime value)
  | _, _ => fail "invalid generic argument kind or payload"

def decode : Parser (Array GenericArg) := array argument

end Miri.Input.GenericArgsCodec
