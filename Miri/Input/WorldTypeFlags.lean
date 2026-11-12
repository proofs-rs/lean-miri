import Miri.Input.TypeArenaWorld

/-! Pinned rustc_type_ir::{flags,visit}: constructor flags union child flags.
Material leaves retain explicit flag-query results until their source graph
projection is migrated. No declaration field types contribute to an ADT's
identity flags. Regions are free except Erased/Bound, including Static. -/
namespace Miri.Input.WorldTypeFlags
open TypeArena

private def regionFlag (key : String) (depth : Nat) : MIR.Region → Bool
  | .EarlyParameter .. => key == "has_erasable_regions" || key == "is_monomorphic_enough"
  | .Static | .LateParameter .. => key == "has_erasable_regions"
  | .Bound (.Bound index) .. => key == "is_monomorphic" && index >= depth
  | .Bound .Canonical .. | .Erased => false
  | .InferenceVariable .. | .Placeholder .. | .Error =>
    key == "has_erasable_regions" || key == "is_monomorphic"

private def argsRegions (constructor : Constructor) : Array MIR.Region :=
  let args := match constructor with
    | .adt _ args | .functionDefinition _ args _ | .alias _ _ _ args
    | .closure _ args | .coroutineClosure _ args | .coroutine _ args => args
    | _ => #[]
  let direct := match constructor with | .reference _ _ region => #[region] | _ => #[]
  direct ++ args.filterMap (fun arg => match arg with | .Lifetime region => some region | _ => none)

private abbrev FlagM := StateT (Std.HashMap (Bool × Nat × Nat) Bool) (Except String)

mutual
private def typeFlag (world : World) (key : String) (depth : Nat) : Nat → TypeId → FlagM Bool
  | 0, _ => throw "world type-flag traversal exhausted"
  | fuel + 1, id => do
    if let some result := (← get)[(false,id,depth)]? then return result
    let result ← do
      let view ← liftM (world.lookupType id)
      if let .material source := view then
        if let some facts := source.compilerFacts then
          unless facts.typingEnvironment == "fully_monomorphized" do throw "material type-flag environment mismatch"
          if let some (_,result) := facts.booleanQueries.find? (·.1 == key) then
            return if key == "has_erasable_regions" then result else !result
      let constructor ← match view with
        | .material source => do
          let some constructor ← liftM (world.materialKey source)
            | throw "material type flags require an unported source constructor"
          pure constructor
        | .constructed constructor => pure constructor
      if key == "is_monomorphic" then
        if let .functionDefinition _ _ variables := constructor then
          unless variables.isEmpty do throw "world closed-type flags exclude nonempty FnDef binders"
      if (argsRegions constructor).any (regionFlag key depth) then return true
      let childDepth := match constructor with | .functionPointer _ => depth + 1 | _ => depth
      for child in constructor.typeChildren do
        if ← typeFlag world key childDepth fuel child then return true
      for child in constructor.constantChildren do
        if ← constFlag world key childDepth fuel child then return true
      pure false
    modify fun memo => memo.insert (false,id,depth) result
    pure result
private def constFlag (world : World) (key : String) (depth : Nat) : Nat → TypeConstantId → FlagM Bool
  | 0, _ => throw "world constant-flag traversal exhausted"
  | fuel + 1, id => do
    if let some result := (← get)[(true,id,depth)]? then return result
    let result ← do
      match ← liftM (world.lookupConstant id) with
      | .Param .. => pure (key != "has_erasable_regions")
      | .InferVar _ | .Placeholder .. | .Error => pure (key == "is_monomorphic")
      | .InferFresh _ | .Bound .Canonical _ => pure false
      | .Bound (.Bound index) _ => pure (key == "is_monomorphic" && index >= depth)
      | .Alias _ _ _ args | .Expr _ args =>
        for arg in args do
          match arg with
          | .Type child => if ← typeFlag world key depth fuel child then return true
          | .Lifetime region => if regionFlag key depth region then return true
          | .Const child => if ← constFlag world key depth fuel child then return true
        pure false
      | .Value ty tree =>
        if ← typeFlag world key depth fuel ty then return true
        let some root := tree.nodes[tree.root]? | throw "constant flag value-tree root absent"
        match root with
        | .Leaf .. => pure false
        | .Branch children =>
          for child in children do
            if ← constFlag world key depth fuel child then return true
          pure false
    modify fun memo => memo.insert (true,id,depth) result
    pure result

end

def query (world : World) (key : String) (fuel : Nat) (id : TypeId) : Except String Bool := do
  unless #["has_erasable_regions", "is_monomorphic_enough", "is_monomorphic"].contains key do
    throw "unsupported world type-flag query"
  let (flag,_) ← (typeFlag world key 0 fuel id).run {}
  pure (if key == "has_erasable_regions" then flag else !flag)

end Miri.Input.WorldTypeFlags
