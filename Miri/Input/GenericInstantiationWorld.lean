import Miri.ABI.PackedExternAbi
import Miri.Input.TypeArenaWorld
import Miri.Input.GenericMaterialCodec
import Lean.Data.Json.Parser

/-! On-demand generic type construction in one execution-owned universe.
Reification reads that universeIndex; construction returns its updated persistent
state. No algebraic IDs, material-only snapshots or query-result caches occur.
-/
namespace Miri.Input.GenericInstantiationWorld
open GenericSubstitution TypeArena

private def lift {m : Type → Type} [Monad m] [MonadExceptOf String m] (result : Except String α) : m α :=
  match result with | .ok value => pure value | .error error => throw error
private def arrayOfTerms (result : Array Term) : Terms → Array Term
  | .nil => result | .cons head tail => arrayOfTerms (result.push head) tail
private def integerName : MIR.IntegerKind → String
  | .i8 => "i8" | .i16 => "i16" | .i32 => "i32" | .i64 => "i64" | .i128 => "i128" | .isize => "isize"
  | .u8 => "u8" | .u16 => "u16" | .u32 => "u32" | .u64 => "u64" | .u128 => "u128" | .usize => "usize"
private def integerKind : String → Except String MIR.IntegerKind
  | "i8" => .ok .i8 | "i16" => .ok .i16 | "i32" => .ok .i32 | "i64" => .ok .i64
  | "i128" => .ok .i128 | "isize" => .ok .isize | "u8" => .ok .u8 | "u16" => .ok .u16
  | "u32" => .ok .u32 | "u64" => .ok .u64 | "u128" => .ok .u128 | "usize" => .ok .usize
  | _ => .error "generic integer constructor is unknown"
private def signedInteger : MIR.IntegerKind → Bool
  | .i8 | .i16 | .i32 | .i64 | .i128 | .isize => true
  | _ => false
private def boundIdentity (world : World) : MIR.BoundRegionKind → Except String BoundIdentity
  | .Anon => pure .anonymous | .NamedForPrinting name => pure (.namedForPrinting name)
  | .Named id => do
    pure (.named (← world.identity id))
  | .ClosureEnv => pure .closureEnvironment

def ofRegion (world : World) : MIR.Region → Except String Term
  | .EarlyParameter index _ => pure (.parameter .region index)
  | .Bound index variableIndex kind => do
    pure (.bound .region index variableIndex (← boundIdentity world kind))
  | .Placeholder universeIndex variableIndex kind => do
    pure (.placeholder .region universeIndex variableIndex (← boundIdentity world kind))
  | .Static => pure (.atom .region "static" "") | .Erased => pure (.atom .region "erased" "")
  | .InferenceVariable variableIndex => pure (.inference .region variableIndex)
  | .LateParameter scope kind => do
    let child ← match kind with
      | .Anon index => pure (.atom .region "anonymous" (toString index))
      | .NamedAnon index name => pure (.node .region "named_anonymous" (toString index)
          (.cons (.atom .region "printing_name" name) .nil))
      | .Named definition => do
        pure (.definition .region "named" (← world.identity definition) .nil)
      | .ClosureEnv => pure (.atom .region "closure_environment" "")
    pure (.definition .region "late_parameter" (← world.identity scope) (.cons child .nil))
  | .Error => .error "error region in generic type universeIndex"

private def scalar (bits bytes : Nat) : Term :=
  .atom .aggregate "scalar" ("{\"bytes\":" ++ toString bytes ++ ",\"bits\":" ++ toString bits ++ "}")

private structure ReifyState where
  types : Array (TypeId × Term) := #[]
  constants : Array (TypeConstantId × Term) := #[]
private abbrev ReifyM := StateT ReifyState (Except String)
private def liftReify (result : Except String α) : ReifyM α :=
  match result with | .ok value => pure value | .error error => throw error

/- Per-traversal AST sharing only. This memo is discarded when the fold ends;
no normalization, trait, layout or compiler query result is retained. -/
mutual
def reifyType (world : World) : Nat → TypeId → ReifyM Term
  | 0, _ => throw "generic universe type reification exhausted"
  | fuel + 1, id => do
    if let some (_,term) := (← get).types.find? (·.1 == id) then return term
    let constructor ← match ← liftReify (world.lookupType id) with
      | .constructed constructor => pure constructor
      | .material source => do
        let some constructor ← liftReify (world.materialKey source)
          | throw "material type lacks lossless generic universe constructor"
        pure constructor
    let child := reifyType world fuel
    let args := reifyArguments world fuel
    let result ← match constructor with
      | .bool => pure (.atom .type "bool" "") | .char => pure (.atom .type "char" "")
      | .str => pure (.atom .type "str" "") | .never => pure (.atom .type "never" "")
      | .integer signed kind => pure (.atom .type (if signed then "int" else "uint") (integerName kind))
      | .float kind => do
        let name ← match kind with
          | .f16 => pure "f16" | .f32 => pure "f32" | .f64 => pure "f64" | .f128 => pure "f128"
          | _ => throw "generic universe float has no pinned rustc constructor"
        pure (.atom .type "float" name)
      | .rawPointer pointee mutability => do
        pure (.node .type "raw_pointer"
          (if mutability == .Mut then "mutable" else "immutable") (.cons (← child pointee) .nil))
      | .reference pointee mutability region => do
        pure (.node .type "reference"
          (if mutability == .Mut then "mutable" else "immutable")
          (.cons (← liftReify (ofRegion world region)) (.cons (← child pointee) .nil)))
      | .slice element => do
        pure (.node .type "slice" "" (.cons (← child element) .nil))
      | .tuple elements => do
        pure (.node .type "tuple" "" (Terms.ofArray (← elements.mapM child)))
      | .array element length => do
        pure (.node .type "array" ""
          (.cons (← child element) (.cons (← reifyConstant world fuel length) .nil)))
      | .adt definition arguments => do
        pure (.definition .type "adt" definition (Terms.ofArray (← args arguments)))
      | .foreign definition => pure (.definition .type "foreign" definition .nil)
      | .functionDefinition definition arguments variables => do
        unless variables.isEmpty do throw "generic universe FnDef excludes nonempty argument binders"
        pure (.definition .type "function_definition" definition
          (.cons (.binder #[] (.node .aggregate "arguments" "" (Terms.ofArray (← args arguments)))) .nil))
      | .functionPointer signature => do
        let header := Lean.Json.compress (Lean.Json.mkObj [
          ("abi_packed", Lean.toJson signature.abiPacked), ("safe", Lean.toJson signature.safe),
          ("c_variadic", Lean.toJson signature.cVariadic), ("splatted", Lean.toJson signature.splatted)])
        let types ← (signature.inputs.push signature.output).mapM child
        pure (.node .type "function_pointer" ""
          (.cons (.binder #[] (.node .aggregate "signature" header (Terms.ofArray types))) .nil))
      | .closure definition arguments => do
        pure (.definition .type "closure" definition (Terms.ofArray (← args arguments)))
      | .coroutineClosure definition arguments => do
        pure (.definition .type "coroutine_closure" definition (Terms.ofArray (← args arguments)))
      | .coroutine definition arguments => do
        pure (.definition .type "coroutine" definition (Terms.ofArray (← args arguments)))
      | .alias kind rigid definition arguments => do
        let kind := match kind with | .projection => "projection" | .inherent => "inherent" | .opaque => "opaque" | .free => "free"
        pure (.definition .type ("alias_" ++ kind ++ if rigid then "_rigid" else "_not_rigid")
          definition (Terms.ofArray (← args arguments)))
    modify fun state => {state with types := state.types.push (id,result)}
    pure result

def reifyArgument (world : World) : Nat → MIR.GenericArg → ReifyM Term
  | 0, _ => throw "generic universe argument reification exhausted"
  | fuel + 1, .Type id => reifyType world fuel id
  | _ + 1, .Lifetime region => liftReify (ofRegion world region)
  | fuel + 1, .Const id => reifyConstant world fuel id

def reifyArguments (world : World) : Nat → Array MIR.GenericArg → ReifyM (Array Term)
  | 0, _ => throw "generic universe arguments reification exhausted"
  | fuel + 1, args => args.mapM (reifyArgument world fuel)

def reifyConstant (world : World) : Nat → TypeConstantId → ReifyM Term
  | 0, _ => throw "generic universe constant reification exhausted"
  | fuel + 1, id => do
    if let some (_,term) := (← get).constants.find? (·.1 == id) then return term
    let result ← match ← liftReify (world.lookupConstant id) with
      | .Param index _ _ => pure (.parameter .constant index)
      | .Bound index variableIndex => pure (.bound .constant index variableIndex .anonymous)
      | .Placeholder universeIndex variableIndex => pure (.placeholder .constant universeIndex variableIndex .anonymous)
      | .Value ty tree => do
        let some root := tree.nodes[tree.root]? | throw "generic universe valtree root absent"
        let value ← match root with
          | .Leaf bits bytes => pure (scalar bits bytes)
          | .Branch children => do
            pure (.node .aggregate "valtree_branch" ""
              (Terms.ofArray (← children.mapM (reifyConstant world fuel))))
        pure (.node .constant "value" "" (.cons (← reifyType world fuel ty) (.cons value .nil)))
      | _ => throw "generic universe constant constructor is not reconstructed"
    modify fun state => {state with constants := state.constants.push (id,result)}
    pure result
end

def ofType (world : World) (fuel : Nat) (id : TypeId) : Except String Term :=
  (reifyType world fuel id).run {} |>.map Prod.fst

def ofArguments (world : World) (fuel : Nat) (args : Array MIR.GenericArg) : Except String (Array Term) :=
  (reifyArguments world fuel args).run {} |>.map Prod.fst

def ofArgument (world : World) (fuel : Nat) (arg : MIR.GenericArg) : Except String Term :=
  (reifyArgument world fuel arg).run {} |>.map Prod.fst

def ofConstant (world : World) (fuel : Nat) (id : TypeConstantId) : Except String Term :=
  (reifyConstant world fuel id).run {} |>.map Prod.fst

private def regionIdentity (world : World) : BoundIdentity → Except String MIR.BoundRegionKind
  | .anonymous => pure .Anon | .namedForPrinting name => pure (.NamedForPrinting name)
  | .named identity => do
    pure (.Named (← world.definitionRef identity))
  | .closureEnvironment => pure .ClosureEnv

def resolveRegion (world : World) : Term → Except String MIR.Region
  | .atom .region "erased" "" => pure .Erased | .atom .region "static" "" => pure .Static
  | .bound .region index variableIndex identity => do
    pure (.Bound index variableIndex (← regionIdentity world identity))
  | .placeholder .region universeIndex variableIndex identity => do
    pure (.Placeholder universeIndex variableIndex (← regionIdentity world identity))
  | _ => .error "generic universe region requires erasure or explicit bound/placeholder material"

private def mutability : String → Except String MIR.Mutability
  | "mutable" => pure .Mut | "immutable" => pure .Not | _ => .error "generic pointer mutability is unknown"

private structure ConstructState where
  types : Array (Term × TypeId) := #[]
  constants : Array (Term × TypeConstantId) := #[]
private abbrev ConstructM := StateT ConstructState WorldM
private def sameTerm (left right : Term) : Bool :=
  (withPtrEqDecEq left right (fun _ => inferInstance)).decide

mutual
def constructType : Nat → Term → ConstructM TypeId
  | 0, _ => throw "generic universe type construction exhausted"
  | fuel + 1, term => do
    if let some (_,id) := (← get).types.find? (fun row => sameTerm row.1 term) then return id
    let constructor : Constructor ← match term with
      | .atom .type "bool" "" => pure Constructor.bool
      | .atom .type "char" "" => pure .char
      | .atom .type "str" "" => pure .str
      | .atom .type "never" "" => pure .never
      | .atom .type "int" kind => do
        let kind ← lift (integerKind kind)
        unless signedInteger kind do throw "signed generic constructor carries an unsigned kind"
        pure (.integer true kind)
      | .atom .type "uint" kind => do
        let kind ← lift (integerKind kind)
        if signedInteger kind then throw "unsigned generic constructor carries a signed kind"
        pure (.integer false kind)
      | .atom .type "float" kind => do
        match kind with
        | "f16" => pure (.float .f16) | "f32" => pure (.float .f32)
        | "f64" => pure (.float .f64) | "f128" => pure (.float .f128)
        | _ => throw "generic universe float constructor is unknown"
      | .node .type "raw_pointer" mutTag (.cons child .nil) => do
        pure (.rawPointer (← constructType fuel child) (← lift (mutability mutTag)))
      | .node .type "reference" mutTag (.cons region (.cons child .nil)) => do
        let region ← lift (resolveRegion (← getThe World) region)
        pure (.reference (← constructType fuel child) (← lift (mutability mutTag)) region)
      | .node .type "slice" "" (.cons child .nil) => do
        pure (.slice (← constructType fuel child))
      | .node .type "tuple" "" children => do
        pure (.tuple (← (arrayOfTerms #[] children).mapM (constructType fuel)))
      | .node .type "array" "" (.cons child (.cons length .nil)) => do
        pure (.array (← constructType fuel child) (← constructConstant fuel length))
      | .node .type "function_pointer" ""
          (.cons (.binder variables (.node .aggregate "signature" payload children)) .nil) => do
        unless variables.isEmpty do throw "function-pointer bound type construction is not implemented"
        let header ← lift (Lean.Json.parse payload)
        for (key,_) in (← lift header.getObj?).toArray do
          unless ["abi_packed", "safe", "c_variadic", "splatted"].contains key do
            throw "function-pointer signature header has unknown field"
        let abiPacked ← lift ((← lift (header.getObjVal? "abi_packed")).getNat?)
        let _ ← lift (Miri.ABI.ExternAbi.ofPacked abiPacked)
        let safe ← lift ((← lift (header.getObjVal? "safe")).getBool?)
        let cVariadic ← lift ((← lift (header.getObjVal? "c_variadic")).getBool?)
        let rawSplatted ← lift (header.getObjVal? "splatted")
        let splatted ← if rawSplatted == .null then pure none else some <$> lift rawSplatted.getNat?
        let types ← (arrayOfTerms #[] children).mapM (constructType fuel)
        let some output := types.back? | throw "function-pointer output absent"
        pure (.functionPointer {abiPacked, safe, cVariadic, splatted, inputs := types.pop, output})
      | .definition .type "adt" identity arguments => do
        pure (.adt identity (← constructArguments fuel (arrayOfTerms #[] arguments)))
      | .definition .type "foreign" identity .nil => pure (.foreign identity)
      | .definition .type "function_definition" identity
          (.cons (.binder variables (.node .aggregate "arguments" "" arguments)) .nil) => do
        unless variables.isEmpty do throw "generic universe FnDef excludes nonempty argument binders"
        pure (.functionDefinition identity (← constructArguments fuel (arrayOfTerms #[] arguments)) #[])
      | .definition .type "closure" identity arguments => do
        pure (.closure identity (← constructArguments fuel (arrayOfTerms #[] arguments)))
      | .definition .type "coroutine_closure" identity arguments => do
        pure (.coroutineClosure identity (← constructArguments fuel (arrayOfTerms #[] arguments)))
      | .definition .type "coroutine" identity arguments => do
        pure (.coroutine identity (← constructArguments fuel (arrayOfTerms #[] arguments)))
      | .definition .type tag identity arguments => do
        let pair ← match tag with
          | "alias_projection_rigid" => pure (AliasTypeKind.projection,true)
          | "alias_projection_not_rigid" => pure (.projection,false)
          | "alias_inherent_rigid" => pure (.inherent,true)
          | "alias_inherent_not_rigid" => pure (.inherent,false)
          | "alias_opaque_rigid" => pure (.opaque,true)
          | "alias_opaque_not_rigid" => pure (.opaque,false)
          | "alias_free_rigid" => pure (.free,true)
          | "alias_free_not_rigid" => pure (.free,false)
          | _ => throw "generic universe nominal constructor is unknown"
        pure (.alias pair.1 pair.2 identity (← constructArguments fuel (arrayOfTerms #[] arguments)))
      | _ => throw "generic universe type constructor is unsupported"
    let id ← liftM (World.internType constructor)
    modify fun state => {state with types := state.types.push (term,id)}
    pure id

def constructArguments : Nat → Array Term → ConstructM (Array MIR.GenericArg)
  | 0, _ => throw "generic universe argument construction exhausted"
  | fuel + 1, arguments => arguments.mapM fun argument => do
    match argument.sort with
    | .type => do
      pure (.Type (← constructType fuel argument))
    | .region => do
      pure (.Lifetime (← lift (resolveRegion (← getThe World) argument)))
    | .constant => do
      pure (.Const (← constructConstant fuel argument))
    | .aggregate => throw "aggregate term cannot be a generic argument"

def constructConstant : Nat → Term → ConstructM TypeConstantId
  | 0, _ => throw "generic universe constant construction exhausted"
  | fuel + 1, term => do
    if let some (_,id) := (← get).constants.find? (fun row => sameTerm row.1 term) then return id
    let constant : MIR.TypeConst ← match term with
      | .bound .constant index variableIndex .anonymous => pure (MIR.TypeConst.Bound index variableIndex)
      | .placeholder .constant universeIndex variableIndex .anonymous => pure (.Placeholder universeIndex variableIndex)
      | .node .constant "value" "" (.cons ty (.cons value .nil)) => do
        let ty ← constructType fuel ty
        let node : MIR.ValTreeNode ← match value with
          | .atom .aggregate "scalar" payload => do
            let raw ← lift (Lean.Json.parse payload)
            let bits ← lift ((← lift (raw.getObjVal? "bits")).getNat?)
            let bytes ← lift ((← lift (raw.getObjVal? "bytes")).getNat?)
            pure (MIR.ValTreeNode.Leaf bits bytes)
          | .node .aggregate "valtree_branch" "" children => do
            pure (.Branch (← (arrayOfTerms #[] children).mapM (constructConstant fuel)))
          | _ => throw "generic universe constant value tree is unsupported"
        pure (.Value ty ⟨#[node],0⟩)
      | _ => throw "generic universe constant requires explicit closed construction material"
    let id ← liftM (World.internConstant constant)
    modify fun state => {state with constants := state.constants.push (term,id)}
    pure id
end

def resolveType (fuel : Nat) (term : Term) : WorldM TypeId :=
  (constructType fuel term).run {} |>.map Prod.fst

def resolveArguments (fuel : Nat) (terms : Array Term) : WorldM (Array MIR.GenericArg) :=
  (constructArguments fuel terms).run {} |>.map Prod.fst

def resolveConstant (fuel : Nat) (term : Term) : WorldM TypeConstantId :=
  (constructConstant fuel term).run {} |>.map Prod.fst

def instantiateFieldTerm (world : World) (fuel : Nat) (definition : DefinitionIdentity)
    (arguments : Array MIR.GenericArg) (variant field : Nat) : Except String Term := do
  let id ← world.definitionRef definition
  let some source := world.definitions[id]? | throw "generic universe definition source absent"
  let some material := source.genericTemplate | throw "generic universe field template absent"
  let arguments ← ofArguments world fuel arguments
  material.instantiateField fuel arguments variant field

end Miri.Input.GenericInstantiationWorld
