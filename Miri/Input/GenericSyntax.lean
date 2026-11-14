import Miri.Input.RawFunctionSignature

/-! Typed validation of raw generic constructor trees. Universe visibility and
inference-variable ownership are query-state obligations, not syntax checks. -/
namespace Miri.Input.GenericSyntax
open GenericSubstitution

inductive Role where
  | type | region | constant | signature | pattern | predicate | valtree | regionName
  deriving Repr, DecidableEq

structure Policy where
  parameters : Array ArgSort := #[]
  inference : Bool := false
  placeholders : Bool := false
  erasedRegions : Bool := false
  lateRegions : Bool := false
  boundTypes : Bool := true
  boundConstants : Bool := true

private def Role.sort : Role → ArgSort
  | .type => .type | .region | .regionName => .region | .constant => .constant
  | _ => .aggregate

private def terms : Terms → Array Term
  | .nil => #[] | .cons value rest => #[value] ++ terms rest

private def argumentRole : ArgSort → Except String Role
  | .type => pure .type | .region => pure .region | .constant => pure .constant
  | .aggregate => throw "generic argument has aggregate sort"

private def aliasType (tag : String) : Bool :=
  ["projection","inherent","opaque","free"].any fun family =>
    tag == s!"alias_{family}_rigid" || tag == s!"alias_{family}_not_rigid"

private def aliasConst (tag : String) : Bool :=
  ["projection","inherent_self","inherent_impl","free","anonymous"].any fun family =>
    tag == s!"alias_{family}_rigid" || tag == s!"alias_{family}_not_rigid"

private def validateIdentity (sort : ArgSort) (identity : BoundIdentity) : Except String Unit :=
  match sort,identity with
  | .type,.anonymous | .type,.named _ | .region,_ | .constant,.anonymous => pure ()
  | _,_ => throw "generic bound identity does not belong to its variable sort"

private def validateVariables (policy : Policy) (variables : Array BoundVariable) : Except String Unit := do
  for binderVariable in variables do
    match binderVariable with
    | .type identity =>
      unless policy.boundTypes do throw "bound type variable outside supported syntax domain"
      validateIdentity .type identity
    | .region identity => validateIdentity .region identity
    | .constant => unless policy.boundConstants do
      throw "bound constant variable outside supported syntax domain"

private def validateAt (policy : Policy) : Nat → Array (Array BoundVariable) → Role → Term → Except String Unit
  | 0, _, _, _ => throw "generic syntax validation exhausted"
  | fuel + 1, scopes, role, value => do
    unless value.sort == role.sort do throw "generic syntax role/sort mismatch"
    let check := validateAt policy fuel scopes
    let args := fun (values : Array Term) => do
      for value in values do check (← argumentRole value.sort) value
    match value with
    | .parameter sort index =>
      unless role == .type || role == .region || role == .constant do
        throw "generic parameter outside a type/region/constant role"
      unless policy.parameters[index]? == some sort do throw "generic syntax parameter index/sort mismatch"
    | .inference _ _ =>
      unless policy.inference && (role == .type || role == .region || role == .constant) do
        throw "inference variable forbidden for this generic syntax role"
    | .placeholder sort _ _ identity =>
      unless policy.placeholders && (role == .type || role == .region || role == .constant) do
        throw "placeholder forbidden for this generic syntax role"
      validateIdentity sort identity
    | .bound sort (.Bound depth) index identity =>
      unless role == .type || role == .region || role == .constant do
        throw "bound variable outside a type/region/constant role"
      unless depth < scopes.size do throw "generic syntax escaping bound variable"
      let some variables := scopes[scopes.size - 1 - depth]? | throw "generic syntax binder scope is absent"
      let some boundVariable := variables[index]? | throw "generic syntax bound variable index is absent"
      match sort,boundVariable with
      | .region,.region expected => unless identity == expected do throw "bound region identity mismatch"
      | .type,.type expected =>
        unless policy.boundTypes && identity == expected do throw "bound type identity/domain mismatch"
      | .constant,.constant =>
        unless policy.boundConstants && identity == .anonymous do throw "bound constant identity/domain mismatch"
      | _,_ => throw "generic syntax bound variable sort mismatch"
    | .bound .. => throw "unknown generic syntax bound-variable index"
    | .binder variables body =>
      validateVariables policy variables
      if role == .signature then
        let signature ← RawFunctionSignature.read value
        for ty in signature.inputs.push signature.output do
          validateAt policy fuel (scopes.push variables) .type ty
      else if role == .predicate then
        validateAt policy fuel (scopes.push variables) .predicate body
      else throw "unexpected binder for generic syntax role"
    | .atom .type tag payload =>
      let valid :=
        if ["bool","char","str","never"].contains tag then payload.isEmpty
        else if tag == "int" then ["i8","i16","i32","i64","i128","isize"].contains payload
        else if tag == "uint" then ["u8","u16","u32","u64","u128","usize"].contains payload
        else tag == "float" && ["f16","f32","f64","f128"].contains payload
      unless valid do throw "unknown generic syntax primitive type"
    | .atom .region tag payload =>
      if role == .regionName then
        unless (tag == "closure_environment" && payload.isEmpty) ||
            (tag == "anonymous" && payload.toNat?.isSome) do throw "unknown late-region name syntax"
      else unless payload.isEmpty && (tag == "static" ||
          (tag == "erased" && policy.erasedRegions)) do throw "unknown generic syntax region"
    | .atom .aggregate "pattern_not_null" payload =>
      unless role == .pattern && payload.isEmpty do throw "invalid not-null pattern syntax"
    | .atom .aggregate "scalar" payload =>
      unless role == .valtree do throw "scalar leaf outside a valtree"
      let raw ← Lean.Json.parse payload
      unless (← raw.getObj?).size == 2 do throw "valtree scalar has extra fields"
      let bytes ← (← raw.getObjVal? "bytes").getNat?
      let bits ← (← raw.getObjVal? "bits").getNat?
      unless bytes > 0 && bytes ≤ 16 do throw "valtree scalar width mismatch"
      unless bits < 2^(8*bytes) do throw "valtree scalar range mismatch"
    | .definition .type tag _ children =>
      let values := terms children
      if tag == "foreign" then
        unless values.isEmpty do throw "foreign type has generic arguments"
      else if tag == "adt" || aliasType tag ||
          ["closure","coroutine_closure","coroutine","coroutine_witness"].contains tag then args values
      else if tag == "function_definition" then
        let #[.binder variables (.node .aggregate "arguments" "" children)] := values
          | throw "function-definition argument binder syntax mismatch"
        validateVariables policy variables
        for argument in terms children do
          validateAt policy fuel (scopes.push variables) (← argumentRole argument.sort) argument
      else throw "unknown nominal generic type syntax"
    | .definition .constant tag _ children =>
      unless aliasConst tag do throw "unknown generic constant alias syntax"
      args (terms children)
    | .definition .region tag _ children =>
      if role == .regionName then
        unless tag == "named" && (terms children).isEmpty do throw "invalid late-region named identity"
      else
        unless policy.lateRegions && tag == "late_parameter" do throw "late region forbidden in generic syntax"
        let #[name] := terms children | throw "late region name arity mismatch"
        check .regionName name
    | .definition .aggregate tag _ children =>
      unless role == .predicate do throw "existential predicate outside predicate syntax"
      let values := terms children
      if tag == "trait" then args values
      else if tag == "auto_trait" then
        unless values.isEmpty do throw "auto-trait predicate has arguments"
      else if tag == "projection" then
        let some output := values.back? | throw "existential projection has no term"
        unless output.sort == .type || output.sort == .constant do throw "invalid existential projection output sort"
        args values
      else throw "unknown existential predicate syntax"
    | .node .type tag payload children =>
      let values := terms children
      if tag == "reference" then
        let #[region,pointee] := values | throw "reference syntax arity mismatch"
        unless ["mutable","immutable"].contains payload do throw "reference syntax mutability mismatch"
        check .region region; check .type pointee
      else if tag == "raw_pointer" then
        let #[pointee] := values | throw "pointer syntax arity mismatch"
        unless ["mutable","immutable"].contains payload do throw "pointer syntax mutability mismatch"
        check .type pointee
      else
        unless payload.isEmpty do throw "unexpected generic type syntax payload"
        if tag == "tuple" then for ty in values do check .type ty
        else if tag == "slice" then
          let #[element] := values | throw "slice syntax arity mismatch"
          check .type element
        else if tag == "array" then
          let #[element,length] := values | throw "array syntax arity mismatch"
          check .type element; check .constant length
        else if tag == "pattern" then
          let #[base,pattern] := values | throw "pattern type syntax arity mismatch"
          check .type base; check .pattern pattern
        else if tag == "function_pointer" then
          let #[signature] := values | throw "function-pointer syntax arity mismatch"
          check .signature signature
        else if tag == "unsafe_binder" then
          let #[.binder variables body] := values | throw "unsafe binder syntax arity mismatch"
          validateVariables policy variables
          validateAt policy fuel (scopes.push variables) .type body
        else if tag == "dynamic" then
          let some region := values.back? | throw "dynamic syntax has no object lifetime"
          for predicate in values.pop do
            let .binder _ _ := predicate | throw "existential predicate lacks its binder"
            check .predicate predicate
          check .region region
        else throw "unknown generic type constructor syntax"
    | .node .constant tag payload children =>
      let values := terms children
      if tag == "value" then
        unless payload.isEmpty do throw "unexpected value-constant payload"
        let #[ty,tree] := values | throw "value-constant syntax arity mismatch"
        check .type ty; check .valtree tree
      else if tag == "binary_expression" then
        let some opcode := payload.toNat? | throw "invalid binary constant opcode"
        unless opcode < 26 do throw "unknown pinned MIR binary constant opcode"
        let #[leftTy,rightTy,left,right] := values | throw "binary constant expression arity mismatch"
        check .type leftTy; check .type rightTy
        check .constant left; check .constant right
      else if tag == "unary_expression" then
        let some opcode := payload.toNat? | throw "invalid unary constant opcode"
        unless opcode < 3 do throw "unknown pinned MIR unary constant opcode"
        let #[ty,operand] := values | throw "unary constant expression arity mismatch"
        check .type ty; check .constant operand
      else if tag == "cast_expression" then
        let some opcode := payload.toNat? | throw "invalid abstract constant cast opcode"
        unless opcode < 2 do throw "unknown pinned abstract constant cast opcode"
        let #[sourceTy,operand,targetTy] := values | throw "constant cast expression arity mismatch"
        check .type sourceTy; check .constant operand; check .type targetTy
      else if tag == "function_call_expression" then
        unless payload.isEmpty do throw "unexpected constant-call opcode payload"
        let some functionTy := values[0]? | throw "constant call has no function type"
        let some functionValue := values[1]? | throw "constant call has no function value"
        check .type functionTy; check .constant functionValue
        for argument in values.extract 2 values.size do check .constant argument
      else throw "unknown generic constant constructor syntax"
    | .node .region "named_anonymous" payload children =>
      unless role == .regionName && payload.toNat?.isSome do throw "invalid late-region anonymous index"
      let #[.atom .region "printing_name" _] := terms children | throw "invalid late-region printing name"
    | .node .aggregate tag payload children =>
      unless payload.isEmpty do throw "unexpected aggregate syntax payload"
      let values := terms children
      if role == .pattern && tag == "pattern_range" then
        let #[start,finish] := values | throw "pattern range syntax arity mismatch"
        check .constant start; check .constant finish
      else if role == .pattern && tag == "pattern_or" then
        for pattern in values do check .pattern pattern
      else if role == .valtree && tag == "valtree_branch" then
        for value in values do check .constant value
      else throw "unknown aggregate constructor syntax"
    | _ => throw "unsupported generic syntax constructor/role"

def validateInBinders (policy : Policy) (fuel : Nat) (scopes : Array (Array BoundVariable))
    (role : Role) (value : Term) : Except String Unit := do
  unless policy.parameters.all (· != .aggregate) do throw "aggregate cannot be a generic parameter sort"
  for scope in scopes do validateVariables policy scope
  validateAt policy fuel scopes role value

def validate (policy : Policy) (fuel : Nat) (role : Role) (value : Term) : Except String Unit :=
  validateInBinders policy fuel #[] role value

end Miri.Input.GenericSyntax
