import Miri.Input.TraitSelection.Fulfill

/-! Fixed raw-declaration component checks, not rustc differential evidence.
Providers reject every unimplemented external/builtin operation. The positive
cases therefore exercise actual head substitution and nested-clause evaluation. -/
open Miri.Input.GenericSubstitution Miri.Input.TraitSelection

private instance {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .ok a, .ok b => match decEq a b with
    | .isTrue same => .isTrue (by cases same; rfl)
    | .isFalse different => .isFalse (fun same => different (Except.ok.inj same))
  | .error a, .error b => match decEq a b with
    | .isTrue same => .isTrue (by cases same; rfl)
    | .isFalse different => .isFalse (fun same => different (Except.error.inj same))
  | .ok _, .error _ => .isFalse (by intro same; cases same)
  | .error _, .ok _ => .isFalse (by intro same; cases same)

private def gate : DefinitionIdentity := ⟨0, 1⟩
private def aux : DefinitionIdentity := ⟨0, 2⟩
private def loopTrait : DefinitionIdentity := ⟨0, 3⟩
private def u32 : Term := .atom .type "uint" "u32"
private def u64 : Term := .atom .type "uint" "u64"
private def wrapper (arg : Term) : Term := .definition .type "adt" ⟨0,100⟩ (.ofArray #[arg])
private def obligation (traitDefinition : DefinitionIdentity) (self : Term) : Clause :=
  ⟨#[], .trait ⟨.positive, ⟨traitDefinition, #[self]⟩⟩⟩
private def implementation (id : Nat) (traitDefinition : DefinitionIdentity)
    (parameters : Array ArgSort) (self : Term)
    (polarity : Polarity := .positive) (isDefault : Bool := false) : Impl := {
  definition := ⟨0,id⟩
  parameters := parameters
  traitRef := ⟨traitDefinition, #[self]⟩
  polarity := polarity
  isDefault := isDefault
  associatedValues := #[] }
private def declaration (identity : DefinitionIdentity) (implementations : Array Impl) : TraitDeclaration := {
  definition := identity
  parameters := #[.type]
  isAuto := false
  isAlias := false
  isUnsafe := false
  isCoinductive := false
  isMarker := false
  langItem := none
  superPredicates := #[]
  implementations := implementations }
private def genericGate : Impl := implementation 20 gate #[.type] (wrapper (.parameter .type 0))
private def program : Program := {traits := #[
  declaration gate #[genericGate],
  declaration aux #[implementation 21 aux #[] u32, implementation 22 aux #[] u64 .negative]]}
private def hooks : Hooks where
  implementationPredicates := fun implementation =>
    if implementation.definition == (⟨0,20⟩ : DefinitionIdentity) then
      .ok #[obligation aux (.parameter .type 0)]
    else if implementation.definition == (⟨0,30⟩ : DefinitionIdentity) then
      .ok #[obligation loopTrait (.parameter .type 0)]
    else .ok #[]
  normalize := fun _ fuel _ term => do Match.requireGround fuel term; pure term
  builtin := fun _ _ _ _ _ => .error "builtin provider not implemented"
  external := fun _ _ _ _ _ => .error "external predicate not implemented"
private def resultClass : Except String Outcome → Except String String
  | .error error => .error error
  | .ok (.proven _) => .ok "proven"
  | .ok .noSolution => .ok "no_solution"
  | .ok (.ambiguous _) => .ok "ambiguous"

example : selectUnique program hooks {} 100 100 ⟨gate, #[wrapper u32]⟩ =
    .ok ⟨⟨0,20⟩, #[u32]⟩ := by decide +kernel
example : resultClass (solve program hooks {} 100 100 ⟨.positive, ⟨gate, #[wrapper u64]⟩⟩) =
    .ok "no_solution" := by decide +kernel
example : resultClass (solve program hooks {} 100 100 ⟨.positive, ⟨gate, #[u32]⟩⟩) =
    .ok "no_solution" := by decide +kernel
example : resultClass (solve program hooks {} 100 100 ⟨.positive, ⟨aux, #[u64]⟩⟩) =
    .ok "no_solution" := by decide +kernel
example : resultClass (solve program hooks {} 100 100 ⟨.negative, ⟨aux, #[u64]⟩⟩) =
    .ok "proven" := by decide +kernel
example : resultClass (solve {traits := #[declaration gate #[genericGate,
    implementation 23 gate #[] (wrapper u32)], declaration aux #[implementation 21 aux #[] u32]]}
    hooks {} 100 100 ⟨.positive, ⟨gate, #[wrapper u32]⟩⟩) = .ok "ambiguous" := by decide +kernel
example : selectUnique {traits := #[declaration gate #[implementation 20 gate #[] u32 .positive true]]}
    hooks {} 100 100 ⟨gate, #[u32]⟩ =
    .error "default impl selection requires specialization semantics" := by decide +kernel
example : resultClass (solve program hooks {} 100 100 ⟨.positive, ⟨⟨99,99⟩, #[u32]⟩⟩) =
    .error "raw trait declaration catalog missing or ambiguous" := by decide +kernel
example : resultClass (solve program hooks {} 0 100 ⟨.positive, ⟨aux, #[u32]⟩⟩) =
    .error "trait selection recursion exhausted" := by decide +kernel
example : resultClass (solve program hooks {} 100 0 ⟨.positive, ⟨aux, #[u32]⟩⟩) =
    .error "trait fulfillment total work exhausted" := by decide +kernel
example : resultClass (solve program hooks {} 100 100 ⟨.positive, ⟨aux, #[]⟩⟩) =
    .error "trait query argument arity mismatch" := by decide +kernel
example : resultClass (fulfill program hooks {} 100 100 #[⟨#[], .equal u32 u64⟩]) =
    .ok "no_solution" := by decide +kernel
example : resultClass (fulfill program hooks {} 100 100 #[⟨#[], .wellFormed u32⟩]) =
    .error "external predicate not implemented" := by decide +kernel
example : resultClass (fulfill program hooks {} 100 100 #[
    ⟨#[.region .anonymous], .trait ⟨.positive, ⟨aux, #[u32]⟩⟩⟩]) =
    .ok "proven" := by decide +kernel
example : resultClass (solve program hooks {assumptions := #[obligation gate u64],eraseRegions := false} 100 100
    ⟨.positive, ⟨gate, #[u64]⟩⟩) = .ok "proven" := by decide +kernel
example : selectUnique program hooks {assumptions := #[obligation gate u64],eraseRegions := false} 100 100 ⟨gate, #[u64]⟩ =
    .error "trait proof does not identify a unique source impl" := by decide +kernel
example : resultClass (solve {traits := #[declaration loopTrait #[implementation 30 loopTrait #[.type]
    (.parameter .type 0)]]} hooks {} 100 100
    ⟨.positive, ⟨loopTrait, #[u32]⟩⟩) = .ok "ambiguous" := by decide +kernel
example : resultClass (solve program hooks {assumptions := #[obligation gate u64],eraseRegions := false} 100 100
    ⟨.positive, ⟨aux, #[wrapper u32]⟩⟩) = .ok "ambiguous" := by decide +kernel

-- A catalog filtered by source constructor scope must never turn an outside
-- constructor into a definite negative, including nested generic arguments.
example : resultClass (solve {program with constructorScope := some #[]} hooks {} 100 100
    ⟨.positive, ⟨aux, #[wrapper u32]⟩⟩) =
    .error "trait query ADT constructor outside closed source declaration scope" := by decide +kernel
example : resultClass (solve {program with constructorScope := some #[⟨0,100⟩]} hooks {} 100 100
    ⟨.positive, ⟨aux, #[wrapper u32]⟩⟩) = .ok "no_solution" := by decide +kernel
example : resultClass (solve {program with constructorScope := some #[⟨0,100⟩]} hooks {} 100 100
    ⟨.positive, ⟨aux, #[wrapper (.definition .type "adt" ⟨0,101⟩ .nil)]⟩⟩) =
    .error "trait query ADT constructor outside closed source declaration scope" := by decide +kernel

private def autoProgram : Program := {traits := #[
  { (declaration gate #[genericGate]) with isAuto := true, isCoinductive := true },
  declaration aux #[implementation 21 aux #[] u32, implementation 22 aux #[] u64 .negative]]}
-- A possible impl suppresses the structural auto candidate before testing its
-- where clauses. The mandatory unknown builtin hook must not be invoked.
example : selectUnique autoProgram hooks {} 100 100 ⟨gate, #[wrapper u32]⟩ =
    .ok ⟨⟨0,20⟩, #[u32]⟩ := by decide +kernel
example : resultClass (solve autoProgram hooks {} 100 100 ⟨.positive, ⟨gate, #[wrapper u64]⟩⟩) =
    .ok "no_solution" := by decide +kernel
example : resultClass (solve autoProgram hooks {} 100 100 ⟨.positive, ⟨gate, #[u32]⟩⟩) =
    .error "builtin provider not implemented" := by decide +kernel
example : resultClass (solve {traits := #[
    { (declaration gate #[implementation 50 gate #[] u32 .negative]) with isAuto := true }]}
    hooks {} 100 100 ⟨.positive, ⟨gate, #[u32]⟩⟩) = .ok "no_solution" := by decide +kernel
private def dynamicAux : Term := .node .type "dynamic" "" (Terms.ofArray #[
  .binder #[] (.definition .aggregate "trait" aux .nil), .atom .region "erased" ""])
example : resultClass (solve program hooks {} 100 100 ⟨.positive, ⟨aux, #[dynamicAux]⟩⟩) =
    .error "dynamic trait goals require object candidate assembly" := by decide +kernel

private def evaluated (ty : Term) : Term := .node .constant "value" "" (.ofArray #[ty,.atom .aggregate "scalar" "{\"bytes\":4,\"bits\":3}"])
example : resultClass (fulfill program hooks {} 100 100 #[⟨#[],.constHasType (evaluated u32) u32⟩]) = .ok "proven" := by decide +kernel
example : resultClass (fulfill program hooks {} 100 100 #[⟨#[],.constHasType (evaluated u32) u64⟩]) = .ok "no_solution" := by decide +kernel
example : resultClass (fulfill program hooks {} 100 100 #[⟨#[],.constHasType (.parameter .constant 0) u32⟩]) = .error "trait matching requires a ground query" := by decide +kernel
example : resultClass (fulfill program hooks {assumptions := #[obligation gate u32]} 100 100
    #[⟨#[],.constHasType (evaluated u32) u64⟩]) = .ok "ambiguous" := by decide +kernel

private def structuralProgram : Program := {traits := #[
  {(declaration gate #[]) with isAuto := true, isCoinductive := true}, declaration aux #[]]}
private def structuralHooks : Hooks := { hooks with builtin := fun _ _ _ _ goal => .ok (some #[⟨#[],.trait goal⟩]) }
example : resultClass (solve structuralProgram structuralHooks {} 100 100
    ⟨.positive,⟨gate,#[u32]⟩⟩) = .ok "proven" := by decide +kernel
private def negativeSiblingHooks : Hooks := {hooks with builtin := fun _ _ _ _ goal => .ok (some #[⟨#[],.trait goal⟩,obligation aux u32])}
example : resultClass (solve structuralProgram negativeSiblingHooks {} 100 100
    ⟨.positive,⟨gate,#[u32]⟩⟩) = .ok "no_solution" := by decide +kernel
example : resultClass (solveWithActive structuralProgram structuralHooks {} 100 100
    #[⟨.positive,⟨gate,#[u32]⟩⟩] ⟨.positive,⟨gate,#[u32]⟩⟩) =
    .ok "ambiguous" := by decide +kernel

private def inheritedProgram : Program := {traits := #[
  {(declaration gate #[]) with superPredicates := #[obligation aux (.parameter .type 0)]},
  declaration aux #[]]}
example : resultClass (solve inheritedProgram hooks {assumptions := #[obligation gate u32]}
    100 100 ⟨.positive,⟨aux,#[u32]⟩⟩) = .ok "proven" := by decide +kernel
example : resultClass (solve inheritedProgram hooks {assumptions := #[obligation gate u32]}
    100 100 ⟨.positive,⟨aux,#[u64]⟩⟩) = .ok "ambiguous" := by decide +kernel
example : resultClass (solveWithSourceParameters inheritedProgram hooks
    {assumptions := #[obligation gate (.parameter .type 0)]} #[.type]
    100 100 ⟨.positive,⟨aux,#[.parameter .type 0]⟩⟩) = .ok "proven" := by decide +kernel
example : resultClass (solveWithSourceParameters inheritedProgram hooks
    {assumptions := #[]} #[.type]
    100 100 ⟨.positive,⟨aux,#[.parameter .type 0]⟩⟩) = .ok "ambiguous" := by decide +kernel
