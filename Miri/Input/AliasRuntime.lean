import Miri.Input.SourceEnvironmentRuntime
import Miri.Input.AliasMaterialProgram
import Miri.Input.GenericInstantiation
import Miri.Input.MirTemplate
import Miri.Input.StructuralSized
import Miri.Input.TermSized
import Miri.Input.TraitSelection.Fulfill
import Miri.Input.TraitSelection.StructuralCopyClone
import Miri.Input.TraitSelection.StructuralAuto

/-! Executable composition of source alias RHS reduction and the raw trait
selection/fulfillment engine. The supported domain is a fully monomorphic,
region-erasing, empty parameter environment. Region erasure occurs before and
after normalization, as in rustc_traits/normalize_erasing_regions.rs. The current
eraser explicitly rejects binders; this module makes no higher-ranked or opaque
inference claim. No normalized type or selected-impl answer catalog is read. -/
namespace Miri.Input.AliasRuntime
open GenericSubstitution

structure Context where
  generic : GenericInstantiation.Context
  aliases : AliasNormalization.Program
  traits : TraitSelection.Program

def Context.ofDocument (source : ImportDocument) :
    Except String Context := do
  let generic ← GenericInstantiation.Context.ofDocument source
  let mut declarations := #[]
  for definition in source.definitions do
    if let some declaration := definition.aliasDeclaration then
      unless declaration.definition == (⟨definition.crateIndex,definition.index⟩ : DefinitionIdentity) do
        throw "runtime alias source identity mismatch"
      declarations := declarations.push (declaration,definition.genericTemplate)
  let aliases ← AliasMaterial.program declarations
  pure ⟨generic,aliases,source.traitProgram⟩

private def requireProven (value : TraitSelection.Outcome) : Except String Unit :=
  match value with
  | .proven _ => pure ()
  | .noSolution => throw "alias normalization own predicates have no solution"
  | .ambiguous reason => throw s!"alias normalization own predicates are ambiguous: {reason}"

/-- Canonical declaration adapter shared by production trait queries and
independent term-sizedness correspondence tests. No instantiated TypeId or
compiler-computed Sized constraint is needed for a novel ADT expression. -/
def sourceAdt (context : Context) (identity : DefinitionIdentity) :
    Except String (AdtDeclaration.Material × DefinitionTemplate) := do
  let reference ← GenericInstantiation.definitionRef context.generic identity
  let some definition := context.generic.definitions[reference]?
    | throw "term trait ADT definition absent"
  let some material := definition.adtDeclaration
    | throw "term Sized canonical ADT declaration absent"
  let some template := definition.genericTemplate
    | throw "term trait canonical ADT generic template absent"
  material.validate template
  pure (material,template)

def sizedHooks (context : Context) (normalize : Nat → Term → Except String Term) :
    TermSized.Hooks := {
  sourceAdt := fun identity => do
    let (material,template) ← sourceAdt context identity
    pure (material.kind,template),
  normalizeAlias := normalize }

/-- One shared builtin/external-predicate dictionary for alias normalization and
standalone raw trait queries. Normalization is a mandatory recursive dependency. -/
def traitHooks (context : Context) (_depth : Nat)
    (normalize : Nat → Array TraitSelection.Goal → Term → Except String Term) :
    TraitSelection.Hooks := {
      implementationPredicates := fun implementation => do
        let lookup := SourceEnvironmentRuntime.lookupDefinitions context.generic.definitions
        let material ← lookup implementation.definition
        unless material.parameters == implementation.parameters do
          throw "impl generic header differs from its canonical raw source scope"
        SourceEnvironment.predicates lookup 16384 implementation.definition
      normalize := normalize
      builtin := fun remaining activeGoals declaration goal => do
        unless goal.traitRef.arguments.size == 1 do throw "structural builtin requires exactly Self"
        let some self := goal.traitRef.arguments[0]? | throw "structural builtin Self absent"
        if declaration.isAuto then
          let some constituents ← TraitSelection.StructuralAuto.query (sourceAdt context)
              declaration.isUnsafe (remaining + 1) self
            | return none
          return some (constituents.map fun ty =>
            ({variables := #[], predicate := (.trait ⟨.positive,⟨goal.traitRef.definition,#[ty]⟩⟩)} : TraitSelection.Clause))
        let some kind := declaration.builtin | throw "unimplemented raw lang-item builtin"
        match kind with
        | .sized | .metaSized =>
          let kind := if kind == .sized then StructuralSized.TraitKind.sized else .metaSized
          let answer ← TermSized.query
            (sizedHooks context (fun fuel term => normalize fuel activeGoals term))
            kind (remaining + 1) self
          return if answer then some #[] else none
        | _ => pure ()
        match kind with
        | .copy | .clone =>
          let some constituents ← TraitSelection.StructuralCopyClone.query (remaining + 1) self
            | return none
          return some (constituents.map fun ty =>
            ({variables := #[], predicate := (.trait ⟨.positive,⟨goal.traitRef.definition,#[ty]⟩⟩)} : TraitSelection.Clause))
        | .freeze | .unpin | .unsafeUnpin => return none
        | _ => throw "unimplemented structural trait builtin"
      external := fun remaining activeGoals _ predicate => do
        match predicate with
        | .projection .projectionType definition arguments expected =>
          let projection := Term.definition .type "alias_projection_not_rigid" definition (Terms.ofArray arguments)
          let actual ← normalize remaining activeGoals projection
          let expected ← normalize remaining activeGoals expected
          if actual = expected then pure (.proven (.equality actual)) else pure .noSolution
        | _ => throw "unimplemented alias normalization predicate semantics"  }

/-- Recursive alias/trait composition shares both active stacks and decreases an
outer depth bound through callback re-entry. Trait calls also retain the engine's
explicit work bound. Unknown builtins/predicates fail instead of gaining evidence. -/
def normalizeTerm (context : Context) (work : Nat) :
    Nat → Array AliasNormalization.Key → Array TraitSelection.Goal → Term → Except String Term
  | 0, _, _, _ => .error "runtime alias/trait recursion exhausted"
  | fuel + 1, aliases, goals, input => do
    let input ← MirTemplate.eraseFreeRegions (fuel + 1) input
    MirTemplate.validateClosed (fuel + 1) input
    let currentTraitHooks (activeAliases : Array AliasNormalization.Key) :=
      traitHooks context (fuel + 1)
        (fun _ activeGoals term => normalizeTerm context work fuel activeAliases activeGoals term)
    let environment : TraitSelection.Environment := {eraseRegions := true}
    let aliasHooks : AliasNormalization.Hooks := {
      ownPredicates := fun definition => do
        let material ← SourceEnvironmentRuntime.lookupDefinitions context.generic.definitions definition
        pure material.ownPredicates
      select := fun remaining activeAliases kind parent arguments => do
        unless kind == .projection do throw "inherent associated alias selection is not implemented"
        let selection ← TraitSelection.selectUniqueWithActive context.traits (currentTraitHooks activeAliases)
          environment (min remaining fuel) work goals ⟨parent,arguments⟩
        let implementations := context.traits.traits.flatMap (·.implementations)
          |>.filter (·.definition == selection.implementation)
        unless implementations.size == 1 do throw "selected raw impl declaration absent or duplicated"
        let some implementation := implementations[0]? | throw "selected raw impl declaration absent"
        AliasNormalization.fromTraitSelection implementation selection
      fulfill := fun remaining activeAliases predicates => do
        requireProven (← TraitSelection.fulfillWithActive context.traits (currentTraitHooks activeAliases)
          environment (min remaining fuel) work goals predicates) }
    let result ← AliasNormalization.normalize context.aliases aliasHooks (fuel + 1) aliases input
    let result ← MirTemplate.eraseFreeRegions (fuel + 1) result
    MirTemplate.validateClosed (fuel + 1) result
    pure result

def normalizeType (context : Context) (depth work : Nat) (id : TypeId) : Except String TypeId := do
  let source ← TypeArena.node context.generic.types id
  let query := source.layoutQueryInputTypeId.getD id
  let input ← GenericInstantiation.ofType context.generic depth query
  let result ← normalizeTerm context work depth #[] #[] input
  GenericInstantiation.resolveType context.generic depth result

def solveGoal (context : Context) (depth work : Nat) (goal : TraitSelection.Goal) :
    Except String TraitSelection.Outcome :=
  TraitSelection.solve context.traits
    (traitHooks context depth (fun remaining goals term =>
      normalizeTerm context work remaining #[] goals term))
    {eraseRegions := true} depth work goal

def selectGoal (context : Context) (depth work : Nat) (goal : TraitSelection.TraitRef) :
    Except String TraitSelection.ImplSelection :=
  TraitSelection.selectUnique context.traits
    (traitHooks context depth (fun remaining goals term =>
      normalizeTerm context work remaining #[] goals term))
    {eraseRegions := true} depth work goal

end Miri.Input.AliasRuntime
