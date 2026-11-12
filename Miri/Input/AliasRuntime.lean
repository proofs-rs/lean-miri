import Miri.Input.AliasMaterialProgram
import Miri.Input.GenericInstantiation
import Miri.Input.MirTemplate
import Miri.Input.StructuralSized
import Miri.Input.StructuralAutoTraits
import Miri.Input.TraitSelection.Fulfill

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

/-- One shared builtin/external-predicate dictionary for alias normalization and
standalone raw trait queries. Normalization is a mandatory recursive dependency. -/
def traitHooks (context : Context) (depth : Nat)
    (normalize : Nat → Array TraitSelection.Goal → Term → Except String Term) :
    TraitSelection.Hooks := {

      normalize := normalize
      builtin := fun remaining activeGoals declaration goal => do
        let some kind := declaration.builtin | throw "unimplemented raw lang-item/auto-trait builtin"
        unless goal.traitRef.arguments.size == 1 do throw "structural builtin requires exactly Self"
        let some self := goal.traitRef.arguments[0]? | throw "structural builtin Self absent"
        let ty ← GenericInstantiation.resolveType context.generic depth self
        let lookup := fun id => do
          let source ← TypeArena.node context.generic.types id context.generic.constants.size
          match source.shape with
          | .alias .. =>
            let term ← GenericInstantiation.ofType context.generic depth id
            let normalized ← normalize remaining activeGoals term
            let id ← GenericInstantiation.resolveType context.generic depth normalized
            return (← TypeArena.node context.generic.types id context.generic.constants.size).shape
          | _ => pure source.shape
        match kind with
        | .sized | .metaSized =>
          let kind := if kind == .sized then StructuralSized.TraitKind.sized else .metaSized
          let some answer ← StructuralSized.queryKind kind lookup (remaining + 1) ty
            | throw "structural Sized builtin has unresolved source alias"
          pure (if answer then some #[] else none)
        | .freeze | .unpin | .unsafeUnpin =>
          if ← StructuralAutoTraits.trivial lookup (remaining + 1) ty then return some #[]
          throw "nontrivial auto-trait builtin requires complete structural candidate assembly"
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
  let source ← TypeArena.node context.generic.types id context.generic.constants.size
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
