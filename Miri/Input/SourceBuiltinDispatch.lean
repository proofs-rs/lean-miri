import Miri.Input.TraitSelection.Match

/-! Pinned candidate_assembly.rs::assemble_candidates dispatch. A language item
marks a compiler-known trait, not necessarily a compiler-generated impl.
The finite manual-only list is the pinned trait LangItem inventory excluding
all actual builtin assembly arms. Inventory: rustc_attr_ir/src/lang_items.rs,
pin 8144389c895da997dbdecaa635e41d6a50be6ffd. Dispatch and fallback:
rustc_trait_selection/src/traits/select/candidate_assembly.rs::assemble_candidates.
Excluded arms: Copy/Clone/TrivialClone, DiscriminantKind, Pointee, Sized/MetaSized/
PointeeSized, Unsize, Destruct, Transmute, Tuple, FnPtrTrait,
BikeshedGuaranteedNoDrop, TryAsDyn, Field; plus Fn/AsyncFn families and
AsyncFnKindHelper. CoerceUnsized and DispatchFromDyn have no assembly arm
in this pinned selector: their ordinary impl catalog is searched normally.
Auto traits still use their separate provider. Conditional candidate helpers
are assemble_{coroutine,future,iterator,fused_iterator,async_iterator}_candidates:
only Coroutine heads enter those builtin paths. Coroutine kind/confirmation
remains unsupported here, including generator Iterator/FusedIterator and async
Future/AsyncIterator. No missing builtin is treated as a negative trait answer.
Iterator/Future/etc only have coroutine-head builtin candidates; this module
proves their absence for checked ground non-coroutine heads, never a trait goal.
Unported coroutine/dyn/alias/inference cases remain errors. -/
namespace Miri.Input.SourceBuiltinDispatch
open GenericSubstitution TraitSelection
inductive Decision where
  | existingProvider | noCompilerCandidate
  deriving Repr, DecidableEq, BEq
private def manualOnly : Array String := #[
    "structural_peq","use_cloned","sync","freeze","unsafe_unpin","drop",
    "async_drop","coerce_unsized","dispatch_from_dyn","add","sub","mul",
    "div","rem","neg","not","bitxor","bitand",
    "bitor","shl","shr","add_assign","sub_assign","mul_assign",
    "div_assign","rem_assign","bitxor_assign","bitand_assign","bitor_assign","shl_assign",
    "shr_assign","index","index_mut","va_arg_safe","deref","deref_mut",
    "deref_pure","receiver","legacy_receiver","fn_static","unpin","eq",
    "partial_ord","termination","Try","coerce_pointee_validated","const_param_ty","default_trait4",
    "default_trait3","default_trait2","default_trait1","reborrow","coerce_shared","From"]
private def coroutineConditional : Array String :=
  #["iterator","fused_iterator","future_trait","async_iterator","coroutine"]
private def nonCoroutine (fuel : Nat) (self : Term) (languageItem : String) : Except String Unit := do
  Match.requireGround fuel self
  match self with
  | .definition .type "coroutine" .. =>
    throw s!"compiler builtin {languageItem} on Coroutine requires source kind and confirmation provider"
  | .definition .type tag _ _ =>
    unless ["adt","foreign","function_definition","closure","coroutine_closure","coroutine_witness"].contains tag do
      throw "conditional compiler builtin requires a classified ground Self head"
  | .node .type "dynamic" .. => throw "dynamic trait goals require object candidate assembly"
  | .node .type tag _ _ =>
    unless ["tuple","array","slice","raw_pointer","reference","function_pointer","pattern","unsafe_binder"].contains tag do
      throw "conditional compiler builtin requires a classified ground Self head"
  | .atom .type tag _ =>
    unless ["bool","char","int","uint","float","str","never"].contains tag do
      throw "conditional compiler builtin requires a classified ground Self head"
  | _ => throw "conditional compiler builtin requires a classified ground Self head"

def classify (fuel : Nat) (declaration : TraitDeclaration) (arguments : Array Term) :
    Except String Decision := do
  if declaration.isAuto then return .existingProvider
  let some languageItem := declaration.langItem | return .noCompilerCandidate
  if manualOnly.contains languageItem then return .noCompilerCandidate
  if coroutineConditional.contains languageItem then
    unless declaration.parameters.size == arguments.size do
      throw "conditional compiler builtin canonical argument arity mismatch"
    for (sort,argument) in declaration.parameters.zip arguments do
      unless sort == argument.sort do throw "conditional compiler builtin argument sort mismatch"
      Match.requireGround fuel argument
    let some self := arguments[0]? | throw "conditional compiler builtin Self absent"
    nonCoroutine fuel self languageItem
    return .noCompilerCandidate
  if declaration.builtin.isSome then return .existingProvider
  throw s!"unimplemented compiler builtin language trait: {languageItem}"
end Miri.Input.SourceBuiltinDispatch
