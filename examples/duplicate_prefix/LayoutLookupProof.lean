import duplicate_prefix.NodeLookupProof
import Lean

namespace DuplicatePrefix.LayoutLookupProof
open Miri.Input Miri.ABI
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def firstInsert {Row Value : Type} (key : Row → TypeId) (value : Row → Value)
    (entries : Std.HashMap TypeId Value) (row : Row) :=
  if entries.contains (key row) then entries else entries.insert (key row) (value row)

theorem list_lookup {Row Value : Type} (key : Row → TypeId) (value : Row → Value)
    (rows : List Row) (entries : Std.HashMap TypeId Value) (id : TypeId) :
    (Id.run (forIn rows entries (fun row state => pure (.yield (firstInsert key value state row)))))[id]? =
      (entries[id]?).orElse (fun _ => (rows.find? (fun row => key row == id)).map value) := by
  induction rows generalizing entries with
  | nil => simp [List.forIn_nil]
  | cons row rows ih =>
    simp only [List.forIn_cons, Id.run, pure, bind, Id.instMonad]
    simp only [Id.run, pure, bind] at ih
    rw [ih]
    unfold firstInsert
    cases held : entries[id]? <;> by_cases same : key row = id <;>
      by_cases stored : entries.contains (key row) <;>
      simp_all [-Std.HashMap.isSome_getElem?_eq_contains, List.find?, Std.HashMap.contains_eq_isSome_getElem?,
        Std.HashMap.getElem?_insert, Option.orElse]
    all_goals
      have different : (key row == id) = false := by simpa using same
      rw [different]

open Lean Elab Tactic in
elab "unfold_layout_table" : tactic => do
  let env ← getEnv
  let found := env.constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith (".canonicalLayoutLookup" : String) then some (mkIdent name) else none
  match found with
  | [name] => evalTactic (← `(tactic| unfold $name:ident))
  | _ => throwError "expected exact canonicalLayoutLookup source"

theorem layout_table_lookup
    (layouts : Array (TypeId × Except RuntimeMetadataError (TyAndLayout TypeId))) (id : TypeId) :
    (RuntimeLayoutLookupCache.build layouts).entries[id]? =
      (layouts.find? (fun row => row.1 == id)).map Prod.snd := by
  unfold RuntimeLayoutLookupCache.build
  unfold_layout_table
  simp only [← Array.forIn_toList]
  have callback :
      (fun (row : TypeId × Except RuntimeMetadataError (TyAndLayout TypeId)) entries =>
        if !(entries.contains row.1) then
          (pure (ForInStep.yield (entries.insert row.1 row.2)) : Id _)
        else pure (ForInStep.yield entries)) =
      (fun row entries => pure (ForInStep.yield (firstInsert Prod.fst Prod.snd entries row))) := by
    funext row entries
    cases flag : entries.contains row.1 <;> simp [flag, firstInsert]
  rw [callback]
  simpa [Id.run, bind, pure] using (list_lookup Prod.fst Prod.snd layouts.toList {} id)

theorem indexed_lookup_eq (metadata : RuntimeMetadata)
    (certificate : Option (RuntimeMetadata.JsonReflexivity metadata.source.raw)) (id : TypeId) :
    (RuntimeMetadata.Indexed.ofMetadata metadata certificate).lookup id = metadata.lookup id := by
  have entries : (RuntimeMetadata.Indexed.ofMetadata metadata certificate).layoutIndex[id]? =
      match metadata.layoutCache with
      | some cache => cache.entries[id]?
      | none => (metadata.layouts.find? (fun row => row.1 == id)).map Prod.snd := by
    cases cached : metadata.layoutCache with
    | none =>
      simpa [RuntimeMetadata.Indexed.ofMetadata, cached, Id.run, pure, Id.instMonad] using layout_table_lookup metadata.layouts id
    | some cache => simp [RuntimeMetadata.Indexed.ofMetadata, cached, Id.run, pure, Id.instMonad]
  unfold RuntimeMetadata.Indexed.lookup RuntimeMetadata.lookup
  rw [entries]
  rfl

#print axioms indexed_lookup_eq
open Lean Elab Command in
run_cmd do
  for declaration in [``list_lookup, ``layout_table_lookup, ``indexed_lookup_eq] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"

#print axioms layout_table_lookup
end DuplicatePrefix.LayoutLookupProof
