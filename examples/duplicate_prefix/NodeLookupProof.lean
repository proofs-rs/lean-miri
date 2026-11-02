import Miri.Input.RuntimeMetadata
import Std.Data.HashMap.Lemmas
import Init.Data.List.Monadic

namespace DuplicatePrefix.NodeLookupProof
open Miri.Input
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def firstInsert {Value : Type} (key : Value → TypeId)
    (entries : Std.HashMap TypeId Value) (node : Value) :=
  if entries.contains (key node) then entries else entries.insert (key node) node

theorem list_lookup {Value : Type} (key : Value → TypeId)
    (nodes : List Value) (entries : Std.HashMap TypeId Value) (id : TypeId) :
    (Id.run (forIn nodes entries (fun node state => pure (.yield (firstInsert key state node)))))[id]? =
      (entries[id]?).orElse (fun _ => nodes.find? (fun node => key node == id)) := by
  induction nodes generalizing entries with
  | nil => simp [List.forIn_nil]
  | cons node nodes ih =>
    simp only [List.forIn_cons, Id.run, pure, bind, Id.instMonad]
    simp only [Id.run, pure, bind] at ih
    rw [ih]
    unfold firstInsert
    cases held : entries[id]? <;> by_cases same : key node = id <;>
      by_cases stored : entries.contains (key node) <;>
      simp_all [-Std.HashMap.isSome_getElem?_eq_contains, List.find?, Std.HashMap.contains_eq_isSome_getElem?,
        Std.HashMap.getElem?_insert, Option.orElse]
    all_goals
      have different : (key node == id) = false := by simpa using same
      rw [different]

open Lean Elab Tactic in
elab "unfold_node_table" : tactic => do
  let env ← getEnv
  let found := env.constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith (".canonicalNodeLookup" : String) then some (mkIdent name) else none
  match found with
  | [name] => evalTactic (← `(tactic| unfold $name:ident))
  | _ => throwError "expected exact canonicalNodeLookup source"

theorem node_table_lookup (nodes : Array TypeNode) (id : TypeId) :
    (RuntimeNodeLookupCache.build nodes).entries[id]? = nodes.find? (·.id == id) := by
  unfold RuntimeNodeLookupCache.build
  unfold_node_table
  simp only [← Array.forIn_toList]
  have callback :
      (fun (node : TypeNode) (entries : Std.HashMap TypeId TypeNode) =>
        if !(entries.contains node.id) then
          (pure (ForInStep.yield (entries.insert node.id node)) : Id _)
        else pure (ForInStep.yield entries)) =
      (fun node entries => pure (ForInStep.yield (firstInsert (·.id) entries node))) := by
    funext node entries
    cases flag : entries.contains node.id <;> simp [flag, firstInsert]
  rw [callback]
  simpa [Id.run, bind, pure] using (list_lookup (·.id) nodes.toList {} id)



theorem indexed_node (metadata : RuntimeMetadata) (id : TypeId)
    (certificate : Option (RuntimeMetadata.JsonReflexivity metadata.source.raw)) :
    (RuntimeMetadata.Indexed.ofMetadata metadata certificate).node id = metadata.node id := by
  cases cached : metadata.nodeCache <;>
    simp [RuntimeMetadata.Indexed.ofMetadata, RuntimeMetadata.Indexed.node,
      RuntimeMetadata.node, cached, node_table_lookup]

#print axioms list_lookup
#print axioms node_table_lookup
#print axioms indexed_node

end DuplicatePrefix.NodeLookupProof
