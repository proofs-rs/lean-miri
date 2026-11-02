import duplicate_prefix.CurrentCallEmptyEntryBool
import duplicate_prefix.CurrentCallEmptyEntryLenZeroTransport
import duplicate_prefix.CurrentCallEmptyEntryLenZeroOldRootQueries

namespace DuplicatePrefix.CurrentCallEmptyEntryLenZeroFactoryQueries
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowExposedNonleafPrimaryPath S05ConcreteProtectedChildCompletion
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] UniValMap.insert

/-- Instantiate the original repaired factory on the SAME arbitrary current
row after the two actual empty helpers. Old roots use their original support;
the orphan component is supplied separately by the immediate consumer. -/
theorem old_queries {tree : BorrowTree} {completion : Completion} {protections : ProtectedTags}
    {source : UniIndex} {qTag tag1 tag2 : BorTag}
    (factory : CurrentCallEmptyEntryBool.OrphanWriteFactory tree completion protections source qTag)
    (first : EmptyForestSharedPool.Input tree qTag tag1)
    (second : EmptyForestSharedPool.Input first.after tag1 tag2)
    (firstParent : first.parent = factory.orphan) (secondParent : second.parent = first.index)
    (parentless : first.parentNode.parent = none)
    (noIncoming1 : ∀ (query predecessor : UniIndex),completion.parents[query.toNat]? = some (some predecessor) → predecessor ≠ first.index)
    (noIncoming2 : ∀ (query predecessor : UniIndex),(extend completion first.index first.parent).parents[query.toNat]? = some (some predecessor) → predecessor ≠ second.index)
    (sourceNode middleSourceNode : TreeNode)
    (sourceAt : tree.nodes.get source = some sourceNode)
    (middleSourceAt : first.after.nodes.get source = some middleSourceNode)
    (current : LocationTree)
    (authority : S05CompletedAncestryReadMutable.Authority second.after
      (extend (extend completion first.index first.parent) second.index second.parent) protections source current)
    (position : Nat) (root : UniIndex) (rootSlot : tree.roots[position]? = some root)
    (notSelected : root ≠ factory.selected) (notOrphan : root ≠ factory.orphan)
    (consistent : ∀ index node,second.after.nodes.get index = some node → Path second.after root index →
      GeneralBorrowSifaPermissionConsistency.Consistent ((current.perms.get index).getD node.defaultLocationState)
        (protections.contains node.tag)) :
    Nonempty (CurrentCallEmptyEntryBool.WriteQueries second.after
      (extend (extend completion first.index first.parent) second.index second.parent) protections
      source root position (some factory.selectedNode.tag) current) := by
  have middleAuthority := CurrentCallEmptyEntryLenZeroTransport.authority_back first.after
    (extend completion first.index first.parent) protections tag1 tag2 second source middleSourceNode middleSourceAt
    noIncoming2 current authority
  have beforeAuthority := CurrentCallEmptyEntryLenZeroTransport.authority_back tree completion protections qTag tag1
    first source sourceNode sourceAt noIncoming1 current middleAuthority
  have different : root ≠ first.parent := by simpa only [firstParent] using notOrphan
  have beforeConsistent : ∀ index node,tree.nodes.get index = some node → Path tree root index →
      GeneralBorrowSifaPermissionConsistency.Consistent ((current.perms.get index).getD node.defaultLocationState)
        (protections.contains node.tag) := by
    intro index node present path
    exact consistent index node
      ((CurrentCallEmptyEntryLenZeroOldRootFrame.nodes first second secondParent parentless root index different path).trans present)
      (CurrentCallEmptyEntryLenZeroOldRootFrame.paths first second root index path)
  obtain ⟨old⟩ := factory.callbacks current beforeAuthority position root rootSlot notSelected beforeConsistent
  obtain ⟨auth,classification⟩ := CurrentCallEmptyEntryLenZeroOldRootQueries.queries first second secondParent
    parentless current protections root position (some factory.selectedNode.tag) .Write old.support different old.path
    old.authorization completion (extend (extend completion first.index first.parent) second.index second.parent)
    source old.classification (by
      intro query _
      exact (CurrentCallEmptyEntryLenZeroTransport.ancestry_iff first.after (extend completion first.index first.parent)
        tag1 tag2 second source middleSourceNode middleSourceAt noIncoming2 query).trans
        (CurrentCallEmptyEntryLenZeroTransport.ancestry_iff tree completion qTag tag1 first source sourceNode sourceAt noIncoming1 query))
  exact ⟨⟨old.support,auth,fun query included => CurrentCallEmptyEntryLenZeroOldRootFrame.paths first second root query
    (old.path query included),classification⟩⟩

end DuplicatePrefix.CurrentCallEmptyEntryLenZeroFactoryQueries

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallEmptyEntryLenZeroFactoryQueries" then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved old-root factory dependency {dependency}"
