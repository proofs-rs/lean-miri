import duplicate_prefix.DuplicatePrefixResidualPostchildrenNoop

/-! Entry expansion needs no legacy authorization: PendingSaved stores the
CURRENT removal mask and its entry skip=false. Later children may change the
cache/classification; only the pending node's optional permission slot remains
untouched. This is local invariant preservation, not child execution or a
complete revised DFS. The actual entry loop below is exposed once; no equality
between independently chosen existential loop bodies is assumed. -/
namespace DuplicatePrefix.DuplicatePrefixResidualEntryExpand
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization
open DuplicatePrefixResidualCountModel DuplicatePrefixResidualSavedWriteDFSInvariant
open DuplicatePrefixResidualWriteWitnessPlan GeneralBorrowResidualSavedWriteRuntime
open GeneralBorrowWildcardVirtualLeaf (effective)
open GeneralBorrowWildcardSubtreeData (Weights)
open GeneralBorrowWildcardSubtreeStack GeneralBorrowProjection
open DuplicatePrefixCallbackVisitAuthorization (entrySkip)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-- The old expand proof's used premises only: no Authorization or initial
cache-coherence assumption is needed to save the actual current entry mask. -/
theorem expand {tree : BorrowTree} {initial current : LocationTree} {protections : ProtectedTags}
    {root : UniIndex} {position : Nat} {maximum : Option BorTag}
    (weights : Weights tree) (support : GeneralBorrowWildcardControlStack.Support tree root)
    (plan : Plan tree initial protections root position maximum)
    (short : tree.nodes.size < 65536)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree initial protections).topology)
    (witness : Bool) (stack : Array Task) (index : UniIndex) (node : TreeNode) (steps : Nat)
    (valid : RuntimeInvariant (initial := initial) (protections := protections)
      (rootPosition := position) (maximum := maximum) weights support plan
      (current,witness,.Completed,stack.push (index,false),steps))
    (present : tree.nodes.get index = some node)
    (recurse : entrySkip (effective current index node) .Write
      (relation current root index node maximum .Write position) = false) :
    RuntimeInvariant (initial := initial) (protections := protections)
      (rootPosition := position) (maximum := maximum) weights support plan
      (current,witness,.Completed,expanded stack index node.children,steps+1) := by
  obtain ⟨base,profile,possible,vacant⟩ := valid
  have unvisited := top_unvisited weights support plan current witness stack index node false steps base present
  obtain ⟨removed,legal,matching,pending⟩ := base.model
  have savedActive : entrySkip (effective initial index node) .Write
      (residualRelation tree initial protections root index node maximum .Write position removed) = false := by
    rw [←relation_matches tree initial current protections .Write removed matching base.coherent short root index node maximum position]
    simpa only [effective,unvisited] using recurse
  obtain ⟨disjoint,untouched⟩ := GeneralBorrowWildcardUntouched.expand_actual tree initial protections forest
    initial current stack index node present base.disjoint base.untouched
  refine ⟨⟨rfl,⟨removed,legal,matching,?_⟩,base.coherent,
    GeneralBorrowWildcardControlStack.expand weights support stack index node steps base.control present,
    disjoint,untouched,base.outside,plan.expand witness stack index node present base.witness⟩,profile,possible,vacant⟩
  intro query queryNode member found
  simp only [expanded,Array.toList_append,Array.toList_push,Array.toList_map,List.mem_append] at member
  rcases member with old | child
  · rcases old with earlier | currentTask
    · exact pending query queryNode (by simp [earlier]) found
    · have same : query = index := by simpa using currentTask
      subst query
      have nodeEq := Option.some.inj (present.symm.trans found)
      subst queryNode
      exact ⟨removed,legal,(fun _ member => member),savedActive⟩
  · obtain ⟨child,childMember,impossible⟩ := List.mem_map.mp child
    simp at impossible

/-- The real previsit expands on any skip=false query, including None/Either.
It neither materializes nor records, and leaves current cache/witness intact.
This exposes the actual core body, not a surrogate transition. -/
theorem actual_entry (tree : BorrowTree) (initial : LocationTree) (root : UniIndex)
    (maximum : Option BorTag) (protections : ProtectedTags) (position : Nat) :
    ∃ scan : Unit → LoopState → Id (ForInStep LoopState),
      (tree.performWildcardAccessAt initial root maximum .Write protections (position != 0) =
        let final := Lean.Loop.forIn {} (initial,false,.Completed,#[(root,false)],0) scan
        ⟨final.1,if final.2.2.1 == .Completed && !final.2.1 && !(position != 0) then
          .NoValidExposedReferences root none else final.2.2.1⟩) ∧
      ∀ (current : LocationTree) (witness : Bool) (stack : Array Task)
        (index : UniIndex) (node : TreeNode) (steps : Nat),
        tree.nodes.get index = some node → ¬steps+1 > tree.nodes.size*2+1 →
        entrySkip (effective current index node) .Write
          (relation current root index node maximum .Write position) = false →
        scan () (current,witness,.Completed,stack.push (index,false),steps) =
          .yield (current,witness,.Completed,expanded stack index node.children,steps+1) := by
  unfold BorrowTree.performWildcardAccessAt
  simp only [Id.run,bind,pure,ForIn.forIn]
  name_range_scan
  refine ⟨scan,?_,?_⟩
  · split <;> rfl
  · intro current witness stack index node steps present budget recurse
    have related := relation_source current root index node maximum .Write position
    unfold aboveMaximum at related
    have physical (exact : AccessRelatedness)
        (noSkip : DuplicatePrefixCallbackAuthorization.skip (effective current index node) .Write exact = false) :
        (effective current index node).skipIfKnownNoop .Write exact = .Recurse := by
      cases skipped : (effective current index node).skipIfKnownNoop .Write exact with
      | Recurse => rfl
      | SkipSelfAndChildren =>
        have yes := (skip_source _ _ _).mpr skipped
        simp [noSkip] at yes
    have bounded : ¬tree.nodes.size*2 < steps := by omega
    have pushing := children_loop node.children (stack.push (index,true))
    simp only [forIn'_eq_forIn,pure] at pushing
    simp only [scan]
    simp only [budget]
    unfold_leaf_helpers
    cases maximum <;>
      simp_all [entrySkip,DuplicatePrefixCallbackAuthorization.skip,effective,
        expanded,pushing,bounded,Id.run,bind,pure]
    all_goals cases query : current.exposedCache.accessRelatedness root index .Write (position != 0) _ <;> simp_all
    all_goals rename_i relatedness
    all_goals cases relatedness
    all_goals unfold_leaf_helpers
    all_goals simp_all [entrySkip,physical,effective,expanded,pushing,bounded,Id.run,bind,pure]

end DuplicatePrefix.DuplicatePrefixResidualEntryExpand
