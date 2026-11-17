import duplicate_prefix.GeneralBorrowFreshRootScopedRow
import duplicate_prefix.S03EmptyPopFactsAuthorization
import duplicate_prefix.S04ReturnReleaseParent

namespace DuplicatePrefix.S04ReturnWildcardRestore
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality DuplicatePrefixResidualSupportAuthorization
open DuplicatePrefixCallbackAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- The fresh hidden return root is a secondary root. Once its protector is
gone, its zero-contributor callback is authorized for either access kind.
No particular final permission (Unique, Frozen or Disabled) is required. -/
theorem leaf_callback (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (graph : GeneralBorrowStructuralHistoryState.GraphState tree)
    (root : UniIndex) (node : TreeNode) (present : tree.nodeAt root = some node)
    (leaf : node.children = #[]) (hidden : node.isExposed = false)
    (position : Nat) (secondary : position ≠ 0) (kind : AccessKind)
    (possible : ((location.perms.get root).getD node.defaultLocationState).possible = true)
    (absent : protections.contains node.tag = false) :
    Authorization tree location protections root position none kind (fun index => index = root) := by
  have zero := S03EmptyPopFactsAuthorization.leaf_cardinality tree location protections graph root node present leaf hidden kind
  refine ⟨rfl,?_,?_,?_,?_,?_,?_⟩
  · intro index same
    subst index
    exact ⟨node,present⟩
  · intro index value same found child member
    subst index
    have eq : value = node := Option.some.inj (found.symm.trans present)
    subst value
    rw [leaf] at member
    simp at member
  · intro index same
    subst index
    intro row member walked
    exact walked
  · intro index value same found
    subst index
    have eq : value = node := Option.some.inj (found.symm.trans present)
    subst value
    exact possible
  · intro before after legalBefore legalAfter subset index value same found retained
    subst index
    have eq : value = node := Option.some.inj (found.symm.trans present)
    subst value
    have beforeEmpty := no_maximum_removal_empty tree location protections kind before legalBefore
    have afterEmpty := no_maximum_removal_empty tree location protections kind after legalAfter
    subst before
    subst after
    have classification : residualRelation tree location protections root root node none kind position [] = some .ForeignAccess := by
      simp [residualRelation,residual_empty,zero,classify,secondary,aboveMaximum]
    rw [classification]
    refine ⟨possible,?_⟩
    by_cases skipped : skip ((location.perms.get root).getD node.defaultLocationState) kind .ForeignAccess = true
    · exact Or.inl skipped
    · apply Or.inr
      refine ⟨by simpa using skipped,?_⟩
      cases kind <;> simp [DuplicatePrefixScalarAuthorization.Compatible,
        GeneralBorrowProtectedReadCompatible.Compatible,
        GeneralBorrowExposedConditionalWritePermissions.Compatible,absent,possible]
  · intro impossible
    exact False.elim (secondary impossible)

/-- Reinterpret the saved old-root callback supports after a hidden isolated
return root has lost its protector. Older roots retain their original support;
the additional root receives its own harmless foreign callback. -/
theorem row (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (graph : GeneralBorrowStructuralHistoryState.GraphState tree)
    (root : UniIndex) (tag : BorTag) (node : TreeNode)
    (present : tree.nodeAt root = some node) (leaf : node.children = #[])
    (hidden : node.isExposed = false) (absent : protections.contains node.tag = false)
    (notPrimary : ∀ valid : 0 < tree.roots.size, tree.roots[0] ≠ root)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location)
    (old : GeneralBorrowFreshRootScopedRow.Row tree location protections root root tag) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Row tree location protections none none none) := by
  refine ⟨{wildcard := fun _ => rfl,rootPath := ?_,rootPresent := ?_,cutoff := rfl,normal := ?_,callbacks := ?_}⟩
  · intro anchor impossible
    cases impossible
  · intro anchor impossible
    cases impossible
  · intro anchor impossible
    cases impossible
  · intro position valid different
    by_cases same : tree.roots[position] = root
    · have secondary : position ≠ 0 := by
        intro zero
        subst position
        exact notPrimary valid same
      have possibleRoot := possible root node present
      refine ⟨(fun index => index = root),?_,?_⟩
      all_goals rw [same]
      · exact leaf_callback tree location protections graph root node present leaf hidden position secondary .Read possibleRoot absent
      · exact leaf_callback tree location protections graph root node present leaf hidden position secondary .Write possibleRoot absent
    · obtain ⟨support,bounded,read,write⟩ := old.callbacks position valid (Ne.symm same)
      exact ⟨support,
        (GeneralBorrowFreshRootSupportCutoff.authorization_iff tree location protections tag old.exposed _ position .Read support bounded).mpr read,
        (GeneralBorrowFreshRootSupportCutoff.authorization_iff tree location protections tag old.exposed _ position .Write support bounded).mpr write⟩

/-- Full original wildcard capability from the current saved scoped capability
and the actual hidden-root shape. This consumes no wildcard success or future
Positive premise. The saved bounds concern exposed nodes and old supports only,
so later hidden helper tags may exceed the return tag. -/
theorem positive (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (root : UniIndex) (tag : BorTag) (offset len : UInt64) (node : TreeNode)
    (present : tree.nodeAt root = some node) (leaf : node.children = #[])
    (parentless : node.parent = none)
    (hidden : node.isExposed = false) (absent : global.protectedTags.contains node.tag = false)
    (notPrimary : ∀ valid : 0 < tree.roots.size, tree.roots[0] ≠ root)
    (old : GeneralBorrowFreshRootScopedRow.Positive tree global.protectedTags root root tag offset len) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Positive tree global.protectedTags none none none offset len) := by
  have nonempty : 0 < tree.roots.size := by
    have member := runtime.formed.covered root node present parentless
    have positive := List.length_pos_of_mem member
    simpa only [Array.length_toList] using positive
  refine ⟨{positive := old.base.positive,bounds := old.base.bounds,sourcePresent := ?_,wildcardRoot := fun _ => nonempty,rows := ?_}⟩
  · intro anchor impossible
    cases impossible
  · intro position valid positive start stop
    obtain ⟨oldRow⟩ := old.rows position valid positive start stop
    exact row tree _ global.protectedTags runtime.formed.toGraphState root tag node present leaf hidden absent notPrimary
      (runtime.possible position valid) oldRow

end DuplicatePrefix.S04ReturnWildcardRestore
