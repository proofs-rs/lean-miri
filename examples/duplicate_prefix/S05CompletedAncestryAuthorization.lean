import duplicate_prefix.CompletedBorrowAncestry
import duplicate_prefix.S05RawGrantAuthorizationClosure
import duplicate_prefix.GeneralBorrowSharedAuthorizationGeometry

/-! One-mask Write adequacy for the explicitly unadopted completed-ancestry
model. Actual exposed attachments and their cutoff eligibility are derived
from its graph clauses and independent raw scalar rights. This is neither
ordinary-input coverage nor transport across a source Read or child traversal. -/
namespace DuplicatePrefix.S05CompletedAncestryAuthorization
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowExposedNonleafPrimaryPath
open GeneralBorrowWildcardParentTagOrder GeneralBorrowExposureCardinality
open DuplicatePrefixResidualSupportAuthorization DuplicatePrefixCallbackAuthorization
open OrdinaryBorrowAuthority
set_option autoImplicit false
set_option maxHeartbeats 3000000

private theorem local_support (state : LocationState) (held : Bool)
    (right : LocalWrite state held) :
    (state.permission.strongestAllowedLocalAccess held).allows .Write = true := by
  cases permission : state.permission with
  | ReservedFrz conflicted =>
    cases conflicted <;> cases held <;>
      simp_all [LocalWrite,Permission.strongestAllowedLocalAccess,WildcardAccessLevel.allows]
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
    cases held <;> simp_all [LocalWrite,Permission.strongestAllowedLocalAccess,WildcardAccessLevel.allows]

/-- For a callback on another physical root, completed ancestry and current
raw LocalWrite/ForeignWrite tables suffice for every legal residual mask and
any entry classification. No exposed-supporter or authorization premise is
supplied: the completion graph itself yields the retained attachment.
The actual selected root fixes the cutoff, independently of root array order. -/
theorem authorized_root_local (tree : BorrowTree) (completion : Completion)
    (initial : LocationTree) (protections : ProtectedTags)
    (complete : Completes tree completion)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (rootPosition selectedPosition : Nat) (root selectedRoot source query : UniIndex)
    (node selectedNode : TreeNode)
    (rootSlot : tree.roots[rootPosition]? = some root)
    (selectedSlot : tree.roots[selectedPosition]? = some selectedRoot)
    (selectedPresent : tree.nodes.get selectedRoot = some selectedNode)
    (different : root ≠ selectedRoot)
    (selectedPath : Path tree selectedRoot source) (queryPath : Path tree root query)
    (present : tree.nodes.get query = some node)
    (localRights : ∀ index found, tree.nodes.get index = some found → Path tree root index →
      Below completion index source → LocalWrite
        ((initial.perms.get index).getD found.defaultLocationState) (protections.contains found.tag))
    (foreignRights : ∀ index found, tree.nodes.get index = some found → Path tree root index →
      ¬ Below completion index source → ForeignWrite
        ((initial.perms.get index).getD found.defaultLocationState) (protections.contains found.tag))
    (consistent : GeneralBorrowSifaPermissionConsistency.Consistent
      ((initial.perms.get query).getD node.defaultLocationState) (protections.contains node.tag))
    (removed : List UniIndex)
    (legal : Removal tree initial protections (some selectedNode.tag) .Write removed)
    (entry : Option WildcardAccessRelatedness) :
    DuplicatePrefixCallbackVisitAuthorizationRepaired.Authorized
      ((initial.perms.get query).getD node.defaultLocationState) .Write (protections.contains node.tag)
      entry (residualRelation tree initial protections root query node (some selectedNode.tag) .Write rootPosition removed) := by
  obtain ⟨rootNode,rootPresent,rootParentless⟩ := complete.2.2.2.1 rootPosition root rootSlot
  obtain ⟨selected,selectedFound,selectedParentless⟩ := complete.2.2.2.1 selectedPosition selectedRoot selectedSlot
  have same : selected = selectedNode := Option.some.inj (selectedFound.symm.trans selectedPresent)
  subst selected
  have covered := GeneralBorrowSharedAuthorizationGeometry.covers_of_path tree depth root query queryPath
  have origin : ∀ index found, tree.nodes.get index = some found → Path tree root index →
      Below completion index source → ∃ witness witnessNode,
      tree.nodes.get witness = some witnessNode ∧
      Supports initial protections witness witnessNode (some selectedNode.tag) .Write ∧
      Path tree index witness ∧ Below completion witness source := by
    intro index found lookup path below
    obtain ⟨witness,witnessNode,witnessPresent,exposed,witnessPath,_,witnessBelow,bound⟩ :=
      CompletedBorrowAncestry.cross_root_origin complete order rootPresent rootParentless selectedPresent
        selectedParentless lookup different path selectedPath below
    refine ⟨witness,witnessNode,witnessPresent,⟨exposed,?_,?_⟩,witnessPath,witnessBelow⟩
    · exact local_support _ _ (localRights witness witnessNode witnessPresent (CompletedBorrowAncestry.path_trans path witnessPath) witnessBelow)
    · simpa only [Option.isNone_some,Option.any_some,Bool.false_or,decide_eq_true_eq] using bound
  have primary : rootPosition = 0 → ∃ witness witnessNode,
      tree.nodes.get witness = some witnessNode ∧
      Supports initial protections witness witnessNode (some selectedNode.tag) .Write ∧
      Path tree root witness ∧ Below completion witness source := by
    intro zero
    have below := CompletedBorrowAncestry.root_zero_below complete
      (by simpa only [zero] using rootSlot) selectedSlot selectedPath
    exact origin root rootNode rootPresent (.refl root rootNode rootPresent) below
  have positive : 0 < residualCount tree initial protections .Write removed root +
      if rootPosition != 0 then 1 else 0 := by
    by_cases zero : rootPosition = 0
    · obtain ⟨witness,witnessNode,lookup,eligible,path,_⟩ := primary zero
      have supported := GeneralBorrowResidualPrimaryWitness.positive tree initial protections depth
        (some selectedNode.tag) .Write removed legal root witness witnessNode lookup eligible path
      simpa only [zero,bne_self_eq_false,Bool.false_eq_true,ite_false,Nat.add_zero] using supported
    · simp only [show (rootPosition != 0) = true by simp [zero],ite_true]
      omega
  have nonzero : ((residualCount tree initial protections .Write removed root +
      if rootPosition != 0 then 1 else 0) == 0) = false := by
    apply Bool.eq_false_iff.mpr
    intro equal
    exact (Nat.ne_of_gt positive) (beq_iff_eq.mp equal)
  by_cases below : Below completion query source
  · have raw := localRights query node present queryPath below
    obtain ⟨witness,witnessNode,lookup,eligible,path,_⟩ := origin query node present queryPath below
    have localPositive := GeneralBorrowResidualPrimaryWitness.positive tree initial protections depth
      (some selectedNode.tag) .Write removed legal query witness witnessNode lookup eligible path
    have localNonzero : (residualCount tree initial protections .Write removed query == 0) = false := by
      simp [Nat.ne_of_gt localPositive]
    have unclamped := path_not_above tree order initial protections (some selectedNode.tag) .Write
      query witness node witnessNode present lookup path eligible
    apply DuplicatePrefixCallbackVisitAuthorizationRepaired.old_inclusion
    refine ⟨raw.1,Or.inr ?_⟩
    by_cases equal : residualCount tree initial protections .Write removed root +
        (if rootPosition != 0 then 1 else 0) = residualCount tree initial protections .Write removed query
    · have equalBool : ((residualCount tree initial protections .Write removed root +
          if rootPosition != 0 then 1 else 0) == residualCount tree initial protections .Write removed query) = true := beq_iff_eq.mpr equal
      simp only [residualRelation,unclamped,classify,nonzero,equalBool,Bool.false_eq_true,↓reduceIte]
      exact ⟨by simp [skip,AccessRelatedness.isForeign],OrdinaryBorrowAuthorityBridge.local_scalar _ _ raw .Write⟩
    · have equalBool : ((residualCount tree initial protections .Write removed root +
          if rootPosition != 0 then 1 else 0) == residualCount tree initial protections .Write removed query) = false := by
        apply Bool.eq_false_iff.mpr
        intro same
        exact equal (beq_iff_eq.mp same)
      simp only [residualRelation,unclamped,classify,nonzero,localNonzero,equalBool,Bool.false_eq_true,↓reduceIte]
  · have raw := foreignRights query node present queryPath below
    have unequal : residualCount tree initial protections .Write removed root +
        (if rootPosition != 0 then 1 else 0) ≠ residualCount tree initial protections .Write removed query := by
      intro equal
      by_cases zero : rootPosition = 0
      · obtain ⟨witness,witnessNode,lookup,eligible,path,witnessBelow⟩ := primary zero
        have counts : residualCount tree initial protections .Write removed query =
            residualCount tree initial protections .Write removed root := by simpa [zero] using equal.symm
        have physical := S05RawGrantAuthorizationClosure.equal_counts_path tree initial protections depth
          (some selectedNode.tag) removed legal root query witness witnessNode lookup eligible path covered counts
        exact below (CompletedBorrowAncestry.below_trans (CompletedBorrowAncestry.physical_below complete physical) witnessBelow)
      · have bounded := DuplicatePrefixResidualWriteSkip.residual_dominates tree initial protections removed root query covered
        have virtual : (rootPosition != 0) = true := by simp [zero]
        simp only [virtual,ite_true] at equal
        omega
    have foreign := S05RawForeignAuthorizationBridge.foreign_write_authorized _ _ entry consistent raw
    have either : DuplicatePrefixCallbackVisitAuthorizationRepaired.Authorized
        ((initial.perms.get query).getD node.defaultLocationState) .Write (protections.contains node.tag)
        entry (some .EitherAccess) := .inl ⟨raw.1,Or.inr trivial⟩
    have unequalBool : ((residualCount tree initial protections .Write removed root +
        if rootPosition != 0 then 1 else 0) == residualCount tree initial protections .Write removed query) = false := by
      apply Bool.eq_false_iff.mpr
      intro same
      exact unequal (beq_iff_eq.mp same)
    simp only [residualRelation,classify,nonzero,unequalBool,Bool.false_eq_true,↓reduceIte]
    cases aboveMaximum node (some selectedNode.tag) <;>
      cases zero : (residualCount tree initial protections .Write removed query == 0) <;>
      simp only [Bool.false_eq_true,↓reduceIte]
    all_goals first | exact foreign | exact either

/-- Original global-table API, preserved as a specialization of root-local
authority. Other physical roots do not supply this callback's supporters. -/
theorem authorized (tree : BorrowTree) (completion : Completion)
    (initial : LocationTree) (protections : ProtectedTags)
    (complete : Completes tree completion)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (rootPosition selectedPosition : Nat) (root selectedRoot source query : UniIndex)
    (node selectedNode : TreeNode)
    (rootSlot : tree.roots[rootPosition]? = some root)
    (selectedSlot : tree.roots[selectedPosition]? = some selectedRoot)
    (selectedPresent : tree.nodes.get selectedRoot = some selectedNode)
    (different : root ≠ selectedRoot)
    (selectedPath : Path tree selectedRoot source) (queryPath : Path tree root query)
    (present : tree.nodes.get query = some node)
    (localRights : ∀ index found, tree.nodes.get index = some found →
      Below completion index source → LocalWrite
        ((initial.perms.get index).getD found.defaultLocationState) (protections.contains found.tag))
    (foreignRights : ∀ index found, tree.nodes.get index = some found →
      ¬ Below completion index source → ForeignWrite
        ((initial.perms.get index).getD found.defaultLocationState) (protections.contains found.tag))
    (consistent : GeneralBorrowSifaPermissionConsistency.Consistent
      ((initial.perms.get query).getD node.defaultLocationState) (protections.contains node.tag))
    (removed : List UniIndex)
    (legal : Removal tree initial protections (some selectedNode.tag) .Write removed)
    (entry : Option WildcardAccessRelatedness) :
    DuplicatePrefixCallbackVisitAuthorizationRepaired.Authorized
      ((initial.perms.get query).getD node.defaultLocationState) .Write (protections.contains node.tag)
      entry (residualRelation tree initial protections root query node (some selectedNode.tag) .Write rootPosition removed) := by
  exact authorized_root_local tree completion initial protections complete depth order rootPosition selectedPosition
    root selectedRoot source query node selectedNode rootSlot selectedSlot selectedPresent different selectedPath
    queryPath present (fun index found lookup _ below => localRights index found lookup below)
    (fun index found lookup _ outside => foreignRights index found lookup outside) consistent removed legal entry

end DuplicatePrefix.S05CompletedAncestryAuthorization
