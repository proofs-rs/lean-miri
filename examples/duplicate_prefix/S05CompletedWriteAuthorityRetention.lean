import duplicate_prefix.S05CompletedAncestryReadMutable
import duplicate_prefix.S05RawAuthorityStepPreservation

namespace DuplicatePrefix.S05CompletedWriteAuthorityRetention
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowExposedNonleafPrimaryPath
open GeneralBorrowWildcardParentTagOrder GeneralBorrowExposureCardinality
open DuplicatePrefixResidualSupportAuthorization DuplicatePrefixCallbackAuthorization OrdinaryBorrowAuthority
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem origin_root (tree : BorrowTree) (completion : Completion)
    (initial : LocationTree) (protections : ProtectedTags)
    (complete : Completes tree completion) (order : ParentTagOrder tree)
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
    (below : Below completion query source) :
    ∃ witness witnessNode, tree.nodes.get witness = some witnessNode ∧
      Supports initial protections witness witnessNode (some selectedNode.tag) .Write ∧
      Path tree query witness ∧ Below completion witness source := by
  obtain ⟨rootNode,rootPresent,rootParentless⟩ := complete.2.2.2.1 rootPosition root rootSlot
  obtain ⟨selected,selectedFound,selectedParentless⟩ := complete.2.2.2.1 selectedPosition selectedRoot selectedSlot
  have same : selected = selectedNode := Option.some.inj (selectedFound.symm.trans selectedPresent)
  subst selected
  obtain ⟨witness,witnessNode,witnessPresent,exposed,witnessPath,_,witnessBelow,bound⟩ :=
    CompletedBorrowAncestry.cross_root_origin complete order rootPresent rootParentless selectedPresent
      selectedParentless present different queryPath selectedPath below
  refine ⟨witness,witnessNode,witnessPresent,⟨exposed,?_,?_⟩,witnessPath,witnessBelow⟩
  · exact GeneralBorrowExposedConditionalWritePermissions.local_allows _ _ (localRights witness witnessNode witnessPresent (CompletedBorrowAncestry.path_trans queryPath witnessPath) witnessBelow)
  · simpa only [Option.isNone_some,Option.any_some,Bool.false_or,decide_eq_true_eq] using bound

theorem query_shape (tree : BorrowTree) (completion : Completion)
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
    (removed : List UniIndex)
    (legal : Removal tree initial protections (some selectedNode.tag) .Write removed) :
    let classification := residualRelation tree initial protections root query node (some selectedNode.tag) .Write rootPosition removed
    (Below completion query source → classification = some .LocalAccess ∨ classification = some .EitherAccess) ∧
      (¬Below completion query source → classification = some .ForeignAccess ∨ classification = some .EitherAccess) := by
  dsimp only
  have covered := GeneralBorrowSharedAuthorizationGeometry.covers_of_path tree depth root query queryPath
  have eligibleOrigin := origin_root tree completion initial protections complete order rootPosition selectedPosition
    root selectedRoot source query node selectedNode rootSlot selectedSlot selectedPresent different selectedPath queryPath present localRights
  obtain ⟨rootNode,rootPresent,_⟩ := complete.2.2.2.1 rootPosition root rootSlot
  have primary : rootPosition = 0 → ∃ witness witnessNode,
      tree.nodes.get witness = some witnessNode ∧
      Supports initial protections witness witnessNode (some selectedNode.tag) .Write ∧
      Path tree root witness ∧ Below completion witness source := by
    intro zero
    exact origin_root tree completion initial protections complete order rootPosition selectedPosition
      root selectedRoot source root rootNode selectedNode rootSlot selectedSlot selectedPresent different selectedPath
      (.refl root rootNode rootPresent) rootPresent localRights
      (CompletedBorrowAncestry.root_zero_below complete (by simpa only [zero] using rootSlot) selectedSlot selectedPath)
  have positive : 0 < residualCount tree initial protections .Write removed root +
      if rootPosition != 0 then 1 else 0 := by
    by_cases zero : rootPosition = 0
    · obtain ⟨witness,witnessNode,lookup,eligible,path,_⟩ := primary zero
      have positive := GeneralBorrowResidualPrimaryWitness.positive tree initial protections depth
        (some selectedNode.tag) .Write removed legal root witness witnessNode lookup eligible path
      simpa [zero] using positive
    · simp only [show (rootPosition != 0) = true by simp [zero],ite_true]
      omega
  have nonzero : ((residualCount tree initial protections .Write removed root +
      if rootPosition != 0 then 1 else 0) == 0) = false := by
    apply Bool.eq_false_iff.mpr
    intro equal
    exact (Nat.ne_of_gt positive) (beq_iff_eq.mp equal)
  constructor
  · intro below
    obtain ⟨witness,witnessNode,lookup,eligible,path,_⟩ := eligibleOrigin below
    have localPositive := GeneralBorrowResidualPrimaryWitness.positive tree initial protections depth
      (some selectedNode.tag) .Write removed legal query witness witnessNode lookup eligible path
    have localNonzero : (residualCount tree initial protections .Write removed query == 0) = false := by simp [Nat.ne_of_gt localPositive]
    have unclamped := path_not_above tree order initial protections (some selectedNode.tag) .Write
      query witness node witnessNode present lookup path eligible
    by_cases equal : residualCount tree initial protections .Write removed root +
        (if rootPosition != 0 then 1 else 0) = residualCount tree initial protections .Write removed query
    · have equalBool : ((residualCount tree initial protections .Write removed root +
          if rootPosition != 0 then 1 else 0) == residualCount tree initial protections .Write removed query) = true := beq_iff_eq.mpr equal
      simp only [residualRelation,unclamped,classify,nonzero,equalBool,Bool.false_eq_true,↓reduceIte]
      simp
    · have equalBool : ((residualCount tree initial protections .Write removed root +
          if rootPosition != 0 then 1 else 0) == residualCount tree initial protections .Write removed query) = false := by
        apply Bool.eq_false_iff.mpr
        intro same
        exact equal (beq_iff_eq.mp same)
      simp only [residualRelation,unclamped,classify,nonzero,localNonzero,equalBool,Bool.false_eq_true,↓reduceIte]
      simp
  · intro below
    have unequal : residualCount tree initial protections .Write removed root +
        (if rootPosition != 0 then 1 else 0) ≠ residualCount tree initial protections .Write removed query := by
      intro equal
      by_cases zero : rootPosition = 0
      · obtain ⟨witness,witnessNode,lookup,eligible,path,witnessBelow⟩ := primary zero
        have outside : query ∉ GeneralBorrowExposureAncestorFold.walk tree.nodes (tree.nodes.size+1) witness := by
          intro member
          have physical := S05RawGrantAuthorizationClosure.path_of_walk tree depth _ query witness witnessNode lookup member
          exact below (CompletedBorrowAncestry.below_trans (CompletedBorrowAncestry.physical_below complete physical) witnessBelow)
        have strict := S05CutoffOwnershipGeometry.residual_strict tree initial protections depth root query witness
          witnessNode lookup (some selectedNode.tag) .Write removed legal eligible path outside covered
        simp only [zero,bne_self_eq_false,Bool.false_eq_true,ite_false,Nat.add_zero] at equal
        omega
      · have bounded : residualCount tree initial protections .Write removed query ≤ residualCount tree initial protections .Write removed root := by
          exact DuplicatePrefixResidualWriteSkip.residual_dominates tree initial protections removed root query covered
        have virtual : (rootPosition != 0) = true := by simp [zero]
        simp only [virtual,ite_true] at equal
        omega
    have unequalBool : ((residualCount tree initial protections .Write removed root +
        if rootPosition != 0 then 1 else 0) == residualCount tree initial protections .Write removed query) = false := by
      apply Bool.eq_false_iff.mpr
      intro same
      exact unequal (beq_iff_eq.mp same)
    simp only [residualRelation,classify,nonzero,unequalBool,Bool.false_eq_true,↓reduceIte]
    cases aboveMaximum node (some selectedNode.tag) <;>
      cases zero : (residualCount tree initial protections .Write removed query == 0) <;>
      simp only [Bool.false_eq_true,↓reduceIte]
    all_goals simp


/-- The actual scalar Write poststep retains its matching source-relative right.
Recording is consumed as an intermediate production-step equation. -/
theorem local_post (before recorded after : LocationState) (held : Bool) (delta : PermTransition)
    (initial : LocalWrite before held)
    (record : before.recordNewAccess .Write .LocalAccess = .Recorded recorded)
    (access : recorded.performAccess .Write .LocalAccess held = .Success after delta) :
    LocalWrite after held := by
  have kept := S05RawAuthorityStepPreservation.record_local before recorded held .Write .LocalAccess initial record
  obtain ⟨next,change,actual,right⟩ := S05RawAuthorityStepPreservation.local_step recorded held .Write kept
  have equal := access.symm.trans actual
  cases equal
  exact right

theorem foreign_post (before recorded after : LocationState) (held : Bool) (delta : PermTransition)
    (initial : ForeignWrite before held)
    (record : before.recordNewAccess .Write .ForeignAccess = .Recorded recorded)
    (access : recorded.performAccess .Write .ForeignAccess held = .Success after delta) :
    ForeignWrite after held := by
  have kept := S05RawAuthorityStepPreservation.record_foreign before recorded held .Write .ForeignAccess initial record
  obtain ⟨next,change,actual,right⟩ := S05RawAuthorityStepPreservation.foreign_step recorded held .Write kept
  have equal := access.symm.trans actual
  cases equal
  exact right


theorem materialized_authority (tree : BorrowTree) (completion : Completion)
    (current : LocationTree) (protections : ProtectedTags) (source index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node)
    (authority : S05CompletedAncestryReadMutable.Authority tree completion protections source current) :
    S05CompletedAncestryReadMutable.Authority tree completion protections source
      (GeneralBorrowWildcardVirtualLeaf.materialized current index node) := by
  intro query found lookup
  have eq := GeneralBorrowExposedVirtualSchedule.materialized_effective tree current index node present query found lookup
  change (Below completion query source → LocalWrite (GeneralBorrowWildcardVirtualLeaf.effective _ query found) _) ∧
    (¬Below completion query source → ForeignWrite (GeneralBorrowWildcardVirtualLeaf.effective _ query found) _)
  rw [eq]
  exact authority query found lookup

set_option maxHeartbeats 200000 in
/-- The production optional-slot write retains every current source-relative
scalar right once its exact query has the completed-ancestry shape. -/
theorem updated_authority (tree : BorrowTree) (completion : Completion)
    (current : LocationTree) (protections : ProtectedTags) (source index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node)
    (authority : S05CompletedAncestryReadMutable.Authority tree completion protections source current)
    (exact : AccessRelatedness) (recorded next : LocationState) (delta : PermTransition)
    (localShape : Below completion index source → exact = .LocalAccess)
    (foreignShape : ¬Below completion index source → exact = .ForeignAccess)
    (record : ((current.perms.get index).getD node.defaultLocationState).recordNewAccess .Write exact = .Recorded recorded)
    (access : recorded.performAccess .Write exact (protections.contains node.tag) = .Success next delta) :
    S05CompletedAncestryReadMutable.Authority tree completion protections source
      (GeneralBorrowExposedNonleafState.updated tree current index node protections recorded next delta) := by
  intro query found lookup
  by_cases same : query = index
  · subst query
    have eq : found = node := Option.some.inj (lookup.symm.trans present)
    subst found
    have raw : RawState (GeneralBorrowExposedNonleafState.updated tree current index node protections recorded next delta) index node = next := by
      unfold CandidateStableCallOwnership.RawState
      dsimp only [GeneralBorrowExposedNonleafState.updated]
      rw [GeneralBorrowWildcardSubtreeState.write_same]
      rfl
    rw [raw]
    by_cases below : Below completion index source
    · have relation := localShape below
      subst exact
      exact ⟨fun _ => local_post _ _ _ _ _ ((authority index node present).1 below) record access,
        fun outside => False.elim (outside below)⟩
    · have relation := foreignShape below
      subst exact
      exact ⟨fun inside => False.elim (below inside),
        fun _ => foreign_post _ _ _ _ _ ((authority index node present).2 below) record access⟩
  · have frame := GeneralBorrowExposedNonleafState.updated_other tree current index query node protections recorded next delta same
    simpa only [CandidateStableCallOwnership.RawState, frame] using authority query found lookup

end DuplicatePrefix.S05CompletedWriteAuthorityRetention

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05CompletedWriteAuthorityRetention." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved completed Write retention dependency {dependency}"
