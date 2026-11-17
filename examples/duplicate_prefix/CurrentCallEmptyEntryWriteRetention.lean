import duplicate_prefix.S05CompletedWriteAuthorityDFS

/-! Retention for the finite empty-entry callback. This exposes the existing
repaired DFS's internal geometry interface without a post-entry Completes gate.
The endpoint derives classification from its exact old-tree/orphan effect. -/
namespace DuplicatePrefix.CurrentCallEmptyEntryWriteRetention
open Lean Lean.Elab Lean.Elab.Term
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixResidualCountModel
open DuplicatePrefixResidualSupportAuthorization (Removal residualRelation residualCount)
open GeneralBorrowProjection
open CandidateStableCallOwnership
open GeneralBorrowWildcardSubtreeData (Weights)
open DuplicatePrefixResidualWriteWitnessPlan
open DuplicatePrefixResidualWriteRepaired (Authorization)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

elab "empty_retained_write_kernel" : term => do
  let names := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith ".S05CompletedWriteAuthorityDFS.access_with_geometry" then some name else none
  match names with
  | [name] => Lean.Meta.mkConstWithFreshMVarLevels name
  | _ => throwError "expected unique checked repaired Write retention kernel"

theorem callback (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag)
    (weights : Weights tree) (rootBound : weights.weight root ≤ tree.nodes.size)
    (support : GeneralBorrowWildcardControlStack.Support tree root)
    (plan : Plan tree initial protections root rootPosition maximum)
    (authorization : Authorization tree initial protections root rootPosition maximum .Write support.contains)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree initial protections).topology)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (short : tree.nodes.size < 65536)
    (initialProfile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (initialPossible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial)
    (completion : Completion) (source : UniIndex)
    (classification : ∀ removed, Removal tree initial protections maximum .Write removed →
      ∀ index node, support.contains index → tree.nodes.get index = some node →
      let query := residualRelation tree initial protections root index node maximum .Write rootPosition removed
      (CandidateStableCallOwnership.Below completion index source → query = some .LocalAccess ∨ query = some .EitherAccess) ∧
      (¬CandidateStableCallOwnership.Below completion index source → query = some .ForeignAccess ∨ query = some .EitherAccess))
    (initialAuthority : S05CompletedAncestryReadMutable.Authority tree completion protections source initial) :
    let result := tree.performWildcardAccessAt initial root maximum .Write protections (rootPosition != 0)
    result.status = .Completed ∧ ∃ removed,
      Removal tree initial protections maximum .Write removed ∧
      Matches tree initial result.location protections .Write removed ∧
      GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
      (∀ query, ¬support.contains query → result.location.perms.get query = initial.perms.get query) ∧
      GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
      (∀ query, tree.nodes.get query = none → result.location.perms.get query = initial.perms.get query) ∧
      S05CompletedAncestryReadMutable.Authority tree completion protections source result.location := by
  exact empty_retained_write_kernel tree initial protections root rootPosition maximum weights rootBound support plan
    authorization depth forest coherent short initialProfile initialPossible completion source classification initialAuthority

/-- Form the real callback plan from repaired clauses, retaining the supplied
internally derived source-relative rights on the SAME actual row. -/
theorem root (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree) (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (root : UniIndex) (position : Nat) (maximum : Option BorTag)
    (support : UniIndex → Prop)
    (auth : Authorization tree initial protections root position maximum .Write support)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections) (short : tree.nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial)
    (completion : Completion) (source : UniIndex)
    (classification : ∀ removed,Removal tree initial protections maximum .Write removed →
      ∀ index node,support index → tree.nodes.get index = some node →
      let query := residualRelation tree initial protections root index node maximum .Write position removed
      (Below completion index source → query = some .LocalAccess ∨ query = some .EitherAccess) ∧
      (¬Below completion index source → query = some .ForeignAccess ∨ query = some .EitherAccess))
    (authority : S05CompletedAncestryReadMutable.Authority tree completion protections source initial) :
    let result := tree.performWildcardAccessAt initial root maximum .Write protections (position != 0)
    result.status = .Completed ∧ GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
      (∀ query,¬support query → result.location.perms.get query = initial.perms.get query) ∧
      S05CompletedAncestryReadMutable.Authority tree completion protections source result.location := by
  obtain ⟨forest⟩ := formed.forest initial protections
  have graph := GeneralBorrowExposedScopedReciprocal.of_forest tree initial protections forest depth
  let weights := GeneralBorrowWildcardForestWeights.of_forest tree initial protections forest
  let area : GeneralBorrowWildcardControlStack.Support tree root := ⟨support,auth.rooted,auth.present,auth.children⟩
  have plans : Nonempty (Plan tree initial protections root position maximum) := by
    by_cases zero : position = 0
    · obtain ⟨witness,node,included,present,eligible⟩ := auth.witness zero
      have path := GeneralBorrowWildcardControlWitness.path_of_covers tree depth root witness node present (auth.covers witness included)
      subst position
      exact ⟨DuplicatePrefixResidualVisibleWritePlan.ordered tree initial protections root maximum depth graph short witness node present
        (GeneralBorrowPrimaryWitnessVisibility.of_order tree order initial protections maximum .Write witness node present eligible) eligible path⟩
    · exact ⟨DuplicatePrefixResidualWriteWitnessPlan.virtual tree initial protections root position maximum zero⟩
  obtain ⟨plan⟩ := plans
  obtain ⟨done,_,_,_,cache,outside,sifa,gp,_,rights⟩ := callback tree initial protections root position maximum weights
    (GeneralBorrowWildcardForestWeights.bounded tree initial protections forest root) area plan auth depth forest coherent short profile possible
    completion source classification authority
  exact ⟨done,cache,sifa,gp,outside,rights⟩

/-- Exact masked queries and legal masks survive the finite constructor's
permission metadata frame. The endpoint derives this frame from its actual
hidden nodes and SIFA effect, on the SAME current scalar row. -/
theorem metadata_query (before after : BorrowTree) (oldLocation newLocation : LocationTree)
    (protections : ProtectedTags) (depth : GeneralBorrowExposure.ParentDepth before.nodes)
    (size : before.nodes.size ≤ after.nodes.size)
    (metadata : ∀ index node,before.nodes.get index = some node →
      ∃ next,after.nodes.get index = some next ∧ next.parent = node.parent ∧
        next.tag = node.tag ∧ next.isExposed = node.isExposed ∧
        ((newLocation.perms.get index).getD next.defaultLocationState).permission =
        ((oldLocation.perms.get index).getD node.defaultLocationState).permission)
    (back : ∀ index next,after.nodes.get index = some next → next.isExposed = true →
      ∃ node,before.nodes.get index = some node)
    (root query : UniIndex) (position : Nat) (maximum : Option BorTag) (node : TreeNode)
    (removed : List UniIndex) (legal : Removal after newLocation protections maximum .Write removed) :
    Removal before oldLocation protections maximum .Write removed ∧
      residualRelation after newLocation protections root query node maximum .Write position removed =
      residualRelation before oldLocation protections root query node maximum .Write position removed := by
  have count (index : UniIndex) : residualCount after newLocation protections .Write removed index =
      residualCount before oldLocation protections .Write removed index := by
    apply GeneralBorrowSharedAuthorizationExtension.masked_count_extension before after oldLocation newLocation
      protections depth size _ back removed index .Write
    intro index node found
    obtain ⟨next,lookup,parent,tag,exposed,permission⟩ := metadata index node found
    exact ⟨next,lookup,parent,exposed,by simp only [GeneralBorrowExposureCardinality.effective,tag,permission]⟩
  refine ⟨⟨legal.distinct,?_⟩,?_⟩
  · intro index member
    obtain ⟨next,found,allowed⟩ := legal.allowed index member
    have exposed : next.isExposed = true := by
      cases flag : next.isExposed
      · simp only [DuplicatePrefixResidualSupportAuthorization.removable,flag,Bool.false_and,Bool.false_eq_true] at allowed
      · rfl
    obtain ⟨original,oldPresent⟩ := back index next found exposed
    obtain ⟨actual,actualAt,parent,tag,exposure,permission⟩ := metadata index original oldPresent
    have same := Option.some.inj (actualAt.symm.trans found)
    subst actual
    refine ⟨original,oldPresent,?_⟩
    simpa only [DuplicatePrefixResidualSupportAuthorization.removable,GeneralBorrowExposureCardinality.effective,
      DuplicatePrefixCallbackAuthorization.aboveMaximum,tag,exposure,permission] using allowed
  · simp only [residualRelation,count]

end DuplicatePrefix.CurrentCallEmptyEntryWriteRetention
open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CurrentCallEmptyEntryWriteRetention." then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved empty repaired retention dependency {dependency}"
