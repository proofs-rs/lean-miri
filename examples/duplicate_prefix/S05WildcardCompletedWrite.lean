import duplicate_prefix.S05WildcardCompletedWriteQueries
import duplicate_prefix.S05CompletedWriteAuthorityDFS
import duplicate_prefix.S05CompletedAncestryReadMutable
import duplicate_prefix.GeneralBorrowLoop
import duplicate_prefix.GeneralBorrowConcreteRangeEntry

/-! Actual wildcard Write at every physical root with maximum NONE. One fixed
exposed grant supplies current mutable authority throughout the whole scan.
There is no concrete normal phase, skipped selected root, or substituted cutoff.
This is a sufficient current representation model, not ordinary admission. -/
namespace DuplicatePrefix.S05WildcardCompletedWrite
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowExposedNonleafPrimaryPath OrdinaryBorrowAuthority
open GeneralBorrowWildcardParentTagOrder GeneralBorrowExposureCardinality
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization
open S05CompletedAncestryReadMutable (Authority)
open DuplicatePrefix.BorrowRangeAccess
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem callback (tree : BorrowTree) (completion : Completion) (initial : LocationTree) (protections : ProtectedTags)
    (complete : Completes tree completion) (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (rootPosition selectedPosition : Nat) (root selected source : UniIndex) (selectedNode sourceNode : TreeNode)
    (rootSlot : tree.roots[rootPosition]? = some root) (selectedSlot : tree.roots[selectedPosition]? = some selected)
    (selectedPresent : tree.nodes.get selected = some selectedNode) (sourcePresent : tree.nodes.get source = some sourceNode)
    (exposed : sourceNode.isExposed = true) (sourcePath : Path tree selected source)
    (authority : Authority tree completion protections source initial)
    (coherent : LocationCoherent tree initial protections) (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial) (short : tree.nodes.size < 65536) :
    let result := tree.performWildcardAccessAt initial root none .Write protections (rootPosition != 0)
    result.status = .Completed ∧ LocationCoherent tree result.location protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
      Authority tree completion protections source result.location := by
  have localRights := fun index node present => (authority index node present).1
  have foreignRights := fun index node present => (authority index node present).2
  obtain ⟨forest⟩ := formed.forest initial protections
  have graph := GeneralBorrowExposedScopedReciprocal.of_forest tree initial protections forest depth
  let area := S05CompletedAncestryWriteAccess.support tree completion complete rootPosition root rootSlot
  have auth := S05WildcardCompletedWriteQueries.authorization_root tree completion initial protections complete depth order
    rootPosition selectedPosition root selected source selectedNode sourceNode rootSlot selectedSlot selectedPresent sourcePresent exposed
    sourcePath localRights foreignRights profile
  have plans : Nonempty (DuplicatePrefixResidualWriteWitnessPlan.Plan tree initial protections root rootPosition none) := by
    by_cases zero : rootPosition = 0
    · obtain ⟨rootNode,rootPresent,_⟩ := complete.2.2.2.1 rootPosition root rootSlot
      have below := CompletedBorrowAncestry.root_zero_below complete
        (by simpa only [zero] using rootSlot) selectedSlot sourcePath
      obtain ⟨witness,node,present,eligible,path,_⟩ := S05WildcardCompletedWriteQueries.origin_root
        tree completion initial protections complete order rootPosition selectedPosition root selected source root rootNode selectedNode sourceNode
        rootSlot selectedSlot selectedPresent sourcePresent exposed sourcePath (.refl root rootNode rootPresent) rootPresent localRights below
      subst rootPosition
      exact ⟨DuplicatePrefixResidualVisibleWritePlan.ordered tree initial protections root none depth graph short witness node present
        (GeneralBorrowPrimaryWitnessVisibility.of_order tree order initial protections none .Write witness node present eligible) eligible path⟩
    · exact ⟨DuplicatePrefixResidualWriteWitnessPlan.virtual tree initial protections root rootPosition none zero⟩
  obtain ⟨plan⟩ := plans
  let weights := GeneralBorrowWildcardForestWeights.of_forest tree initial protections forest
  obtain ⟨done,removed,legal,matching,cache,outside,sifa,gp,vacant,retained⟩ :=
    S05CompletedWriteAuthorityDFS.access_none tree initial protections root rootPosition none weights
      (GeneralBorrowWildcardForestWeights.bounded tree initial protections forest root) area plan auth depth forest coherent short profile possible
      completion source selected selectedPosition selectedNode sourceNode complete order rootSlot selectedSlot selectedPresent sourcePresent exposed
      sourcePath (fun _ path => path) rfl authority
  exact ⟨done,cache,sifa,gp,retained⟩

abbrev State := LocationTree × Option BorrowTree.BorrowTreeAccessStatus × Bool

/-- Literal all-root branch of the actual source-none location scan. -/
def scan (tree : BorrowTree) (protections : ProtectedTags) (range : ByteRange)
    (position : Nat) (state : State) : Id (ForInStep State) := Id.run do
  let (location,status,stop) := state
  if status.isNone && !stop then
    match tree.roots[position]? with
    | none => return .yield state
    | some root =>
      let wildcard := tree.performWildcardAccessAt location root none .Write protections (position != 0)
      if wildcard.status != .Completed then
        return .yield (wildcard.location,some (.WildcardFailure range wildcard.status),stop)
      else return .yield (wildcard.location,status,stop)
  return .yield state

private def Good (tree : BorrowTree) (completion : Completion) (protections : ProtectedTags)
    (source : UniIndex) (state : State) : Prop :=
  state.2.1 = none ∧ LocationCoherent tree state.1 protections ∧
  GeneralBorrowLocationSifaConsistency.Profile tree state.1 protections ∧
  GeneralBorrowSnapshotReadRuntime.GlobalPossible tree state.1 ∧ Authority tree completion protections source state.1

theorem access (tree : BorrowTree) (completion : Completion) (initial : LocationTree) (protections : ProtectedTags)
    (complete : Completes tree completion) (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (selectedPosition : Nat) (selected source : UniIndex) (selectedNode sourceNode : TreeNode)
    (selectedSlot : tree.roots[selectedPosition]? = some selected)
    (selectedPresent : tree.nodes.get selected = some selectedNode) (sourcePresent : tree.nodes.get source = some sourceNode)
    (exposed : sourceNode.isExposed = true) (sourcePath : Path tree selected source)
    (authority : Authority tree completion protections source initial)
    (coherent : LocationCoherent tree initial protections) (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial) (short : tree.nodes.size < 65536)
    (mode : ChildrenVisitMode) (range : ByteRange) :
    let result := source_tree_access_at tree initial none .Write protections mode range
    source_access_status result = none ∧ LocationCoherent tree (source_access_location result) protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree (source_access_location result) protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree (source_access_location result) ∧
      Authority tree completion protections source (source_access_location result) := by
  have loop : Good tree completion protections source
      (forIn (List.range' 0 tree.roots.size) (initial,none,false) (scan tree protections range) : Id State) := by
    apply GeneralBorrowLoop.list_invariant _ _ (Good tree completion protections source) _ _
      (show Good tree completion protections source (initial,none,false) from ⟨rfl,coherent,profile,possible,authority⟩)
    intro position member state good
    have valid : position < tree.roots.size := by
      have bound := List.mem_range'_1.mp member
      omega
    rcases state with ⟨location,status,stop⟩
    have statusEq := good.1
    dsimp only at statusEq
    subst status
    by_cases stopped : stop = true
    · subst stop
      simpa only [scan,Option.isNone_none,Bool.not_true,Bool.and_false,Bool.false_eq_true,↓reduceIte,Id.run,pure,
        ForInStep.value] using good
    have noStop : stop = false := by cases stop <;> simp_all
    subst stop
    have rootSlot := Array.getElem?_eq_getElem valid
    have current := callback tree completion location protections complete formed depth order position selectedPosition
      tree.roots[position] selected source selectedNode sourceNode rootSlot selectedSlot selectedPresent sourcePresent
      exposed sourcePath good.2.2.2.2 good.2.1 good.2.2.1 good.2.2.2.1 short
    simpa [scan,rootSlot,current.1,Good] using
      (show Good tree completion protections source
        ((tree.performWildcardAccessAt location tree.roots[position] none .Write protections (position != 0)).location,none,false)
        from ⟨rfl,current.2.1,current.2.2.1,current.2.2.2.1,current.2.2.2.2⟩)
  dsimp only
  simp_tree_helpers
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  change Good tree completion protections source (forIn (List.range' 0 tree.roots.size) (initial,none,false) _ : Id State)
  refine Eq.mpr ?_ loop
  apply congrArg (Good tree completion protections source)
  apply GeneralBorrowVirtualRootsAdapter.forIn_congr
  intro position member state
  rcases state with ⟨location,status,stop⟩
  cases rootSlot : tree.roots[position]? with
  | none => cases mode <;> simp [scan,rootSlot,Id.run,pure]
  | some root =>
    cases tagLookup : (tree.nodes.get root).map TreeNode.tag <;> cases mode <;> simp [scan,rootSlot,tagLookup,Id.run,pure]

/-- Actual wildcard ranged Write, retaining the SAME chosen-origin raw tables
through splitting and the complete max=none all-root scan on each saved row. -/
theorem range (tree : BorrowTree) (completion : Completion) (protections : ProtectedTags)
    (complete : Completes tree completion) (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (selectedPosition : Nat) (selected source : UniIndex) (selectedNode sourceNode : TreeNode)
    (selectedSlot : tree.roots[selectedPosition]? = some selected)
    (selectedPresent : tree.nodes.get selected = some selectedNode) (sourcePresent : tree.nodes.get source = some sourceNode)
    (exposed : sourceNode.isExposed = true) (sourcePath : Path tree selected source)
    (offset len : Size) (lower upper : UInt64)
    (owned : GeneralRangeMapOrigins.OwnedOn (fun location =>
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location ∧ Authority tree completion protections source location)
      lower upper tree.locations)
    (well : tree.locations.WellFormed)
    (runtime : GeneralRangeMapState.Every (fun location => LocationCoherent tree location protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location) tree.locations)
    (bounds : offset.bytes.toNat + len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (requestLower : lower.toNat ≤ offset.bytes.toNat)
    (requestUpper : (offset.bytes + len.bytes).toNat ≤ upper.toNat)
    (short : tree.nodes.size < 65536) (mode : ChildrenVisitMode) :
    GeneralBorrowConcreteRangeInvariant.Contract tree
      (fun location => GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location ∧ Authority tree completion protections source location)
      (fun location => LocationCoherent tree location protections ∧ GeneralBorrowLocationSifaConsistency.Profile tree location protections ∧
        GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location)
      (fun _ _ => True) lower upper
      (tree.performBorrowAccessRange .wildcard offset len .Write protections mode) := by
  apply GeneralBorrowConcreteRangeEntry.access_resolved tree protections .wildcard none rfl offset len .Write mode
    _ _ _ _ (fun _ authority => authority) (fun _ => trivial) _ lower upper owned well runtime bounds requestLower requestUpper
  intro location authority representation range
  have row := access tree completion location protections complete formed depth order selectedPosition selected source
    selectedNode sourceNode selectedSlot selectedPresent sourcePresent exposed sourcePath authority.2 representation.1
    representation.2.1 authority.1 short mode range
  exact ⟨row.1,⟨row.2.2.2.1,row.2.2.2.2⟩,⟨row.2.1,row.2.2.1,row.2.2.2.1⟩,trivial⟩

end DuplicatePrefix.S05WildcardCompletedWrite

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05WildcardCompletedWrite." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved full wildcard Write dependency {dependency}"
