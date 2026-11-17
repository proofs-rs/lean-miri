import duplicate_prefix.S05WildcardCompletedReadQueries
import duplicate_prefix.S05CompletedAncestryReadMutable
import duplicate_prefix.GeneralBorrowLoop
import duplicate_prefix.GeneralBorrowConcreteRangeEntry

/-! Actual wildcard Read at every physical root with maximum NONE. One fixed
exposed grant supplies current mutable authority throughout the whole scan.
There is no concrete normal phase, skipped selected root, or substituted cutoff.
This is a sufficient current representation model, not ordinary admission. -/
namespace DuplicatePrefix.S05WildcardCompletedRead
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
    let result := tree.performWildcardAccessAt initial root none .Read protections (rootPosition != 0)
    result.status = .Completed ∧ LocationCoherent tree result.location protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
      Authority tree completion protections source result.location := by
  have localRights := fun index node present => (authority index node present).1
  have foreignRights := fun index node present => (authority index node present).2
  obtain ⟨done,_,cache,sifa,gp,effects,outside,pointwise,transfer⟩ :=
    S05WildcardCompletedReadQueries.access_root_information tree completion initial protections complete depth order
      rootPosition selectedPosition root selected source selectedNode sourceNode rootSlot selectedSlot selectedPresent
      sourcePresent exposed sourcePath localRights foreignRights formed coherent short profile possible
  refine ⟨done,cache,sifa,gp,?_⟩
  intro index node present
  by_cases path : Path tree root index
  · have shape := S05WildcardCompletedReadQueries.query_shape tree completion initial protections complete depth order
      rootPosition selectedPosition root selected source index node selectedNode sourceNode rootSlot selectedSlot selectedPresent
      sourcePresent exposed sourcePath path present localRights
    dsimp only at shape
    rw [initial_relation tree initial protections root index node none .Read rootPosition coherent short] at shape
    constructor
    · intro below
      apply S05ReadRawAuthorityEndpoint.local_right _ _ _ (relation initial root index node none .Read rootPosition)
        (localRights index node present below)
      · rcases shape.1 below with classified | classified <;> simp [classified]
      · exact transfer index node path present
    · intro notBelow
      apply S05ReadRawAuthorityEndpoint.foreign_right _ _ _ (relation initial root index node none .Read rootPosition)
        (foreignRights index node present notBelow)
      · rcases shape.2 notBelow with classified | classified <;> simp [classified]
      · exact transfer index node path present
      · exact effects index node present
      · exact pointwise index node present
      · exact profile.present index node present
      · exact gp index node present
  · unfold RawState
    rw [outside index path]
    exact authority index node present

abbrev State := LocationTree × Option BorrowTree.BorrowTreeAccessStatus × Bool

/-- Literal all-root branch of the actual source-none location scan. -/
def scan (tree : BorrowTree) (protections : ProtectedTags) (range : ByteRange)
    (position : Nat) (state : State) : Id (ForInStep State) := Id.run do
  let (location,status,stop) := state
  if status.isNone && !stop then
    match tree.roots[position]? with
    | none => return .yield state
    | some root =>
      let wildcard := tree.performWildcardAccessAt location root none .Read protections (position != 0)
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
    let result := source_tree_access_at tree initial none .Read protections mode range
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
        ((tree.performWildcardAccessAt location tree.roots[position] none .Read protections (position != 0)).location,none,false)
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

/-- Actual wildcard ranged Read, retaining the SAME chosen-origin raw tables
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
      (tree.performBorrowAccessRange .wildcard offset len .Read protections mode) := by
  apply GeneralBorrowConcreteRangeEntry.access_resolved tree protections .wildcard none rfl offset len .Read mode
    _ _ _ _ (fun _ authority => authority) (fun _ => trivial) _ lower upper owned well runtime bounds requestLower requestUpper
  intro location authority representation range
  have row := access tree completion location protections complete formed depth order selectedPosition selected source
    selectedNode sourceNode selectedSlot selectedPresent sourcePresent exposed sourcePath authority.2 representation.1
    representation.2.1 authority.1 short mode range
  exact ⟨row.1,⟨row.2.2.2.1,row.2.2.2.2⟩,⟨row.2.1,row.2.2.1,row.2.2.2.1⟩,trivial⟩

end DuplicatePrefix.S05WildcardCompletedRead

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05WildcardCompletedRead." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved full wildcard Read dependency {dependency}"
