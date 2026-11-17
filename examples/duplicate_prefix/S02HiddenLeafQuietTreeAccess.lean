import duplicate_prefix.S02HiddenLeafQuietWildcard
import duplicate_prefix.S03EmptyPopFactsTreeAccess

namespace DuplicatePrefix.S02HiddenLeafQuietTreeAccess
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection BorrowRangeAccess GeneralBorrowExposureCardinality
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Real normal access to a distinct source keeps a zero child inactive.
The actual cache result supplies its zero local counter for later callbacks. -/
theorem normal (tree : BorrowTree) (graph : GeneralBorrowStructuralHistoryState.GraphState tree)
    (location : LocationTree) (protections : ProtectedTags)
    (query source : UniIndex) (node sourceNode : TreeNode)
    (present : tree.nodeAt query = some node) (sourcePresent : tree.nodeAt source = some sourceNode)
    (leaf : node.children = #[]) (hidden : node.isExposed = false) (different : query ≠ source)
    (authorization : DuplicatePrefixBorrowAuthorization.Normal tree location protections source)
    (coherent : LocationCoherent tree location protections)
    (kind : AccessKind) (mode : ChildrenVisitMode)
    (quiet : S02HiddenLeafQuietNormal.Quiet (GeneralBorrowWildcardVirtualLeaf.effective location query node)) :
    let result := tree.performNormalAccessAt location source kind protections mode
    result.access.status = .Completed ∧ result.outcome = .ok () ∧
    S02HiddenLeafQuietNormal.Quiet (GeneralBorrowWildcardVirtualLeaf.effective result.location query node) ∧
    counter result.location.exposedCache query kind = 0 := by
  obtain ⟨forest⟩ := graph.forest location protections
  obtain ⟨depth⟩ := graph.depth
  have owned : GeneralBorrowCompatibleScopedNormal.Owned (source_normal_projection tree location protections)
      source.toNat kind authorization.component := by
    intro index included valid
    have size : (source_normal_projection tree location protections).topology.nodes.size = tree.nodes.data.size := by
      unfold_general_projection
      unfold_general_topology
      simp only [Array.size_map]
    exact authorization.permissions kind index included (by rwa [←size])
  obtain ⟨done,outcome,afterCoherent⟩ := GeneralBorrowCompatibleScopedNormalExposure.access tree location protections
    source kind mode depth graph.children sourceNode sourcePresent forest authorization.component owned coherent
  have before : S02HiddenLeafQuietNormal.LocationTyped location query := by
    intro state stored
    change S02HiddenLeafQuietNormal.Quiet state
    simpa only [GeneralBorrowWildcardVirtualLeaf.effective,stored,Option.getD_some] using quiet
  have after := S02HiddenLeafQuietNormal.normal tree location protections source query kind mode before
    (S03EmptyPopFactsLeaf.foreign_events tree location protections query source node sourceNode present sourcePresent leaf different forest kind mode)
  refine ⟨done,outcome,?_,?_⟩
  · cases stored : (tree.performNormalAccessAt location source kind protections mode).location.perms.get query with
    | none => left;simp only [GeneralBorrowWildcardVirtualLeaf.effective,stored,Option.getD_none,TreeNode.defaultLocationState]
    | some state => simpa only [GeneralBorrowWildcardVirtualLeaf.effective,stored,Option.getD_some,S02HiddenLeafQuietNormal.Quiet] using after state stored
  · rw [afterCoherent query kind,S03EmptyPopFactsAuthorization.leaf_cardinality tree _ protections graph query node present leaf hidden kind]
    rfl

/-- The actual concrete per-row operation preserves the empty leaf through
its normal phase and every ordered physical-root callback. -/
theorem concrete (tree : BorrowTree) (graph : GeneralBorrowStructuralHistoryState.GraphState tree)
    (location : LocationTree) (protections : ProtectedTags)
    (query source : UniIndex) (node sourceNode : TreeNode)
    (present : tree.nodeAt query = some node) (sourcePresent : tree.nodeAt source = some sourceNode)
    (leaf : node.children = #[]) (hidden : node.isExposed = false) (different : query ≠ source)
    (authorization : DuplicatePrefixBorrowAuthorization.Normal tree location protections source)
    (coherent : LocationCoherent tree location protections)
    (kind : AccessKind) (mode : ChildrenVisitMode) (range : ByteRange)
    (quiet : S02HiddenLeafQuietNormal.Quiet (GeneralBorrowWildcardVirtualLeaf.effective location query node)) :
    let result := source_access_location (source_tree_access_at tree location (some source) kind protections mode range)
    S02HiddenLeafQuietNormal.Quiet (GeneralBorrowWildcardVirtualLeaf.effective result query node) ∧
      counter result.exposedCache query kind = 0 := by
  have initial := normal tree graph location protections query source node sourceNode
    present sourcePresent leaf hidden different authorization coherent kind mode quiet
  unfold_internal ".BorrowTree.performTreeAccessAt"
  simp only [Id.run,bind,pure,initial.1,initial.2.1,beq_self_eq_true,bne_self_eq_false,Bool.not_true,Bool.false_eq_true,↓reduceIte]
  cases converted : UniIndex.ofNat? (tree.performNormalAccessAt location source kind protections mode).access.root with
  | none => simpa only [converted] using initial.2.2
  | some selected =>
    simp only [converted,Id.run,bind,pure,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
      Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
    name_borrow_range_scan
    let predicate := fun (state : LocationTree × Option BorrowTree.BorrowTreeAccessStatus × Bool) =>
      S02HiddenLeafQuietNormal.Quiet (GeneralBorrowWildcardVirtualLeaf.effective state.1 query node) ∧
        counter state.1.exposedCache query kind = 0
    have step : ∀ position ∈ List.range' 0 tree.roots.size, ∀ state,
        predicate state → predicate (scan position state).value := by
      intro position member state good
      rcases state with ⟨current,status,stopped⟩
      dsimp only [scan]
      repeat' first | split | simp_all only [Bool.and_eq_true,ForInStep.value]
      all_goals first
        | exact good
        | exact S02HiddenLeafQuietWildcard.access tree graph query node present leaf hidden current _ _ kind protections _ good.1 good.2
    have retained := GeneralBorrowLoop.list_invariant _ scan predicate step
      ((tree.performNormalAccessAt location source kind protections mode).location,none,false) initial.2.2
    exact retained

end DuplicatePrefix.S02HiddenLeafQuietTreeAccess
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S02HiddenLeafQuietTreeAccess.normal,``DuplicatePrefix.S02HiddenLeafQuietTreeAccess.concrete] do
    for ax in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "unapproved axiom {ax}"
