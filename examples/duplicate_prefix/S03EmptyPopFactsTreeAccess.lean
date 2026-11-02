import duplicate_prefix.S03EmptyPopFactsAccess

namespace DuplicatePrefix.S03EmptyPopFactsTreeAccess
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection BorrowRangeAccess GeneralBorrowExposureCardinality
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

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
    (inactive : (GeneralBorrowWildcardVirtualLeaf.effective location query node).accessed = false) :
    let result := source_access_location (source_tree_access_at tree location (some source) kind protections mode range)
    (GeneralBorrowWildcardVirtualLeaf.effective result query node).accessed = false ∧
      counter result.exposedCache query kind = 0 := by
  have initial := S03EmptyPopFactsAccess.normal tree graph location protections query source node sourceNode
    present sourcePresent leaf hidden different authorization coherent kind mode inactive
  unfold_internal ".BorrowTree.performTreeAccessAt"
  simp only [Id.run,bind,pure,initial.1,initial.2.1,beq_self_eq_true,bne_self_eq_false,Bool.not_true,Bool.false_eq_true,↓reduceIte]
  cases converted : UniIndex.ofNat? (tree.performNormalAccessAt location source kind protections mode).access.root with
  | none => simpa only [converted] using initial.2.2
  | some selected =>
    simp only [converted,Id.run,bind,pure,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
      Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
    name_borrow_range_scan
    let predicate := fun (state : LocationTree × Option BorrowTree.BorrowTreeAccessStatus × Bool) =>
      (GeneralBorrowWildcardVirtualLeaf.effective state.1 query node).accessed = false ∧
        counter state.1.exposedCache query kind = 0
    have step : ∀ position ∈ List.range' 0 tree.roots.size, ∀ state,
        predicate state → predicate (scan position state).value := by
      intro position member state good
      rcases state with ⟨current,status,stopped⟩
      dsimp only [scan]
      repeat' first | split | simp_all only [Bool.and_eq_true,ForInStep.value]
      all_goals first
        | exact good
        | exact S03EmptyPopFactsWildcard.access tree graph query node present leaf hidden current _ _ kind protections _ good.1 good.2
    have retained := GeneralBorrowLoop.list_invariant _ scan predicate step
      ((tree.performNormalAccessAt location source kind protections mode).location,none,false) initial.2.2
    exact retained

end DuplicatePrefix.S03EmptyPopFactsTreeAccess
