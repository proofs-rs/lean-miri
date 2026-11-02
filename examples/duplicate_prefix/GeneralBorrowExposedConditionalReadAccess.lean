import duplicate_prefix.GeneralBorrowExposedConditionalReadFold
import duplicate_prefix.GeneralBorrowExposedConditionalReadPrimaryLoop

namespace DuplicatePrefix.GeneralBorrowExposedConditionalReadAccess
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess
open GeneralBorrowExposedNonleafState (ReadFrame)
open GeneralBorrowExposedConditionalReadState
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private def scan (tree : BorrowTree) (kind : AccessKind) (protections : ProtectedTags) (range : ByteRange)
    (root : UniIndex) (state : GeneralBorrowVirtualRootsAdapter.State) : Id (ForInStep GeneralBorrowVirtualRootsAdapter.State) :=
  if state.2.1 = none ∧ state.2.2 = false then
    let first := tree.performWildcardAccessAt state.1 root none kind protections true
    if first.status = .Completed then .yield (first.location,state.2.1,state.2.2)
    else .yield (first.location,some (.WildcardFailure range first.status),state.2.2)
  else .yield state

private theorem successful (tree : BorrowTree) (kind : AccessKind) (protections : ProtectedTags) (range : ByteRange)
    (roots : List UniIndex) (before after : LocationTree)
    (completed : GeneralBorrowWildcardVirtualLeafFold.run tree roots before none kind protections = ⟨after,.Completed⟩) :
    forIn roots (before,none,false) (scan tree kind protections range) = (after,none,false) := by
  induction roots generalizing before with
  | nil => cases completed;rfl
  | cons root rest ih =>
    have good : (tree.performWildcardAccessAt before root none kind protections true).status = .Completed := by
      simp only [GeneralBorrowWildcardVirtualLeafFold.run] at completed
      split at completed
      · exact of_decide_eq_true ‹_ = true›
      · have status := congrArg BorrowTree.WildcardLocationAccessResult.status completed
        simp_all
    have tail : GeneralBorrowWildcardVirtualLeafFold.run tree rest
        (tree.performWildcardAccessAt before root none kind protections true).location none kind protections = ⟨after,.Completed⟩ := by
      simpa only [GeneralBorrowWildcardVirtualLeafFold.run,good,beq_self_eq_true,ite_true] using completed
    rw [List.forIn_cons]
    simp only [scan,good,bind,pure,↓reduceIte]
    exact ih _ tail

private def scanAt (tree : BorrowTree) (primary : UniIndex) (extras : List UniIndex)
    (kind : AccessKind) (protections : ProtectedTags) (range : ByteRange)
    (position : Nat) (state : GeneralBorrowVirtualRootsAdapter.State) : Id (ForInStep GeneralBorrowVirtualRootsAdapter.State) :=
  if state.2.1 = none ∧ state.2.2 = false then
    match (primary::extras)[position]? with
    | none => .yield state
    | some root =>
      let first := tree.performWildcardAccessAt state.1 root none kind protections (position != 0)
      if first.status = .Completed then .yield (first.location,state.2.1,state.2.2)
      else .yield (first.location,some (.WildcardFailure range first.status),state.2.2)
  else .yield state

private theorem indexed (tree : BorrowTree) (primary : UniIndex) (extras : List UniIndex)
    (kind : AccessKind) (protections : ProtectedTags) (range : ByteRange) (initial : GeneralBorrowVirtualRootsAdapter.State) :
    forIn (List.range' 1 extras.length) initial (scanAt tree primary extras kind protections range) =
      forIn extras initial (scan tree kind protections range) := by
  calc
    _ = forIn (List.range' 1 extras.length) initial
        (fun pos state => scan tree kind protections range (primary::extras)[pos]! state) := by
      apply GeneralBorrowVirtualRootsAdapter.forIn_congr
      intro pos member state
      obtain ⟨index,bound,position⟩ := List.mem_range'.mp member
      have positionEq : pos = index+1 := by omega
      subst pos
      have selected : (primary::extras)[index+1]? = some extras[index] := by
        simp only [List.getElem?_cons_succ,List.getElem?_eq_getElem bound]
      simp only [scanAt,Nat.one_mul,Nat.add_comm 1 index,selected,show (index+1 != 0) = true from by simp,
        scan,List.getElem!_eq_getElem?_getD,selected,Option.getD_some]
    _ = forIn ((List.range' 1 extras.length).map (fun pos => (primary::extras)[pos]!)) initial
        (scan tree kind protections range) := List.forIn_map.symm
    _ = _ := by rw [GeneralBorrowVirtualRootsAdapter.index_map]

private theorem iterator (tree : BorrowTree) (before middle after : LocationTree) (primary : UniIndex)
    (extras : List UniIndex) (kind : AccessKind) (protections : ProtectedTags) (mode : ChildrenVisitMode) (range : ByteRange)
    (roots : tree.roots = (primary::extras).toArray)
    (first : tree.performWildcardAccessAt before primary none kind protections false = ⟨middle,.Completed⟩)
    (completed : GeneralBorrowWildcardVirtualLeafFold.run tree extras middle none kind protections = ⟨after,.Completed⟩) :
    source_access_location (source_tree_access_at tree before none kind protections mode range) = after ∧
    source_access_status (source_tree_access_at tree before none kind protections mode range) = none := by
  simp_tree_helpers
  simp only [roots,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one,
    List.size_toArray,List.length_cons]
  simp [List.size_toArray,List.range'_succ,bind,pure,first]
  change (forIn (List.range' 1 extras.length) (middle,none,false)
    (scanAt tree primary extras kind protections range)).1 = after ∧
    (forIn (List.range' 1 extras.length) (middle,none,false)
    (scanAt tree primary extras kind protections range)).2.1 = none
  rw [indexed,successful tree kind protections range extras middle after completed]
  exact ⟨rfl,rfl⟩


/-- Actual wildcard provenance across an arbitrary ordered physical forest.
The primary component has an exposed supporting descendant on a raw parent/child
path in root position zero; all components satisfy cache-sensitive protected Read compatibility. Positive local Read counters admit protected Unique and ReservedIM rows. No leaf, unexposed-node, source
classification or operation-success premise is required. Exposures confined to
extra components do not discharge the primary-component support condition. -/
theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (primary : UniIndex) (extras : List UniIndex) (mode : ChildrenVisitMode) (range : ByteRange)
    (roots : tree.roots = (primary::extras).toArray)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (primaryData : GeneralBorrowExposedConditionalReadPrimaryWitness.Data tree location primary protections)
    (extrasData : ∀ root ∈ extras, Data tree location root protections) :
    ∃ after,
      source_access_location (source_tree_access_at tree location none .Read protections mode range) = after ∧
      source_access_status (source_tree_access_at tree location none .Read protections mode range) = none ∧
      ReadFrame location after ∧ Readable tree after protections ∧
      GeneralBorrowExposureCardinality.LocationCoherent tree after protections := by
  let weights := GeneralBorrowWildcardForestWeights.of_forest tree location protections forest
  have bounded := GeneralBorrowWildcardForestWeights.bounded tree location protections forest
  have first := GeneralBorrowExposedConditionalReadPrimaryLoop.access tree location primary protections weights (bounded primary) primaryData
  let middle := (tree.performWildcardAccessAt location primary none .Read protections false).location
  obtain ⟨after,tail,frame,readable,coherent⟩ := GeneralBorrowExposedConditionalReadFold.run_from tree location middle protections extras none weights
    (fun root _ => bounded root) extrasData first.2.1 first.2.2.1 first.2.2.2 rfl
  have firstEq : tree.performWildcardAccessAt location primary none .Read protections false = ⟨middle,.Completed⟩ := by
    have reconstruct : tree.performWildcardAccessAt location primary none .Read protections false =
        ⟨middle,(tree.performWildcardAccessAt location primary none .Read protections false).status⟩ := by
      dsimp only [middle]
    rw [first.1] at reconstruct
    exact reconstruct
  obtain ⟨actual,status⟩ := iterator tree location middle after primary extras .Read protections mode range roots firstEq tail
  exact ⟨after,actual,status,frame,readable,coherent⟩

end DuplicatePrefix.GeneralBorrowExposedConditionalReadAccess
