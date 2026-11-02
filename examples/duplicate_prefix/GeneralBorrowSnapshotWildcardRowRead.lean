import duplicate_prefix.GeneralBorrowSnapshotVirtualReadFold
import duplicate_prefix.GeneralBorrowSnapshotPrimaryReadRuntime
import duplicate_prefix.DuplicatePrefixBorrowAuthorization
import duplicate_prefix.GeneralBorrowVirtualRootsAdapter
namespace DuplicatePrefix.GeneralBorrowSnapshotWildcardRowRead
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralBorrowProjection DuplicatePrefixCallbackAuthorization
open GeneralBorrowSnapshotVirtualReadFold
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

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


/-- Actual full wildcard-provenance row Read from the raw S01 row contract.
The first physical root's real supporting witness and all virtual callbacks
are derived internally. No successful access or successor snapshot family is
a caller premise. This is a row operation, not whole-function coverage. -/
theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (row : DuplicatePrefixBorrowAuthorization.Row tree location protections none none none)
    (distinct : tree.roots.toList.Nodup) (nonempty : 0 < tree.roots.size)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree location protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location)
    (short : tree.nodes.size < 65536) (mode : ChildrenVisitMode) (range : ByteRange) :
    let result := source_tree_access_at tree location none .Read protections mode range
    source_access_status result = none ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree (source_access_location result) protections ∧
    GeneralBorrowLocationSifaConsistency.Profile tree (source_access_location result) protections ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree (source_access_location result) ∧
    GeneralBorrowExposedNonleafState.ReadFrame location (source_access_location result) ∧
    GeneralBorrowWildcardPrimaryReadWitness.PointwiseReadFrame tree protections location (source_access_location result) ∧
    (∀ query, tree.nodes.get query = none → (source_access_location result).perms.get query = location.perms.get query) := by
  cases rootList : tree.roots.toList with
  | nil =>
    have zero : tree.roots.size = 0 := by
      have length := congrArg List.length rootList
      simpa only [Array.length_toList,List.length_nil] using length
    omega
  | cons primary extras =>
    have roots : tree.roots = (primary::extras).toArray := by rw [←rootList]
    have zeroValid : 0 < tree.roots.size := nonempty
    obtain ⟨primarySupport,primaryAuth,_⟩ := row.callbacks 0 zeroValid (by simp)
    have primaryAuth : DuplicatePrefixResidualSupportAuthorization.Authorization tree location protections primary 0 none .Read primarySupport := by
      simpa only [roots,List.getElem_toArray,List.getElem_cons_zero] using primaryAuth
    have first := GeneralBorrowSnapshotPrimaryReadRuntime.access tree location protections formed primary primarySupport
      primaryAuth coherent short profile possible
    let middle := (tree.performWildcardAccessAt location primary none .Read protections false).location
    have package : ∀ root ∈ extras, ∃ support, RootData tree root support ∧ Snapshot tree location protections root 1 none .Read support := by
      intro root member
      obtain ⟨position,positionValid,selected⟩ := List.getElem_of_mem member
      have valid : position+1 < tree.roots.size := by simp only [roots,List.size_toArray,List.length_cons];omega
      have selectedArray : tree.roots[position+1]'valid = root := by
        simpa only [roots,List.getElem_toArray,List.getElem_cons_succ] using selected
      obtain ⟨support,authorization,_⟩ := row.callbacks (position+1) valid (by simp)
      rw [selectedArray] at authorization
      have rootMember : root ∈ tree.roots.toList := by rw [rootList];simp [member]
      exact ⟨support,⟨authorization.rooted,authorization.present,authorization.children,authorization.covers,rootMember⟩,
        normalize_virtual tree location protections root (position+1) none support (by omega)
          (DuplicatePrefixResidualInitialSnapshot.snapshot tree location protections root (position+1) none .Read support authorization coherent short)⟩
    let supports : UniIndex → UniIndex → Prop := fun root =>
      if member : root ∈ extras then Classical.choose (package root member) else fun _ => False
    have static : ∀ root ∈ extras, RootData tree root (supports root) := by
      intro root member
      simpa only [supports,dif_pos member] using (Classical.choose_spec (package root member)).1
    have snapshots : SnapshotFamily tree middle protections none extras supports := by
      intro root member
      have data := static root member
      have initialSnapshot : Snapshot tree location protections root 1 none .Read (supports root) := by
        simpa only [supports,dif_pos member] using (Classical.choose_spec (package root member)).2
      have primaryMember : primary ∈ tree.roots.toList := by rw [rootList];simp
      have different : primary ≠ root := by
        intro same
        subst root
        exact (List.nodup_cons.mp (by simpa only [rootList] using distinct)).1 member
      exact GeneralBorrowSnapshotReadTransport.transport_other tree location middle protections formed primary root
        primaryMember data.member different primarySupport (supports root) primaryAuth.covers data.present data.covers
        1 none initialSnapshot first.2.1 first.2.2.2.2.2.1
    have tail := GeneralBorrowSnapshotVirtualReadFold.run tree middle protections formed extras none supports
      (List.nodup_cons.mp (by simpa only [rootList] using distinct)).2 static snapshots
      first.2.2.2.2.1 first.2.2.2.2.2.2.1 first.2.2.2.2.2.2.2.1
    let final := (GeneralBorrowWildcardVirtualLeafFold.run tree extras middle none .Read protections).location
    have firstEq : tree.performWildcardAccessAt location primary none .Read protections false = ⟨middle,.Completed⟩ := by
      have reconstruct : tree.performWildcardAccessAt location primary none .Read protections false =
        ⟨middle,(tree.performWildcardAccessAt location primary none .Read protections false).status⟩ := rfl
      rw [first.1] at reconstruct
      exact reconstruct
    have tailEq : GeneralBorrowWildcardVirtualLeafFold.run tree extras middle none .Read protections = ⟨final,.Completed⟩ := by
      have reconstruct : GeneralBorrowWildcardVirtualLeafFold.run tree extras middle none .Read protections =
        ⟨final,(GeneralBorrowWildcardVirtualLeafFold.run tree extras middle none .Read protections).status⟩ := rfl
      rw [tail.1] at reconstruct
      exact reconstruct
    have actual := iterator tree location middle final primary extras .Read protections mode range roots firstEq tailEq
    refine ⟨actual.2,?_,?_,?_,?_,?_,?_⟩
    · rw [actual.1];exact tail.2.1
    · rw [actual.1];exact tail.2.2.1
    · rw [actual.1];exact tail.2.2.2.1
    · rw [actual.1]
      intro query
      exact (tail.2.2.2.2.1 query).trans (first.2.1 query)
    · rw [actual.1]
      intro query node present
      exact (tail.2.2.2.2.2.1 query node present).trans (first.2.2.2.1 query node present)
    · rw [actual.1]
      intro query missing
      exact (tail.2.2.2.2.2.2.1 query missing).trans (first.2.2.2.2.2.2.2.2 query missing)

end DuplicatePrefix.GeneralBorrowSnapshotWildcardRowRead
