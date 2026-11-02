import duplicate_prefix.GeneralBorrowExposedVirtualSchedule
import duplicate_prefix.GeneralBorrowWildcardLeaf
namespace DuplicatePrefix.GeneralBorrowExposedWildcardAccess
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowWildcardLeaf
open DuplicatePrefix.GeneralBorrowNodeUpdate
open DuplicatePrefix.BorrowRangeAccess
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
private theorem insert_same {α : Type} (nodes : UniValMap α) (index : UniIndex) (value : α)
    (present : nodes.get index = some value) : nodes.insert index value = nodes := by
  have valid := lookup_valid nodes index value present
  have cell : nodes.data[index.toNat]'valid = some value := by
    unfold UniValMap.get at present
    simpa only [Array.getElem?_eq_getElem valid] using present
  have data := insert_existing nodes index value value present
  rw [←cell] at data
  simp only [Array.set_getElem_self] at data
  cases nodes with
  | mk original =>
    cases result : (UniValMap.mk original).insert index value with
    | mk changed => exact congrArg UniValMap.mk (by simpa only [result] using data)
theorem physical (tree : BorrowTree) (location : LocationTree) (root : UniIndex)
    (node : TreeNode) (kind : AccessKind) (protections : ProtectedTags)
    (present : tree.nodes.get root = some node) (leaf : node.children = #[])
    (exposed : node.isExposed = true) (stored : location.perms.get root = some unique)
    (nonzero : GeneralBorrowWildcardRelatednessBounds.count location.exposedCache root kind ≠ 0) :
    tree.performWildcardAccessAt location root none kind protections false =
      ⟨location,.Completed⟩ := by
  have nonempty : 0 < tree.nodes.size := by
    have valid := lookup_valid tree.nodes root node present
    unfold UniValMap.size
    omega
  have notPast : ¬ 2 > tree.nodes.size*2+1 := by omega
  have notPast1 : ¬ 1 > tree.nodes.size*2+1 := by omega
  have unchanged := insert_same location.perms root unique stored
  have related : location.exposedCache.accessRelatedness root root kind false false = some .LocalAccess := by
    cases kind <;> simp_all [ExposedCache.accessRelatedness,GeneralBorrowWildcardRelatednessBounds.count,Id.run,pure]
  have recorded : unique.recordNewAccess kind .LocalAccess = .Recorded unique := by cases kind <;> rfl
  have accessed : ∀ held, unique.performAccess kind .LocalAccess held = .Success unique ⟨.Unique,.Unique⟩ := by
    intro held
    cases kind <;> cases held <;> rfl
  have permits : (Permission.Unique.strongestAllowedLocalAccess (protections.contains node.tag)).allows kind = true := by
    cases kind <;> rfl
  unfold BorrowTree.performWildcardAccessAt
  simp only [Id.run,bind,pure,ForIn.forIn]
  name_range_scan
  have step1 : scan () (location,false,.Completed,#[(root,false)],0) =
      .yield (location,false,.Completed,#[(root,true)],1) := by
    simp only [scan]
    unfold_leaf_helpers
    simp [present,leaf,stored,related,
      LocationState.skipIfKnownNoop,AccessRelatedness.isForeign,notPast1,Id.run,bind,pure]
    unfold_leaf_helpers
    simp [LocationState.skipIfKnownNoop,AccessRelatedness.isForeign,leaf]
  have step2 : scan () (location,false,.Completed,#[(root,true)],1) =
      .yield (location,true,.Completed,#[],2) := by
    simp only [scan]
    unfold_leaf_helpers
    simp [present,leaf,exposed,stored,related,
      notPast,Id.run,bind,pure,UniValMap.orInsert]
    all_goals try unfold_leaf_helpers
    all_goals simp [recorded,accessed,unchanged,permits,PermTransition.isNoop,
      LocationState.AccessResult.resultingState,bind,pure]
    simp [show unique.permission = Permission.Unique from rfl,permits]
  have step3 : scan () (location,true,.Completed,#[],2) = .done (location,true,.Completed,#[],2) := by
    simp [scan,bind,pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [step1,bind,pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [step2,bind,pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [step3,bind,pure]
  rfl
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

private theorem iterator (tree : BorrowTree) (before after : LocationTree) (primary : UniIndex)
    (extras : List UniIndex) (kind : AccessKind) (protections : ProtectedTags) (mode : ChildrenVisitMode) (range : ByteRange)
    (roots : tree.roots = (primary::extras).toArray)
    (first : tree.performWildcardAccessAt before primary none kind protections false = ⟨before,.Completed⟩)
    (completed : GeneralBorrowWildcardVirtualLeafFold.run tree extras before none kind protections = ⟨after,.Completed⟩) :
    source_access_location (source_tree_access_at tree before none kind protections mode range) = after ∧
    source_access_status (source_tree_access_at tree before none kind protections mode range) = none := by
  simp_tree_helpers
  simp only [roots,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one,
    List.size_toArray,List.length_cons]
  simp [List.size_toArray,List.range'_succ,bind,pure,first]
  change (forIn (List.range' 1 extras.length) (before,none,false)
    (scanAt tree primary extras kind protections range)).1 = after ∧
    (forIn (List.range' 1 extras.length) (before,none,false)
    (scanAt tree primary extras kind protections range)).2.1 = none
  rw [indexed,successful tree kind protections range extras before after completed]
  exact ⟨rfl,rfl⟩

/-- Real wildcard provenance dispatch across all ordered physical roots. The
first root has an exposed accessed Unique leaf, whose positive coherent counter
derives LocalAccess; all remaining exposed supporting leaves derive Either.
No tag selection, operation success, or poststate ownership is assumed. -/
theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (primary : UniIndex) (primaryNode : TreeNode) (extras : List UniIndex) (nodes : UniIndex → TreeNode)
    (kind : AccessKind) (mode : ChildrenVisitMode) (range : ByteRange)
    (roots : tree.roots = (primary::extras).toArray)
    (present : tree.nodes.get primary = some primaryNode) (leaf : primaryNode.children = #[])
    (exposed : primaryNode.isExposed = true) (stored : location.perms.get primary = some unique)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (short : tree.nodes.size < 65536)
    (data : ∀ root ∈ extras, tree.nodes.get root = some (nodes root) ∧
      (nodes root).children = #[] ∧ (nodes root).isExposed = true ∧
      GeneralBorrowExposureCardinality.supports
        (GeneralBorrowExposureCardinality.effective location protections root (nodes root)) kind = true) :
    ∃ after, source_access_location (source_tree_access_at tree location none kind protections mode range) = after ∧
      source_access_status (source_tree_access_at tree location none kind protections mode range) = none ∧
      GeneralBorrowExposureCardinality.LocationCoherent tree after protections ∧
      after.exposedCache = location.exposedCache ∧
      (∀ query node, tree.nodes.get query = some node →
        GeneralBorrowWildcardVirtualLeaf.effective after query node = GeneralBorrowWildcardVirtualLeaf.effective location query node) := by
  have support : GeneralBorrowExposureCardinality.supports
      (GeneralBorrowExposureCardinality.effective location protections primary primaryNode) kind = true := by
    cases kind <;> simp [GeneralBorrowExposureCardinality.supports,GeneralBorrowExposureCardinality.effective,stored,unique,
      Permission.strongestAllowedLocalAccess,GeneralBorrowExposureAncestorFold.supportsRead,GeneralBorrowExposureAncestorFold.supportsWrite]
  have positive := GeneralBorrowExposureCardinality.exposed_self location.exposedCache tree.nodes
    (GeneralBorrowExposureCardinality.effective location protections) coherent short primary primaryNode present exposed kind support
  have nonzero : GeneralBorrowWildcardRelatednessBounds.count location.exposedCache primary kind ≠ 0 := by
    cases kind <;> simpa only [GeneralBorrowWildcardRelatednessBounds.count,GeneralBorrowExposureCardinality.counter] using Nat.ne_of_gt positive
  have first := physical tree location primary primaryNode kind protections present leaf exposed stored nonzero
  obtain ⟨after,completed,cache,frame⟩ := GeneralBorrowExposedVirtualSchedule.schedule tree location protections extras nodes none kind coherent short
    (fun root member => ⟨(data root member).1,(data root member).2.1,(data root member).2.2.1,(data root member).2.2.2,rfl⟩)
  obtain ⟨actual,status⟩ := iterator tree location after primary extras kind protections mode range roots first completed
  exact ⟨after,actual,status,GeneralBorrowExposedVirtualSchedule.coherent_frame tree location after protections coherent cache frame,cache,frame⟩

end DuplicatePrefix.GeneralBorrowExposedWildcardAccess
