import duplicate_prefix.GeneralBorrowIsolatedLeafNormal
import duplicate_prefix.GeneralBorrowExposedWildcardAccess
namespace DuplicatePrefix.GeneralBorrowExposedConcreteLast
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowWildcardLeaf DuplicatePrefix.GeneralBorrowNodeUpdate
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
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
private theorem physical (tree : BorrowTree) (location : LocationTree) (root : UniIndex)
    (node : TreeNode) (maximum : BorTag) (kind : AccessKind) (protections : ProtectedTags)
    (present : tree.nodes.get root = some node) (leaf : node.children = #[])
    (exposed : node.isExposed = true) (stored : location.perms.get root = some unique)
    (bound : node.tag.value ≤ maximum.value)
    (nonzero : GeneralBorrowWildcardRelatednessBounds.count location.exposedCache root kind ≠ 0) :
    tree.performWildcardAccessAt location root (some maximum) kind protections false =
      ⟨location,.Completed⟩ := by
  have nonempty : 0 < tree.nodes.size := by
    have valid := lookup_valid tree.nodes root node present
    unfold UniValMap.size
    omega
  have notPast : ¬ 2 > tree.nodes.size*2+1 := by omega
  have notForeign : ¬ maximum.value < node.tag.value := by
    have := UInt64.le_iff_toNat_le.mp bound
    simp only [UInt64.lt_iff_toNat_lt]
    omega
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
    simp [present,leaf,stored,notForeign,related,
      LocationState.skipIfKnownNoop,AccessRelatedness.isForeign,notPast1,Id.run,bind,pure]
    unfold_leaf_helpers
    simp [LocationState.skipIfKnownNoop,AccessRelatedness.isForeign,leaf]
  have step2 : scan () (location,false,.Completed,#[(root,true)],1) =
      .yield (location,true,.Completed,#[],2) := by
    simp only [scan]
    unfold_leaf_helpers
    simp [present,leaf,exposed,stored,notForeign,related,
      notPast,Id.run,bind,pure,UniValMap.orInsert]
    all_goals try unfold_leaf_helpers
    all_goals simp [recorded,accessed,unchanged,permits,bound,PermTransition.isNoop,
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

private def scanAt (tree : BorrowTree) (head concrete : UniIndex) (tail : List UniIndex) (maximum : BorTag)
    (kind : AccessKind) (protections : ProtectedTags) (range : ByteRange)
    (position : Nat) (state : GeneralBorrowVirtualRootsAdapter.State) : Id (ForInStep GeneralBorrowVirtualRootsAdapter.State) :=
  if state.2.1 = none ∧ state.2.2 = false then
    match (head::tail)[position]? with
    | none => .yield state
    | some root =>
      if concrete = root then .yield state else
        let first := tree.performWildcardAccessAt state.1 root (some maximum) kind protections (position != 0)
        if first.status = .Completed then .yield (first.location,state.2.1,state.2.2)
        else .yield (first.location,some (.WildcardFailure range first.status),state.2.2)
  else .yield state

private theorem indexed (tree : BorrowTree) (head concrete : UniIndex) (tail : List UniIndex) (maximum : BorTag)
    (kind : AccessKind) (protections : ProtectedTags) (range : ByteRange) (initial : GeneralBorrowVirtualRootsAdapter.State) :
    forIn (List.range' 1 tail.length) initial (scanAt tree head concrete tail maximum kind protections range) =
      forIn tail initial (GeneralBorrowVirtualRootsAdapter.scan tree concrete maximum kind protections range) := by
  calc
    _ = forIn (List.range' 1 tail.length) initial
        (fun pos state => GeneralBorrowVirtualRootsAdapter.scan tree concrete maximum kind protections range (head::tail)[pos]! state) := by
      apply GeneralBorrowVirtualRootsAdapter.forIn_congr
      intro pos member state
      obtain ⟨index,bound,position⟩ := List.mem_range'.mp member
      have positionEq : pos = index+1 := by omega
      subst pos
      have selected : (head::tail)[index+1]? = some tail[index] := by
        simp only [List.getElem?_cons_succ,List.getElem?_eq_getElem bound]
      simp only [scanAt,Nat.one_mul,Nat.add_comm 1 index,selected,show (index+1 != 0) = true from by simp,
        GeneralBorrowVirtualRootsAdapter.scan,List.getElem!_eq_getElem?_getD,selected,Option.getD_some]
    _ = forIn ((List.range' 1 tail.length).map (fun pos => (head::tail)[pos]!)) initial
        (GeneralBorrowVirtualRootsAdapter.scan tree concrete maximum kind protections range) := List.forIn_map.symm
    _ = _ := by rw [GeneralBorrowVirtualRootsAdapter.index_map]

private theorem successful_app (tree : BorrowTree) (primary : UniIndex) (maximum : BorTag)
    (kind : AccessKind) (protections : ProtectedTags) (range : ByteRange)
    (extras : List UniIndex) (different : ∀ root ∈ extras, root ≠ primary)
    (location after : LocationTree)
    (completed : GeneralBorrowWildcardVirtualLeafFold.run tree extras location (some maximum) kind protections = ⟨after,.Completed⟩) :
    forIn (extras++[primary]) (location,none,false) (GeneralBorrowVirtualRootsAdapter.scan tree primary maximum kind protections range) = (after,none,false) := by
  induction extras generalizing location with
  | nil =>
    cases completed
    simp [List.forIn_cons,List.forIn_nil,GeneralBorrowVirtualRootsAdapter.scan,bind,pure]
  | cons root rest ih =>
    have ne : primary ≠ root := Ne.symm (different root (by simp))
    let first := tree.performWildcardAccessAt location root (some maximum) kind protections true
    have good : first.status = .Completed := by
      simp only [GeneralBorrowWildcardVirtualLeafFold.run] at completed
      try dsimp only at completed
      split at completed
      · exact of_decide_eq_true ‹_ = true›
      · have status := congrArg BorrowTree.WildcardLocationAccessResult.status completed
        simp_all [first]
    have tail : GeneralBorrowWildcardVirtualLeafFold.run tree rest first.location (some maximum) kind protections = ⟨after,.Completed⟩ := by
      simpa only [GeneralBorrowWildcardVirtualLeafFold.run,show (tree.performWildcardAccessAt location root (some maximum) kind protections true).status = .Completed from good,
        beq_self_eq_true,↓reduceIte] using completed
    rw [List.cons_append,List.forIn_cons]
    simp only [GeneralBorrowVirtualRootsAdapter.scan,show ((none : Option BorrowTree.BorrowTreeAccessStatus) = none ∧ false = false) from ⟨rfl,rfl⟩,
      ↓reduceIte,ne,show (tree.performWildcardAccessAt location root (some maximum) kind protections true).status = .Completed from good,
      bind,pure]
    exact ih (fun query member => different query (by simp [member])) first.location tail

private theorem iterator (tree : BorrowTree) (before after : LocationTree) (head anchor : UniIndex)
    (anchorNode : TreeNode) (extras : List UniIndex) (kind : AccessKind) (protections : ProtectedTags) (range : ByteRange)
    (roots : tree.roots = (head::(extras++[anchor])).toArray) (different : anchor ≠ head)
    (present : tree.nodes.get anchor = some anchorNode)
    (normalStatus : (tree.performNormalAccessAt before anchor kind protections .VisitChildrenOfAccessed).access.status = .Completed)
    (normalOutcome : (tree.performNormalAccessAt before anchor kind protections .VisitChildrenOfAccessed).outcome = .ok ())
    (rootEq : (tree.performNormalAccessAt before anchor kind protections .VisitChildrenOfAccessed).access.root = anchor.toNat)
    (first : tree.performWildcardAccessAt (tree.performNormalAccessAt before anchor kind protections .VisitChildrenOfAccessed).location
      head (some anchorNode.tag) kind protections false =
      ⟨(tree.performNormalAccessAt before anchor kind protections .VisitChildrenOfAccessed).location,.Completed⟩)
    (extrasDifferent : ∀ root ∈ extras, root ≠ anchor)
    (completed : GeneralBorrowWildcardVirtualLeafFold.run tree extras
      (tree.performNormalAccessAt before anchor kind protections .VisitChildrenOfAccessed).location (some anchorNode.tag) kind protections = ⟨after,.Completed⟩) :
    source_access_location (source_tree_access_at tree before (some anchor) kind protections .VisitChildrenOfAccessed range) = after ∧
    source_access_status (source_tree_access_at tree before (some anchor) kind protections .VisitChildrenOfAccessed range) = none := by
  generalize tailEq : extras++[anchor] = tail at roots
  simp_tree_helpers
  simp only [normalStatus,normalOutcome,rootEq,index_self,present,roots]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one,
    List.size_toArray,List.length_cons]
  simp [List.size_toArray,List.range'_succ,bind,pure,present,first,different]
  change (forIn (List.range' 1 tail.length)
    ((tree.performNormalAccessAt before anchor kind protections .VisitChildrenOfAccessed).location,none,false)
    (scanAt tree head anchor tail anchorNode.tag kind protections range)).1 = after ∧
    (forIn (List.range' 1 tail.length)
    ((tree.performNormalAccessAt before anchor kind protections .VisitChildrenOfAccessed).location,none,false)
    (scanAt tree head anchor tail anchorNode.tag kind protections range)).2.1 = none
  rw [indexed,←tailEq,successful_app tree anchor anchorNode.tag kind protections range extras extrasDifferent _ after completed]
  exact ⟨rfl,rfl⟩

/-- Actual concrete Read at a parentless unexposed leaf appended after exposed
roots. Old components need only expose supporting leaf references; active
protected Unique extras remain allowed because they take the real Either branch.
The concrete normal prefix uses only its own local ownership event. -/
theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (head anchor : UniIndex) (headNode anchorNode : TreeNode) (extras : List UniIndex) (nodes : UniIndex → TreeNode)
    (range : ByteRange) (roots : tree.roots = (head::(extras++[anchor])).toArray)
    (different : anchor ≠ head) (extrasDifferent : ∀ root ∈ extras, root ≠ anchor)
    (headPresent : tree.nodes.get head = some headNode) (headLeaf : headNode.children = #[])
    (headExposed : headNode.isExposed = true) (headStored : location.perms.get head = some unique)
    (headBound : headNode.tag.value ≤ anchorNode.tag.value)
    (anchorPresent : tree.nodes.get anchor = some anchorNode) (anchorLeaf : anchorNode.children = #[])
    (anchorParent : anchorNode.parent = none) (anchorHidden : anchorNode.isExposed = false)
    (state : LocationState) (anchorStored : location.perms.get anchor = some state)
    (localOwned : ∀ held, GeneralBorrowPermissions.AccessOwned state .Read .LocalAccess held)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (short : tree.nodes.size < 65536)
    (data : ∀ root ∈ extras, tree.nodes.get root = some (nodes root) ∧
      (nodes root).children = #[] ∧ (nodes root).isExposed = true ∧
      GeneralBorrowExposureCardinality.supports
        (GeneralBorrowExposureCardinality.effective location protections root (nodes root)) .Read = true ∧
      GeneralBorrowWildcardVirtualLeaf.onlyForeign (nodes root) (some anchorNode.tag) = false) :
    ∃ after, source_access_location (source_tree_access_at tree location (some anchor) .Read protections .VisitChildrenOfAccessed range) = after ∧
      source_access_status (source_tree_access_at tree location (some anchor) .Read protections .VisitChildrenOfAccessed range) = none ∧
      GeneralBorrowExposureCardinality.LocationCoherent tree after protections ∧
      after.exposedCache = location.exposedCache := by
  have normal := GeneralBorrowIsolatedLeafNormal.access tree location protections anchor anchorNode .Read .VisitChildrenOfAccessed
    anchorPresent anchorParent anchorLeaf anchorHidden state anchorStored localOwned
  let middle := (tree.performNormalAccessAt location anchor .Read protections .VisitChildrenOfAccessed).location
  have middleGood := GeneralBorrowIsolatedLeafNormal.coherent tree location protections anchor anchorNode .Read .VisitChildrenOfAccessed
    anchorPresent anchorParent anchorLeaf anchorHidden state anchorStored localOwned coherent
  have middleHead : middle.perms.get head = some unique :=
    (normal.2.2.2.2 head headNode headPresent (Ne.symm different)).trans headStored
  have support : GeneralBorrowExposureCardinality.supports
      (GeneralBorrowExposureCardinality.effective middle protections head headNode) .Read = true := by
    simp [GeneralBorrowExposureCardinality.supports,GeneralBorrowExposureCardinality.effective,middleHead,unique,
      Permission.strongestAllowedLocalAccess,GeneralBorrowExposureAncestorFold.supportsRead]
  have positive := GeneralBorrowExposureCardinality.exposed_self middle.exposedCache tree.nodes
    (GeneralBorrowExposureCardinality.effective middle protections) middleGood short head headNode headPresent headExposed .Read support
  have nonzero : GeneralBorrowWildcardRelatednessBounds.count middle.exposedCache head .Read ≠ 0 := Nat.ne_of_gt positive
  have first := physical tree middle head headNode anchorNode.tag .Read protections headPresent headLeaf headExposed middleHead headBound nonzero
  have afterData : ∀ root ∈ extras, tree.nodes.get root = some (nodes root) ∧
      (nodes root).children = #[] ∧ (nodes root).isExposed = true ∧
      GeneralBorrowExposureCardinality.supports
        (GeneralBorrowExposureCardinality.effective middle protections root (nodes root)) .Read = true ∧
      GeneralBorrowWildcardVirtualLeaf.onlyForeign (nodes root) (some anchorNode.tag) = false := by
    intro root member
    obtain ⟨present,leaf,exposed,support,cutoff⟩ := data root member
    refine ⟨present,leaf,exposed,?_,cutoff⟩
    have stored := normal.2.2.2.2 root (nodes root) present (extrasDifferent root member)
    simpa only [GeneralBorrowExposureCardinality.effective,show middle.perms.get root = location.perms.get root from stored] using support
  obtain ⟨after,completed,cache,frame⟩ := GeneralBorrowExposedVirtualSchedule.schedule tree middle protections extras nodes
    (some anchorNode.tag) .Read middleGood short afterData
  obtain ⟨actual,status⟩ := iterator tree location after head anchor anchorNode extras .Read protections range roots different anchorPresent
    normal.1 normal.2.1 normal.2.2.1 first extrasDifferent completed
  exact ⟨after,actual,status,GeneralBorrowExposedVirtualSchedule.coherent_frame tree middle after protections middleGood cache frame,
    cache.trans normal.2.2.2.1⟩
end DuplicatePrefix.GeneralBorrowExposedConcreteLast
