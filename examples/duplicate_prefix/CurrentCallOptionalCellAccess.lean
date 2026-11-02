import duplicate_prefix.CurrentCallNeutralCellNecessity
import duplicate_prefix.CurrentCallEmptyEntryNormalWrite
import duplicate_prefix.S03EmptyPopFactsAuthorization
import duplicate_prefix.CandidateCurrentGrantRuntime

/-! A bounded representation/consumer bridge: an arbitrary primary physical
component and ONE later hidden, unheld Cell leaf. This is not ordinary-input
coverage and does not modify the positive execution pipeline. -/
namespace DuplicatePrefix.CurrentCallOptionalCellAccess
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.DataStructures
open CandidateStableCallOwnership CandidateCurrentGrantResources OrdinaryBorrowAuthority
open GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowProjection GeneralBorrowExposureCardinality
open GeneralBorrowForest
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- The completion keeps the actual physical parents. The ambient root has
NONE, never a fabricated exposed origin. Concrete families are interpreted in
this SAME finite parent map. Only two physical roots are in this first bridge. -/
structure Representation (tree : BorrowTree) (completion : Completion)
    (protections : ProtectedTags) (primary cell : UniIndex) (cellNode : TreeNode) : Prop where
  roots : tree.roots = #[primary,cell]
  distinct : primary ≠ cell
  physicalParents : completion.parents = tree.nodes.data.map (fun saved => saved.bind (·.parent))
  depths : completion.depths.size = tree.nodes.data.size
  cellPresent : tree.nodes.get cell = some cellNode
  cellParent : cellNode.parent = none
  cellLeaf : cellNode.children = #[]
  cellHidden : cellNode.isExposed = false
  cellPermission : cellNode.defaultInitialPermission = .Cell
  cellSifa : cellNode.defaultInitialSifa = .None
  cellUnheld : protections.contains cellNode.tag = false

/-- The actual decoded content-token/guard clauses for one fixed current grant.
No access result, future row, or raw Allows table is a premise. -/
def RowResources (tree : BorrowTree) (completion : Completion) (protections : ProtectedTags)
    (grant : UniIndex) (location : LocationTree) : Prop :=
  ∀ index node, tree.nodes.get index = some node →
    (Below completion index grant → .exclusive ∈ tokens (denote (RawState location index node) (protections.contains node.tag))) ∧
    (Clash (guard (denote (RawState location index node) (protections.contains node.tag))) .exclusive → Below completion index grant)

/-- Projection of the existing independently stated current resource embedding.
This lower bridge does not replace ordinary admission by RowResources. In
particular, no completion/origin condition occurs in Embeds itself. -/
theorem resources_of_embedding (allocation : Allocation Provenance BorrowTree)
    (completion : Completion) (protections : ProtectedTags) (grant : UniIndex)
    (byte : Nat) (embedding : Embeds allocation protections completion grant byte .exclusive)
    (segment : RangeMapSegment LocationTree)
    (member : segment ∈ allocation.extra.locations.entries.toList)
    (lower : segment.range.start.toNat ≤ byte) (upper : byte < segment.range.stop.toNat) :
    RowResources allocation.extra completion protections grant segment.data :=
  embedding segment member lower upper

private theorem node_array {tree : BorrowTree} {index : UniIndex} {node : TreeNode}
    (present : tree.nodes.get index = some node) : tree.nodes.data[index.toNat]? = some (some node) := by
  unfold UniValMap.get at present
  cases slot : tree.nodes.data[index.toNat]? with
  | none => simp [slot] at present
  | some saved =>
    cases saved with
    | none => simp [slot] at present
    | some actual =>
      have same : actual = node := Option.some.inj (by simpa only [slot] using present)
      subst actual
      rfl

private theorem parent_edge {tree completion protections primary cell cellNode}
    (rep : Representation tree completion protections primary cell cellNode)
    {index : UniIndex} {node : TreeNode} (present : tree.nodes.get index = some node) :
    completion.parents[index.toNat]? = some node.parent := by
  rw [rep.physicalParents,Array.getElem?_map,node_array present]
  rfl

private theorem edge_node {tree completion protections primary cell cellNode}
    (rep : Representation tree completion protections primary cell cellNode)
    {child parent : UniIndex} (edge : completion.parents[child.toNat]? = some (some parent)) :
    ∃ node, tree.nodes.get child = some node ∧ node.parent = some parent := by
  rw [rep.physicalParents,Array.getElem?_map] at edge
  cases slot : tree.nodes.data[child.toNat]? with
  | none => simp [slot] at edge
  | some saved =>
    cases saved with
    | none => simp [slot] at edge
    | some node =>
      refine ⟨node,?_,?_⟩
      · simp only [UniValMap.get,slot]
      · exact Option.some.inj (by simpa only [slot,Option.map_some,Option.bind_some] using edge)

/-- Existing physical ancestry is preserved literally; no root attachment is
inferred merely because a nonprimary node exists. -/
theorem ancestry {tree completion protections primary cell cellNode}
    (rep : Representation tree completion protections primary cell cellNode)
    (graph : GeneralBorrowStructuralHistoryState.GraphState tree)
    {first last : UniIndex} (node : TreeNode) (present : tree.nodes.get last = some node) :
    Below completion first last ↔ Path tree first last := by
  constructor
  · intro below
    obtain ⟨depth⟩ := graph.depth
    induction below generalizing node with
    | refl => exact .refl _ node present
    | @step parent child edge prior ih =>
      obtain ⟨childNode,childAt,physical⟩ := edge_node rep edge
      obtain ⟨parentNode,parentAt,_⟩ := depth.parent child childNode childAt parent physical
      exact .step (ih parentNode parentAt) childNode childAt physical
  · intro path
    clear present node
    induction path with
    | refl => exact .refl _
    | step earlier node nodeAt edge ih => exact .step ((parent_edge rep nodeAt).trans (congrArg some edge)) ih

private theorem authority_of_resources (tree : BorrowTree) (completion : Completion) (protections : ProtectedTags)
    (source : UniIndex) (location : LocationTree)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree location protections)
    (resources : RowResources tree completion protections source location) :
    S05CompletedAncestryReadMutable.Authority tree completion protections source location := by
  intro index node present
  have realized := CandidateCurrentGrantRuntime.realized _ _ (possible index node present) (profile.present index node present)
  obtain ⟨ownedTokens,guards⟩ := resources index node present
  constructor
  · intro below
    exact local_write _ _ realized (token_local _ _ (ownedTokens below))
  · intro outside
    exact foreign_write _ _ realized (no_clash_competing _ _ _ realized (fun clash => outside (guards clash)))

private theorem normal_of_authority (tree : BorrowTree) (completion : Completion) (initial : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (fits : tree.nodes.data.size ≤ 4294967296)
    (position : Nat) (root source : UniIndex) (rootNode : TreeNode)
    (rootSlot : tree.roots[position]? = some root) (rootPresent : tree.nodes.get root = some rootNode)
    (sourcePath : Path tree root source)
    (classification : ∀ index node, tree.nodes.get index = some node → Path tree root index →
      (Below completion index source ↔ Path tree index source))
    (localRights : ∀ index node, tree.nodes.get index = some node → Path tree root index →
      Below completion index source → LocalWrite
        ((initial.perms.get index).getD node.defaultLocationState) (protections.contains node.tag))
    (foreignRights : ∀ index node, tree.nodes.get index = some node → Path tree root index →
      ¬Below completion index source → ForeignWrite
        ((initial.perms.get index).getD node.defaultLocationState) (protections.contains node.tag)) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree initial protections source) := by
  obtain ⟨actual,found,parentless⟩ := formed.rootNodes root (Array.mem_toList_iff.mpr (Array.mem_of_getElem? rootSlot))
  have same : actual = rootNode := Option.some.inj (found.symm.trans rootPresent)
  subst actual
  obtain ⟨forest⟩ := formed.forest initial protections
  let topology := (source_normal_projection tree initial protections).topology
  have projectedPath := GeneralBorrowPhysicalRootPath.projection_desc tree initial protections root source sourcePath
  have rootValid : root.toNat < topology.nodes.size := projectedPath.valid.1
  have projectedRoot := projection_topology_node tree initial protections root.toNat root rootNode rfl rootPresent
  change (topology.nodes[root.toNat]?.getD ⟨none,[]⟩) = _ at projectedRoot
  have rootShape : topology.nodes[root.toNat] =
      ⟨rootNode.parent.map UniIndex.toNat,rootNode.children.toList.map UniIndex.toNat⟩ := by
    simpa only [Array.getElem?_eq_getElem rootValid,Option.getD_some] using projectedRoot
  have rootParentless : (topology.nodes[root.toNat]'rootValid).parent = none := by
    rw [rootShape];simp only [parentless,Option.map_none]
  let chosen := GeneralBorrowExposedScopedNormalRoot.component topology forest root.toNat source.toNat
    rootValid rootParentless projectedPath
  refine ⟨⟨chosen,?_⟩⟩
  intro kind slot inside _
  change Desc topology root.toNat slot at inside
  obtain ⟨index,node,indexEq,present,path⟩ := GeneralBorrowProjectedDescPath.desc_path tree initial protections fits
    root rootNode rootPresent slot inside
  obtain ⟨sourceNode,sourcePresent⟩ := sourcePath.present
  let state := (initial.perms.get index).getD node.defaultLocationState
  refine ⟨state,?_,?_⟩
  · rw [←indexEq]
    exact projection_state tree initial protections index.toNat index node (index_self index) rfl present
  · rw [←indexEq,GeneralBorrowNormalPermissionMetadata.held tree initial protections index node present]
    have physical := classification index node present path
    have related := GeneralBorrowProjectedDescPath.relation_local_iff tree initial protections fits depth forest
      source index sourceNode node sourcePresent present
    by_cases localPath : Path tree index source
    · rw [related.mpr localPath]
      exact OrdinaryBorrowAuthorityBridge.local_scalar state _ (localRights index node present path (physical.mpr localPath)) kind
    · have foreignRelation : GeneralBorrowAnchor.relation (source_normal_projection tree initial protections)
          source.toNat index.toNat = .ForeignAccess := by
        cases relation : GeneralBorrowAnchor.relation (source_normal_projection tree initial protections) source.toNat index.toNat with
        | LocalAccess => exact False.elim (localPath (related.mp relation))
        | ForeignAccess => rfl
      rw [foreignRelation]
      have raw := foreignRights index node present path (fun below => localPath (physical.mp below))
      obtain ⟨next,delta,success,_⟩ := S05RawAuthorityStepPreservation.foreign_step state _ kind raw
      exact (DuplicatePrefixScalarAuthorization.compatible_iff state kind .ForeignAccess _ raw.1).mpr ⟨next,delta,success⟩



open GeneralBorrowWildcardVirtualLeaf
open GeneralBorrowWildcardVirtualLeafFrame (materialized_other)

set_option backward.isDefEq.respectTransparency true in
set_option backward.dsimp.instances false in
set_option maxHeartbeats 500000 in
theorem cell_effect (tree : BorrowTree) (location : LocationTree) (root : UniIndex)
    (node : TreeNode) (maximum : Option BorTag) (kind : AccessKind) (protections : ProtectedTags)
    (present : tree.nodes.get root = some node) (leaf : node.children = #[])
    (parents : GeneralBorrowExposure.ParentDepth tree.nodes) (parentless : node.parent = none)
    (foreignData : onlyForeign node maximum = true ∨
      GeneralBorrowWildcardRelatednessBounds.count location.exposedCache root kind = 0)
    (hidden : node.isExposed = false)
    (cellState : (GeneralBorrowWildcardVirtualLeaf.effective location root node).permission = .Cell)
    (unheld : protections.contains node.tag = false)
    (owned : GeneralBorrowPermissions.ForeignOwned (GeneralBorrowWildcardVirtualLeaf.effective location root node)
      (protections.contains node.tag)) :
    ∃ after, tree.performWildcardAccessAt location root maximum kind protections true =
      ⟨after,.Completed⟩ ∧
      GeneralBorrowPermissions.ForeignOwned (GeneralBorrowWildcardVirtualLeaf.effective after root node) (protections.contains node.tag) ∧
      GeneralBorrowWildcardVirtualLeafFrame.Frame root location after ∧
      (GeneralBorrowWildcardVirtualLeaf.effective after root node).permission = .Cell ∧
      (GeneralBorrowWildcardVirtualLeaf.effective after root node).accessed = (GeneralBorrowWildcardVirtualLeaf.effective location root node).accessed ∧
      after.exposedCache = location.exposedCache := by
  have nonempty : 0 < tree.nodes.size := by
    have valid := GeneralBorrowNodeUpdate.lookup_valid tree.nodes root node present
    unfold UniValMap.size
    omega
  have notPast : ¬ 2 > tree.nodes.size*2+1 := by omega
  have notPast1 : ¬ 1 > tree.nodes.size*2+1 := by omega
  have related : location.exposedCache.accessRelatedness root root kind true
      (onlyForeign node maximum) = some .ForeignAccess := by
    rw [GeneralBorrowWildcardRelatednessBounds.root_classify]
    rcases foreignData with clamp | zero
    · simp [clamp]
    · simp [zero]
  unfold onlyForeign at related
  obtain skip | ⟨recorded,next,transition,record,access,preserved⟩ :=
    GeneralBorrowPermissions.visit_success (GeneralBorrowWildcardVirtualLeaf.effective location root node) .ForeignAccess
      (protections.contains node.tag) kind owned
  · refine ⟨location,?_,owned,(fun _ _ => ⟨rfl,rfl⟩),cellState,rfl,rfl⟩
    clear hidden cellState unheld
    unfold BorrowTree.performWildcardAccessAt
    simp only [Id.run,bind,pure,ForIn.forIn]
    name_range_scan
    have step1 : scan () (location,false,.Completed,#[(root,false)],0) =
        .yield (location,false,.Completed,#[],1) := by
      simp only [scan]
      try unfold_leaf_helpers
      simp [present,notPast1,Id.run,bind,pure]
      try unfold_leaf_helpers
      cases maximum <;> simp_all [GeneralBorrowWildcardVirtualLeaf.effective,AccessRelatedness.isForeign]
      all_goals try unfold_leaf_helpers
      all_goals simp_all [GeneralBorrowWildcardVirtualLeaf.effective,AccessRelatedness.isForeign]
    have step2 : scan () (location,false,.Completed,#[],1) =
        .done (location,false,.Completed,#[],1) := by simp [scan,bind,pure]
    rw [Lean.Loop.forIn_eq_of_monadTail]
    simp only [step1,bind,pure]
    rw [Lean.Loop.forIn_eq_of_monadTail]
    simp only [step2,bind,pure]
    rfl
  · have recurse : (GeneralBorrowWildcardVirtualLeaf.effective location root node).skipIfKnownNoop kind .ForeignAccess = .Recurse := by
      unfold LocationState.recordNewAccess at record
      split at record <;> simp_all
    let updated : LocationTree := {location with perms :=
      ((location.perms.orInsert root node.defaultLocationState).1.insert root recorded).insert root next}
    let update := location.exposedCache.updateExposure tree.nodes root
      ((GeneralBorrowWildcardVirtualLeaf.effective location root node).permission.strongestAllowedLocalAccess (protections.contains node.tag))
      (next.permission.strongestAllowedLocalAccess (protections.contains node.tag))
    have cacheOK : update.outcome = .ok () :=
      GeneralBorrowExposure.update_exposure_succeeds location.exposedCache tree.nodes parents root node present _ _
    let after : LocationTree := {updated with exposedCache :=
      if node.isExposed && !transition.isNoop then update.cache else location.exposedCache}
    have same : after.perms.get root = some next := by
      dsimp only [after,updated]
      exact GeneralBorrowFreshLocation.get_same ((location.perms.orInsert root node.defaultLocationState).1.insert root recorded) root next
    have afterOwned : GeneralBorrowPermissions.ForeignOwned (GeneralBorrowWildcardVirtualLeaf.effective after root node)
        (protections.contains node.tag) := by
      simpa only [GeneralBorrowWildcardVirtualLeaf.effective,same,Option.getD_some,GeneralBorrowPermissions.Owned] using preserved
    have afterFrame : GeneralBorrowWildcardVirtualLeafFrame.Frame root location after := by
      intro query different
      constructor
      · dsimp only [after,updated]
        rw [GeneralBorrowFreshLocation.get_other _ root query next different,
          GeneralBorrowFreshLocation.get_other _ root query recorded different]
        exact materialized_other location root node query different
      · change (if node.isExposed && !transition.isNoop then update.cache else location.exposedCache).nodes.get query = _
        by_cases active : (node.isExposed && !transition.isNoop) = true
        · simp only [active,ite_true]
          exact GeneralBorrowWildcardRootCacheFrame.update_other location.exposedCache tree.nodes root query node
            present parentless different _ _
        · simp only [active,Bool.false_eq_true,ite_false]
    have recPermission := GeneralBorrowEventTransitionMetadata.record_permission _ _ kind .ForeignAccess record
    have recAccessed : recorded.accessed = (GeneralBorrowWildcardVirtualLeaf.effective location root node).accessed := by
      unfold LocationState.recordNewAccess at record
      split at record <;> cases record <;> rfl
    have retained : next.permission = .Cell ∧ next.accessed = (GeneralBorrowWildcardVirtualLeaf.effective location root node).accessed := by
      have nextEq : (recorded.performAccess kind .ForeignAccess (protections.contains node.tag)).resultingState = next := by
        rw [access]
        rfl
      have recCell : recorded.permission = .Cell := recPermission.trans cellState
      have result : next.permission = .Cell ∧ next.accessed = recorded.accessed := by
        rw [←nextEq,unheld]
        rcases recorded with ⟨permission,accessed,sifa⟩
        dsimp only at recCell
        subst permission
        cases accessed <;> cases kind <;> exact ⟨rfl,rfl⟩
      exact ⟨result.1,result.2.trans recAccessed⟩
    have outputState : GeneralBorrowWildcardVirtualLeaf.effective after root node = next := by
      simp only [GeneralBorrowWildcardVirtualLeaf.effective,same,Option.getD_some]
    refine ⟨after,?_,afterOwned,afterFrame,by rw [outputState];exact retained.1,
      by rw [outputState];exact retained.2,?_⟩
    ·
      clear afterOwned afterFrame same retained outputState hidden cellState unheld
      unfold BorrowTree.performWildcardAccessAt
      simp only [Id.run,bind,pure,ForIn.forIn]
      name_range_scan
      have step1 : scan () (location,false,.Completed,#[(root,false)],0) =
          .yield (location,false,.Completed,#[(root,true)],1) := by
        simp only [scan]
        try unfold_leaf_helpers
        simp [present,leaf,notPast1,Id.run,bind,pure]
        try unfold_leaf_helpers
        cases maximum <;> simp_all [GeneralBorrowWildcardVirtualLeaf.effective,AccessRelatedness.isForeign,leaf]
        all_goals try unfold_leaf_helpers
        all_goals simp_all [GeneralBorrowWildcardVirtualLeaf.effective,AccessRelatedness.isForeign,leaf]
      let witness := node.isExposed &&
        ((GeneralBorrowWildcardVirtualLeaf.effective location root node).permission.strongestAllowedLocalAccess (protections.contains node.tag)).allows kind &&
        (maximum.isNone || maximum.any (fun tag => tag.value >= node.tag.value))
      have step2 : scan () (location,false,.Completed,#[(root,true)],1) =
          .yield (after,witness,.Completed,#[],2) := by
        dsimp only [witness]
        simp only [scan]
        try unfold_leaf_helpers
        simp [present,notPast,Id.run,bind,pure]
        try unfold_leaf_helpers
        cases maximum <;> simp_all [GeneralBorrowWildcardVirtualLeaf.effective,after,updated,update,UniValMap.orInsert,
          LocationState.AccessResult.resultingState]
        all_goals try unfold_leaf_helpers
        all_goals try simp_all [GeneralBorrowWildcardVirtualLeaf.effective,after,updated,update,UniValMap.orInsert,LocationState.AccessResult.resultingState]
        all_goals cases stored : location.perms.get root <;> simp_all [GeneralBorrowWildcardVirtualLeaf.effective,after,updated,update,UniValMap.orInsert,LocationState.AccessResult.resultingState]
        all_goals try simp only [cacheOK]
        all_goals split <;> simp_all [after,updated,update,UniValMap.orInsert,LocationState.AccessResult.resultingState]
        all_goals cases exposedEq : node.isExposed <;> simp_all
        all_goals split <;> try simp_all [Bool.and_eq_false_iff]
        all_goals cases allowedEq : ((GeneralBorrowWildcardVirtualLeaf.effective location root node).permission.strongestAllowedLocalAccess (protections.contains node.tag)).allows kind <;> simp_all [GeneralBorrowWildcardVirtualLeaf.effective]
        all_goals simp_all only [UInt64.lt_iff_toNat_lt,UInt64.le_iff_toNat_le]
        all_goals grind
      have step3 : scan () (after,witness,.Completed,#[],2) =
          .done (after,witness,.Completed,#[],2) := by simp [scan,bind,pure]
      rw [Lean.Loop.forIn_eq_of_monadTail]
      simp only [step1,bind,pure]
      rw [Lean.Loop.forIn_eq_of_monadTail]
      simp only [step2,bind,pure]
      rw [Lean.Loop.forIn_eq_of_monadTail]
      simp only [step3,bind,pure]
      simp
    · dsimp only [after]
      simp [hidden]

private theorem cell_runtime (tree : BorrowTree) (before after : LocationTree)
    (protections : ProtectedTags) (cell : UniIndex) (node : TreeNode)
    (present : tree.nodes.get cell = some node)
    (unheld : protections.contains node.tag = false)
    (beforeCell : (RawState before cell node).permission = .Cell)
    (afterCell : (RawState after cell node).permission = .Cell)
    (cache : after.exposedCache = before.exposedCache)
    (frame : GeneralBorrowWildcardVirtualLeafFrame.Frame cell before after)
    (coherent : LocationCoherent tree before protections)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree before protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree before) :
    LocationCoherent tree after protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree after protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree after := by
  have other : ∀ index saved, tree.nodes.get index = some saved → index ≠ cell →
      RawState after index saved = RawState before index saved := by
    intro index saved _ different
    unfold RawState
    rw [(frame index different).1]
  have permission : ∀ index saved, tree.nodes.get index = some saved →
      (RawState after index saved).permission = (RawState before index saved).permission := by
    intro index saved found
    by_cases same : index = cell
    · subst index
      have eq : saved = node := Option.some.inj (found.symm.trans present)
      subst saved
      rw [beforeCell,afterCell]
    · rw [other index saved found same]
  refine ⟨?_,?_,?_⟩
  · intro query kind
    rw [cache,coherent query kind]
    apply congrArg UInt16.ofNat
    apply GeneralBorrowExposurePermissionUpdate.cardinality_congr
    intro index saved found
    change (RawState before index saved).permission.strongestAllowedLocalAccess _ =
      (RawState after index saved).permission.strongestAllowedLocalAccess _
    rw [permission index saved found]
  · constructor
    · intro index saved found
      by_cases same : index = cell
      · subst index
        have eq : saved = node := Option.some.inj (found.symm.trans present)
        subst saved
        change GeneralBorrowSifaPermissionConsistency.Consistent (RawState after cell node) _
        unfold GeneralBorrowSifaPermissionConsistency.Consistent
        refine ⟨.Write,?_,?_⟩
        · rw [afterCell,unheld]; rfl
        · cases (RawState after cell node).idempotentForeignAccess <;> decide
      · change GeneralBorrowSifaPermissionConsistency.Consistent (RawState after index saved) _
        rw [other index saved found same]
        exact profile.present index saved found
    · intro index absent
      have different : index ≠ cell := by intro same; subst index; rw [present] at absent; contradiction
      rw [(frame index different).1]
      exact profile.vacant index absent
  · intro index saved found
    change (RawState after index saved).possible = true
    by_cases same : index = cell
    · subst index
      have eq : saved = node := Option.some.inj (found.symm.trans present)
      subst saved
      simp [LocationState.possible,afterCell,Permission.isUnique]
    · rw [other index saved found same]
      exact possible index saved found

private theorem resources_of_authority (tree : BorrowTree) (completion : Completion)
    (protections : ProtectedTags) (source : UniIndex) (location : LocationTree)
    (rights : S05CompletedAncestryReadMutable.Authority tree completion protections source location) :
    RowResources tree completion protections source location := by
  intro index node present
  obtain ⟨localRights,foreignRights⟩ := rights index node present
  constructor
  · intro below
    have allowed := localRights below
    generalize stateEq : RawState location index node = state at allowed ⊢
    rcases state with ⟨permission,accessed,sifa⟩
    cases permission with
    | ReservedFrz c => cases c <;> cases held : (protections.contains node.tag) <;>
        simp_all [LocalWrite,tokens,denote]
    | Cell | ReservedIM | Unique | Frozen | Disabled => simp_all [LocalWrite,tokens,denote]
  · intro clash
    by_cases inside : Below completion index source
    · exact inside
    have allowed := foreignRights inside
    generalize stateEq : RawState location index node = state at allowed clash
    rcases state with ⟨permission,accessed,sifa⟩
    cases permission with
    | ReservedFrz c => cases c <;> cases accessed <;> cases held : (protections.contains node.tag) <;>
        simp_all [ForeignWrite,Clash,CandidateCurrentGrantResources.guard,denote]
    | Cell | ReservedIM | Unique | Frozen | Disabled =>
        cases accessed <;> cases held : (protections.contains node.tag) <;>
        simp_all [ForeignWrite,Clash,CandidateCurrentGrantResources.guard,denote]

/-- Actual later-root callback. The implementation may record a new SIFA;
only actual success, competing-resource compatibility, and outside lookups are
framed. The fixed family ancestry is not reselected. -/
theorem cell_access (tree : BorrowTree) (completion : Completion)
    (protections : ProtectedTags) (primary cell grant : UniIndex) (node : TreeNode)
    (rep : Representation tree completion protections primary cell node)
    (location : LocationTree) (maximum : Option BorTag) (kind : AccessKind)
    (parents : GeneralBorrowExposure.ParentDepth tree.nodes)
    (state : (RawState location cell node).permission = .Cell)
    (outside : ¬ Below completion cell grant)
    (resources : RowResources tree completion protections grant location) :
    ∃ after, tree.performWildcardAccessAt location cell maximum kind protections true =
        ⟨after,.Completed⟩ ∧
      GeneralBorrowPermissions.ForeignOwned (RawState after cell node)
        (protections.contains node.tag) ∧
      GeneralBorrowWildcardVirtualLeafFrame.Frame cell location after ∧
      RowResources tree completion protections grant after := by
  have owned : GeneralBorrowPermissions.ForeignOwned
      (GeneralBorrowWildcardVirtualLeaf.effective location cell node)
      (protections.contains node.tag) := by
    change (RawState location cell node).possible = true ∧ _
    refine ⟨?_,.inl rep.cellUnheld⟩
    simp [LocationState.possible,state,Permission.isUnique]
  obtain ⟨after,actual,compatible,frame⟩ :=
    GeneralBorrowWildcardVirtualLeafFrame.access tree location cell node maximum kind
      protections rep.cellPresent rep.cellLeaf parents rep.cellParent owned
  refine ⟨after,actual,compatible,frame,?_⟩
  intro index saved found
  by_cases same : index = cell
  · subst index
    have equal : saved = node := Option.some.inj (found.symm.trans rep.cellPresent)
    subst saved
    constructor
    · intro below
      exact False.elim (outside below)
    · intro clash
      simp [rep.cellUnheld,denote,CandidateCurrentGrantResources.guard,Clash] at clash
  · have lookups := (frame index same).1
    have raw : RawState after index saved = RawState location index saved := by
      unfold RawState
      rw [lookups]
    simpa only [raw] using resources index saved found

/-- One actual concrete Write, including the interpreter's later-root loop.
The current semantic token/guard assignment supplies all raw tables internally.
The SAME ancestry/grant/resources survive; the physical ambient root is retained.
This bounded theorem is not a definition of ordinary admission. -/
theorem write (tree : BorrowTree) (completion : Completion) (initial : LocationTree)
    (protections : ProtectedTags) (primary cell source : UniIndex)
    (cellNode sourceNode : TreeNode)
    (rep : Representation tree completion protections primary cell cellNode)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (sourcePresent : tree.nodes.get source = some sourceNode)
    (sourcePath : Path tree primary source)
    (cellState : (RawState initial cell cellNode).permission = .Cell)
    (coherent : LocationCoherent tree initial protections)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial)
    (resources : RowResources tree completion protections source initial)
    (mode : ChildrenVisitMode) (range : ByteRange) :
    let actual := source_tree_access_at tree initial (some source) .Write protections mode range
    source_access_status actual = none ∧
      LocationCoherent tree (source_access_location actual) protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree (source_access_location actual) protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree (source_access_location actual) ∧
      RowResources tree completion protections source (source_access_location actual) := by
  have slot : tree.roots[0]? = some primary := by rw [rep.roots]; rfl
  obtain ⟨primaryNode,primaryAt,parentless⟩ := formed.rootNodes primary
    (Array.mem_toList_iff.mpr (Array.mem_of_getElem? slot))
  obtain ⟨depth⟩ := formed.depth
  have rights := authority_of_resources tree completion protections source initial possible profile resources
  have classification : ∀ index node, tree.nodes.get index = some node → Path tree primary index →
      (Below completion index source ↔ Path tree index source) := by
    intro index node found _
    exact ancestry rep formed sourceNode sourcePresent
  obtain ⟨normal⟩ := normal_of_authority tree completion initial protections formed depth formed.fits
    0 primary source primaryNode slot primaryAt sourcePath classification
    (fun index node found _ => (rights index node found).1)
    (fun index node found _ => (rights index node found).2)
  have distinct : tree.roots.toList.Nodup := by simp [rep.roots,rep.distinct]
  have notBelow : ¬ Below completion cell source := by
    intro below
    exact rep.distinct (CompletedBorrowAncestry.physical_roots_unique primaryAt parentless
      rep.cellPresent rep.cellParent sourcePath ((ancestry rep formed sourceNode sourcePresent).mp below))
  have result := CurrentCallEmptyEntryNormalWrite.write_authority tree completion initial protections
    formed distinct 0 primary source primaryNode sourceNode slot primaryAt sourcePresent sourcePath
    normal rights classification coherent profile possible (fun position root rootAt different current currentRights cache sifa gp currentFrame => by
      have positionOne : position = 1 := by
        cases position with
        | zero =>
          have eq : root = primary := by simpa [rep.roots] using rootAt.symm
          exact False.elim (different eq)
        | succ n =>
          cases n with
          | zero => rfl
          | succ n => simp [rep.roots] at rootAt
      subst position
      have rootCell : root = cell := by simpa [rep.roots] using rootAt.symm
      subst root
      have row : current.perms.get cell = initial.perms.get cell :=
        currentFrame cell cellNode rep.cellPresent (.refl cell cellNode rep.cellPresent)
      have currentCell : (RawState current cell cellNode).permission = .Cell := by
        unfold RawState
        rw [row]
        exact cellState
      have zero : GeneralBorrowWildcardRelatednessBounds.count current.exposedCache cell .Write = 0 := by
        have counted := cache cell .Write
        rw [S03EmptyPopFactsAuthorization.leaf_cardinality tree current protections formed cell cellNode
          rep.cellPresent rep.cellLeaf rep.cellHidden .Write] at counted
        change ((current.exposedCache.nodes.get cell).getD {}).localWrites = 0 at counted
        change ((current.exposedCache.nodes.get cell).getD {}).localWrites.toNat = 0
        rw [counted]
        rfl
      have owned : GeneralBorrowPermissions.ForeignOwned
          (GeneralBorrowWildcardVirtualLeaf.effective current cell cellNode)
          (protections.contains cellNode.tag) := by
        refine ⟨gp cell cellNode rep.cellPresent,.inl rep.cellUnheld⟩
      obtain ⟨after,actual,compatible,frame,afterCell,_,sameCache⟩ := cell_effect tree current cell cellNode
        (some primaryNode.tag) .Write protections rep.cellPresent rep.cellLeaf depth rep.cellParent
        (.inr zero) rep.cellHidden currentCell rep.cellUnheld owned
      have runtime := cell_runtime tree current after protections cell cellNode rep.cellPresent rep.cellUnheld
        currentCell afterCell sameCache frame cache sifa gp
      have afterRights : S05CompletedAncestryReadMutable.Authority tree completion protections source after := by
        intro index node found
        by_cases same : index = cell
        · subst index
          have eq : node = cellNode := Option.some.inj (found.symm.trans rep.cellPresent)
          subst node
          constructor
          · intro below
            exact False.elim (notBelow below)
          · intro _
            exact ⟨runtime.2.2 cell cellNode rep.cellPresent,by simp [rep.cellUnheld]⟩
        · unfold RawState
          rw [(frame index same).1]
          exact currentRights index node found
      dsimp only
      have virtual : ((1 : Nat) != 0) = true := rfl
      rw [virtual,actual]
      refine ⟨rfl,runtime.1,runtime.2.1,runtime.2.2,?_,afterRights⟩
      intro query outside
      exact (frame query (fun same => outside (by subst query; exact .refl cell cellNode rep.cellPresent))).1)
    mode range
  exact ⟨result.1,result.2.1,result.2.2.1,result.2.2.2.1,
    resources_of_authority tree completion protections source _ result.2.2.2.2.2⟩


end
end DuplicatePrefix.CurrentCallOptionalCellAccess

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallOptionalCellAccess.").length != 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved optional Cell access dependency {dependency}"
