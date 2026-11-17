import duplicate_prefix.S05SharedConstructorDisjoint
import duplicate_prefix.GeneralBorrowProtectedConstructorRuntime
import duplicate_prefix.GeneralBorrowWildcardConstructorExact

/-! Actual protected mutable construction preserves an old distinct anchor's
node facets and activity. No completed parent map, leaf, or hidden assumption
is needed; this helper makes no original-parent authority claim. -/
namespace DuplicatePrefix.CurrentCallProtectedConstructorOldFacets
open Miri Miri.ABI Miri.Memory Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowView GeneralBorrowProjection
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- Inserting another slot preserves the old anchor's activity at every byte.
The real range iterator may split segments; no unchanged-tree claim is used. -/
private theorem materialized_active (tree : BorrowTree) (child target : UniIndex)
    (different : target ≠ child) (offset len : Size) (kind : AccessKind) (lower upper : UInt64)
    (well : tree.locations.WellFormed)
    (bounds : offset.bytes.toNat+len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree target kind lower upper) :
    GeneralBorrowFreshActiveWithin.Profile
      (tree.locations.modifyRange offset len (fun _ location =>
        GeneralBorrowFreshMaterialization.materialized location child GeneralBorrowFreshChild.inside)).state
      target kind lower upper := by
  let prepared := tree.locations.iterMut offset len
  let modify := fun (_ : ByteRange) location =>
    GeneralBorrowFreshMaterialization.materialized location child GeneralBorrowFreshChild.inside
  let updated := (tree.locations.modifyRange offset len modify).state
  have good := GeneralRangeMapOriginPrepare.iter_mut tree.locations offset len well bounds
  have old := GeneralBorrowFreshActiveWithin.refines tree.locations prepared.state good.2.1 target kind lower upper active
  have sizes : updated.entries.size = prepared.state.entries.size := by
    dsimp only [updated,prepared]
    rw [GeneralBorrowFreshModify.state_exact tree.locations offset len modify well bounds,GeneralBorrowFreshModify.fold_size]
  intro point location valueAt state stored accessed accessKind associated
  obtain ⟨position,valid,start,stop,data⟩ := valueAt
  have oldValid : position < prepared.state.entries.size := by
    change position < updated.entries.size at valid
    omega
  obtain ⟨_,entry⟩ := GeneralBorrowFreshModify.entry_exact tree.locations offset len modify
    (fun _ location => GeneralBorrowFreshInstallation.materialized_idempotent location child GeneralBorrowFreshChild.inside)
    well bounds position oldValid
  change updated.entries[position] = _ at entry
  have range : updated.entries[position].range = prepared.state.entries[position].range := by
    have known := congrArg RangeMapSegment.range entry
    split at known <;> exact known
  change updated.entries[position].data = location at data
  have lookup : updated.entries[position].data.perms.get target = prepared.state.entries[position].data.perms.get target := by
    rw [entry]
    split
    · exact GeneralBorrowFreshLocation.get_other _ _ _ _ different
    · rfl
  rw [←data,lookup] at stored
  rw [range] at start stop
  exact old point prepared.state.entries[position].data ⟨position,oldValid,start,stop,rfl⟩ state stored accessed accessKind associated

private theorem old_node (tree after : BorrowTree) (child parent target : UniIndex)
    (parentNode targetNode : TreeNode) (newTag : BorTag) (mapping : UniKeyMap BorTag)
    (locations : DedupRangeMap LocationTree) (vacant : tree.nodes.get child = none)
    (targetAt : tree.nodes.get target = some targetNode) (different : target ≠ parent)
    (shape : treeShape after = treeShape (GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode
      (GeneralBorrowFreshChild.child newTag parent) mapping locations))
    (exposure : GeneralBorrowFreshMetadataChildSifa.exposureShape after =
      GeneralBorrowFreshMetadataChildSifa.exposureShape (GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode
        (GeneralBorrowFreshChild.child newTag parent) mapping locations)) :
    ∃ next, after.nodes.get target = some next ∧ next.tag = targetNode.tag ∧ next.parent = targetNode.parent ∧
      next.children = targetNode.children ∧ next.isExposed = targetNode.isExposed := by
  let stage := GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode
    (GeneralBorrowFreshChild.child newTag parent) mapping locations
  have notChild : target ≠ child := by intro same; rw [same,vacant] at targetAt; cases targetAt
  have atStage : stage.nodes.get target = some targetNode := by
    dsimp only [stage,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,GeneralBorrowFreshNode.attachedNodes]
    rw [GeneralBorrowFreshLocation.get_other _ _ _ _ different,GeneralBorrowFreshLocation.get_other _ _ _ _ notChild]
    exact targetAt
  obtain ⟨next,found,tag,parentEq,children,_⟩ := GeneralBorrowFreshMetadata.node_fields stage after shape target targetNode atStage
  have flags := GeneralBorrowFreshMetadataChildSifa.lookup_exposure stage after exposure target
  rw [found,atStage] at flags
  exact ⟨next,found,tag,parentEq,children,by simpa only [Option.map_some,Option.some.injEq] using flags⟩

theorem concrete (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent target : UniIndex) (parentNode targetNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (targetAt : tree.nodes.get target = some targetNode) (different : target ≠ parent)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (kind : AccessKind) (lower upper : UInt64)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree target kind lower upper) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    (∃ next, actual.tree.nodes.get target = some next ∧ next.tag = targetNode.tag ∧ next.parent = targetNode.parent ∧
      next.children = targetNode.children ∧ next.isExposed = targetNode.isExposed) ∧
    GeneralBorrowFreshActiveWithin.ActiveWithin actual.tree target kind lower upper := by
  let rank := GeneralBorrowStructuralHistoryMutable.depth tree runtime.formed.toState
  have slot := GeneralBorrowStructuralHistoryMutable.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildMutable.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        noFree,aligned,fits,offset,len,nonzero,runtime.formed.well,bounds⟩
    let child := GeneralBorrowFreshMetadataChildMutable.index input
    have vacant : tree.nodes.get child = none := by
      have atEnd : child.toNat = tree.nodes.data.size := GeneralBorrowFreshMetadataChildMutable.at_end input
      simp only [UniValMap.get,atEnd,Array.getElem?_eq_none (Nat.le_refl _)]
    have notChild : target ≠ child := by intro same; rw [same,vacant] at targetAt; cases targetAt
    have staged : GeneralBorrowFreshActiveWithin.ActiveWithin (GeneralBorrowFreshMetadataChildMutable.stage input) target kind lower upper :=
      materialized_active tree child target notChild (Size.ofBytes offset) (Size.ofBytes len) kind lower upper runtime.formed.well bounds active
    exact ⟨old_node tree _ child parent target parentNode targetNode newTag _ _ vacant targetAt different
      (GeneralBorrowFreshMetadataChildMutable.shape input) (GeneralBorrowFreshMetadataChildMutable.exposure input),
      GeneralBorrowFreshActiveWithin.shape_preserves _ _ (GeneralBorrowFreshMetadataChildMutable.shape input) target kind lower upper staged⟩
  | reuse child available bounded vacant slack =>
    let input : GeneralBorrowFreshMetadataChildMutableReuse.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        child,available,bounded,vacant,slack,offset,len,nonzero,runtime.formed.well,bounds⟩
    have notChild : target ≠ child := by intro same; rw [same,vacant] at targetAt; cases targetAt
    have staged : GeneralBorrowFreshActiveWithin.ActiveWithin (GeneralBorrowFreshMetadataChildMutableReuse.stage input) target kind lower upper :=
      materialized_active tree child target notChild (Size.ofBytes offset) (Size.ofBytes len) kind lower upper runtime.formed.well bounds active
    exact ⟨old_node tree _ child parent target parentNode targetNode newTag _ _ vacant targetAt different
      (GeneralBorrowFreshMetadataChildMutableReuse.shape input) (GeneralBorrowFreshMetadataChildMutableReuse.exposure input),
      GeneralBorrowFreshActiveWithin.shape_preserves _ _ (GeneralBorrowFreshMetadataChildMutableReuse.shape input) target kind lower upper staged⟩

/-- A wildcard constructor only inserts its fresh root. Every old anchor keeps
its exact node payload and bytewise activity through actual append or reuse. -/
theorem wildcard (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (newTag : BorTag) (target : UniIndex) (targetNode : TreeNode)
    (targetAt : tree.nodes.get target=some targetNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1≤4294967295)
    (offset len : UInt64) (nonzero : len≠0)
    (bounds : offset.toNat+len.toNat≤tree.locations.size.bytes.toNat)
    (kind : AccessKind) (lower upper : UInt64)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree target kind lower upper) :
    let actual := tree.newChild (Size.ofBytes offset) .wildcard newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    (∃ next, actual.tree.nodes.get target=some next ∧ next.tag=targetNode.tag ∧ next.parent=targetNode.parent ∧
      next.children=targetNode.children ∧ next.isExposed=targetNode.isExposed) ∧
    GeneralBorrowFreshActiveWithin.ActiveWithin actual.tree target kind lower upper := by
  obtain ⟨mapping,index,inserted,_,vacant,_,_,_⟩ := GeneralBorrowWildcardConstructorSlot.select tree global runtime newTag fresh room (.ReservedFrz false) .None
  have exactResult := GeneralBorrowWildcardConstructorExact.exact tree runtime.formed.toState newTag fresh room mapping index inserted
    (.ReservedFrz false) .None GeneralBorrowFreshChild.inside true rfl rfl rfl rfl rfl offset len nonzero bounds
  have different : target≠index := by intro same;rw [same,vacant] at targetAt;cases targetAt
  rw [exactResult]
  refine ⟨⟨targetNode,?_,rfl,rfl,rfl,rfl⟩,?_⟩
  · change (tree.nodes.insert index (WildcardHitZeroConstructor.rootNode newTag (.ReservedFrz false) .None)).get target=some targetNode
    rw [GeneralBorrowFreshLocation.get_other _ _ _ _ different]
    exact targetAt
  · exact materialized_active tree index target different (Size.ofBytes offset) (Size.ofBytes len) kind lower upper runtime.formed.well bounds active

end DuplicatePrefix.CurrentCallProtectedConstructorOldFacets
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallProtectedConstructorOldFacets" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved protected old-facet dependency {dependency}"
