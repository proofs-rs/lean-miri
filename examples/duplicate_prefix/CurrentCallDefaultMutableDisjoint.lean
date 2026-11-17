import duplicate_prefix.CurrentCallResourceDefaultMutable
import duplicate_prefix.CurrentCallSharedConstructorFrame
import duplicate_prefix.CurrentCallProtectedConstructorOldFacets
namespace DuplicatePrefix.CurrentCallDefaultMutableDisjoint
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership OrdinaryBorrowAuthority GeneralBorrowView GeneralBorrowProjection GeneralRangeMapOrigins
open S05ConcreteProtectedChildCompletion S05CompletedAncestryReadMutable CurrentCallResourceNormalization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
open Lean Elab Term in
elab "default_frame_rule " suffix:str : term => do
  let found := (←getEnv).constants.toList.filter (fun (name,_)=>name.toString.endsWith suffix.getString)
  match found with
  | [(name,_)]=>return mkConst name
  | _=>throwError "expected unique checked Default frame helper {suffix.getString}"
noncomputable section
private theorem no_vacant_ancestor (tree : BorrowTree) (completion : Completion)
    (complete : ParentInterpretation tree completion) (child target : UniIndex)
    (vacant : tree.nodes.get child = none) (live : ∃ node, tree.nodes.get target = some node)
    (path : Below completion child target) : False := by
  induction path with
  | refl => obtain ⟨node,present⟩ := live; rw [vacant] at present; cases present
  | @step predecessor target edge path induction =>
    exact induction ((complete.edgeLive target predecessor edge).2)

private theorem stage_location (tree : BorrowTree) (completion : Completion) (held : ProtectedTags)
    (complete : ParentInterpretation tree completion) (child parent target : UniIndex) (parentNode targetNode : TreeNode) (tag : BorTag)
    (vacant : tree.nodes.get child = none) (parentAt : tree.nodes.get parent = some parentNode)
    (targetAt : tree.nodes.get target = some targetNode)
    (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree) (location : LocationTree)
    (clean : location.perms.get child = none)
    (unheld : held.contains tag=false)
    (authority : Authority tree completion held target location) :
    Authority (GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode
      (GeneralBorrowFreshDefaultChild.child tag parent) mapping locations) (extend completion child parent) held target location := by
  intro index node present
  by_cases new : index = child
  · subst index
    dsimp only [GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,
      GeneralBorrowFreshNode.attachedNodes] at present
    have different : parent ≠ child := by intro same; rw [same,vacant] at parentAt; cases parentAt
    rw [GeneralBorrowFreshLocation.get_other _ _ _ _ (Ne.symm different),GeneralBorrowFreshLocation.get_same] at present
    have nodeEq : node = GeneralBorrowFreshDefaultChild.child tag parent := Option.some.inj present.symm
    have outside : ¬Below (extend completion child parent) child target := by
      intro path
      exact no_vacant_ancestor tree completion complete child target vacant ⟨targetNode,targetAt⟩
        ((CurrentCallResourceChild.old_ancestry_iff tree completion complete child parent vacant ⟨targetNode,targetAt⟩).mp path)
    constructor
    · intro impossible; exact False.elim (outside impossible)
    · intro _
      simp [RawState,clean,nodeEq,GeneralBorrowFreshDefaultChild.child,TreeNode.defaultLocationState,
        ForeignWrite,LocationState.possible,Permission.isUnique,unheld]
  · have old : ∃ old, tree.nodes.get index = some old ∧ node.tag = old.tag ∧
        node.defaultInitialPermission = old.defaultInitialPermission := by
      dsimp only [GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,
        GeneralBorrowFreshNode.attachedNodes] at present
      by_cases isParent : index = parent
      · subst index
        rw [GeneralBorrowFreshLocation.get_same] at present
        have same : node = {parentNode with children := parentNode.children.push child} := Option.some.inj present.symm
        exact ⟨parentNode,parentAt,by rw [same],by rw [same]⟩
      · rw [GeneralBorrowFreshLocation.get_other _ _ _ _ isParent,
          GeneralBorrowFreshLocation.get_other _ _ _ _ new] at present
        exact ⟨node,present,rfl,rfl⟩
    obtain ⟨old,oldAt,tagEq,defaultEq⟩ := old
    have effective : stateShape (RawState location index node) = stateShape (RawState location index old) := by
      unfold RawState
      cases location.perms.get index <;> simp [stateShape,TreeNode.defaultLocationState,defaultEq]
    have scalar := (default_frame_rule ".CurrentCallResourceDefaultMutable.authority_state") _ _ effective (held.contains node.tag)
    have original := authority index old oldAt
    rw [←tagEq] at original
    have ancestry := CurrentCallResourceChild.old_ancestry_iff tree completion complete child parent vacant ⟨targetNode,targetAt⟩ (ancestor := index)
    exact ⟨fun below => scalar.1.mpr (original.1 (ancestry.mp below)),
      fun outside => scalar.2.mpr (original.2 (fun below => outside (ancestry.mpr below)))⟩

private theorem stage_owned (tree : BorrowTree) (completion : Completion) (held : ProtectedTags)
    (complete : ParentInterpretation tree completion) (child parent target : UniIndex) (parentNode targetNode : TreeNode) (tag : BorTag)
    (vacant : tree.nodes.get child = none) (parentAt : tree.nodes.get parent = some parentNode)
    (targetAt : tree.nodes.get target = some targetNode)
    (mapping : UniKeyMap BorTag) (offset len lower upper : UInt64) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (disjoint : ∀ point : UInt64, lower.toNat ≤ point.toNat → point.toNat < upper.toNat →
      point.toNat < offset.toNat ∨ (offset+len).toNat ≤ point.toNat)
    (unheld : held.contains tag=false)
    (clean : ∀ position (valid : position < tree.locations.entries.size), tree.locations.entries[position].data.perms.get child = none)
    (owned : OwnedOn (Authority tree completion held target) lower upper tree.locations) :
    let locations := (tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len)
      (fun _ location => GeneralBorrowFreshMaterialization.materialized location child GeneralBorrowFreshDefaultChild.inside)).state
    let stage := GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode
      (GeneralBorrowFreshDefaultChild.child tag parent) mapping locations
    OwnedOn (Authority stage (extend completion child parent) held target) lower upper locations := by
  let locations := (tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len)
    (fun _ location => GeneralBorrowFreshMaterialization.materialized location child GeneralBorrowFreshDefaultChild.inside)).state
  have initial : OwnedOn (fun location => Authority tree completion held target location ∧ location.perms.get child = none)
      lower upper tree.locations := by
    intro position valid positive start stop
    exact ⟨owned position valid positive start stop,clean position valid⟩
  have unchanged := (default_frame_rule ".CurrentCallSharedConstructorFrame.modify_outside_owned") tree.locations (Size.ofBytes offset) (Size.ofBytes len) well bounds
    (fun location => GeneralBorrowFreshMaterialization.materialized location child GeneralBorrowFreshDefaultChild.inside)
    (fun location => GeneralBorrowFreshInstallation.materialized_idempotent location child GeneralBorrowFreshDefaultChild.inside)
    _ lower upper disjoint initial
  dsimp only
  intro position valid positive start stop
  obtain ⟨oldAuthority,oldClean⟩ := unchanged position valid positive start stop
  exact stage_location tree completion held complete child parent target parentNode targetNode tag vacant parentAt targetAt
    mapping locations _ oldClean unheld oldAuthority

/-- The old target may inhabit the SAME allocation as the source window.
Only byte-window disjointness is required. The fresh Default mutable child is a
foreign unheld reservation node at these bytes, and old ancestry remains exact. -/
theorem disjoint (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (complete : ParentInterpretation tree completion)
    (parentTag newTag : BorTag) (parent target : UniIndex) (parentNode targetNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (targetAt : tree.nodes.get target = some targetNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (tagBound : newTag.value.toNat < global.nextPointerTag.value.toNat)
    (unheld : global.protectedTags.contains newTag = false)
    (offset len lower upper : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (disjoint : ∀ point : UInt64, lower.toNat ≤ point.toNat → point.toNat < upper.toNat →
      point.toNat < offset.toNat ∨ (offset+len).toNat ≤ point.toNat)
    (owned : OwnedOn (Authority tree completion global.protectedTags target) lower upper tree.locations) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false
    actual.outcome = .ok () ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global ∧
      actual.tree.locations.size = tree.locations.size ∧ actual.tree.nodes.size ≤ tree.nodes.size+1 ∧
      ∃ child, actual.tree.indexOfTag newTag = some child ∧
        OwnedOn (Authority actual.tree (extend completion child parent) global.protectedTags target)
          lower upper actual.tree.locations := by
  obtain ⟨done,afterRuntime,capacity,growth⟩ := GeneralBorrowDefaultConstructorRuntime.construct
    tree global runtime parentTag newTag parent parentNode tagged present fresh room tagBound unheld offset len nonzero bounds
  obtain ⟨child,lookup,_,_,_⟩ := GeneralBorrowDefaultChildMetadata.construct
    tree global runtime parentTag newTag parent parentNode tagged present fresh room offset len nonzero bounds
  refine ⟨done,afterRuntime,capacity,growth,child,lookup,?_⟩
  let rank := GeneralBorrowStructuralHistoryDefault.depth tree runtime.formed.toState
  let slot := GeneralBorrowStructuralHistoryDefault.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildDefault.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        noFree,aligned,fits,offset,len,nonzero,runtime.formed.well,bounds⟩
    have data := GeneralBorrowFreshMetadataChildDefault.append input
    have same : GeneralBorrowFreshMetadataChildDefault.index input = child := Option.some.inj (data.freshLookup.symm.trans lookup)
    have atEnd : (GeneralBorrowFreshMetadataChildDefault.index input).toNat = tree.nodes.data.size := GeneralBorrowFreshMetadataChildDefault.at_end input
    have vacant : tree.nodes.get (GeneralBorrowFreshMetadataChildDefault.index input) = none := by
      simp only [UniValMap.get,atEnd,Array.getElem?_eq_none (Nat.le_refl _)]
    have clean : ∀ position (valid : position < tree.locations.entries.size),
        tree.locations.entries[position].data.perms.get (GeneralBorrowFreshMetadataChildDefault.index input) = none := by
      intro position valid
      exact (runtime.formed.profile position valid).vacant _ vacant
    have staged := stage_owned tree completion global.protectedTags complete (GeneralBorrowFreshMetadataChildDefault.index input)
      parent target parentNode targetNode newTag vacant present targetAt (GeneralBorrowFreshMetadataChildDefault.mapping input)
      offset len lower upper runtime.formed.well bounds disjoint unheld clean owned
    have result := (default_frame_rule ".CurrentCallResourceDefaultMutable.shape_owned") (GeneralBorrowFreshMetadataChildDefault.stage input)
      (GeneralBorrowFreshMetadataChildDefault.result input) _ global.protectedTags target
      lower upper (GeneralBorrowFreshMetadataChildDefault.shape input) staged
    rw [same] at result
    simpa only [GeneralBorrowFreshMetadataChildDefault.result,input] using result
  | reuse index available bounded vacant slack =>
    let input : GeneralBorrowFreshMetadataChildDefaultReuse.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        index,available,bounded,vacant,slack,offset,len,nonzero,runtime.formed.well,bounds⟩
    have data := GeneralBorrowFreshMetadataChildDefaultReuse.reuse input
    have same : index = child := Option.some.inj (data.freshLookup.symm.trans lookup)
    have clean : ∀ position (valid : position < tree.locations.entries.size),
        tree.locations.entries[position].data.perms.get index = none := by
      intro position valid
      exact (runtime.formed.profile position valid).vacant _ vacant
    have staged := stage_owned tree completion global.protectedTags complete index parent target parentNode targetNode newTag vacant present targetAt
      (GeneralBorrowFreshMetadataChildDefaultReuse.mapping input) offset len lower upper runtime.formed.well bounds disjoint unheld clean owned
    have result := (default_frame_rule ".CurrentCallResourceDefaultMutable.shape_owned") (GeneralBorrowFreshMetadataChildDefaultReuse.stage input)
      (GeneralBorrowFreshMetadataChildDefaultReuse.result input) _ global.protectedTags target
      lower upper (GeneralBorrowFreshMetadataChildDefaultReuse.shape input) staged
    rw [same] at result
    simpa only [GeneralBorrowFreshMetadataChildDefaultReuse.result,input] using result

private theorem materialized_active (tree : BorrowTree) (child target : UniIndex)
    (different : target ≠ child) (offset len : Size) (kind : AccessKind) (lower upper : UInt64)
    (well : tree.locations.WellFormed)
    (bounds : offset.bytes.toNat+len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree target kind lower upper) :
    GeneralBorrowFreshActiveWithin.Profile
      (tree.locations.modifyRange offset len (fun _ location =>
        GeneralBorrowFreshMaterialization.materialized location child GeneralBorrowFreshDefaultChild.inside)).state
      target kind lower upper := by
  let prepared := tree.locations.iterMut offset len
  let modify := fun (_ : ByteRange) location =>
    GeneralBorrowFreshMaterialization.materialized location child GeneralBorrowFreshDefaultChild.inside
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
    (fun _ location => GeneralBorrowFreshInstallation.materialized_idempotent location child GeneralBorrowFreshDefaultChild.inside)
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
      (GeneralBorrowFreshDefaultChild.child newTag parent) mapping locations))
    (exposure : GeneralBorrowFreshMetadataChildSifa.exposureShape after =
      GeneralBorrowFreshMetadataChildSifa.exposureShape (GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode
        (GeneralBorrowFreshDefaultChild.child newTag parent) mapping locations)) :
    ∃ next, after.nodes.get target = some next ∧ next.tag = targetNode.tag ∧ next.parent = targetNode.parent ∧
      next.children = targetNode.children ∧ next.isExposed = targetNode.isExposed := by
  let stage := GeneralBorrowFreshMetadataChildAttach.staged tree child parent parentNode
    (GeneralBorrowFreshDefaultChild.child newTag parent) mapping locations
  have notChild : target ≠ child := by intro same; rw [same,vacant] at targetAt; cases targetAt
  have atStage : stage.nodes.get target = some targetNode := by
    dsimp only [stage,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,GeneralBorrowFreshNode.attachedNodes]
    rw [GeneralBorrowFreshLocation.get_other _ _ _ _ different,GeneralBorrowFreshLocation.get_other _ _ _ _ notChild]
    exact targetAt
  obtain ⟨next,found,tag,parentEq,children,_⟩ := GeneralBorrowFreshMetadata.node_fields stage after shape target targetNode atStage
  have flags := GeneralBorrowFreshMetadataChildSifa.lookup_exposure stage after exposure target
  rw [found,atStage] at flags
  exact ⟨next,found,tag,parentEq,children,by simpa only [Option.map_some,Option.some.injEq] using flags⟩

theorem old_facets (tree : BorrowTree) (global : GlobalState)
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
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false
    (∃ next, actual.tree.nodes.get target = some next ∧ next.tag = targetNode.tag ∧ next.parent = targetNode.parent ∧
      next.children = targetNode.children ∧ next.isExposed = targetNode.isExposed) ∧
    GeneralBorrowFreshActiveWithin.ActiveWithin actual.tree target kind lower upper := by
  let rank := GeneralBorrowStructuralHistoryDefault.depth tree runtime.formed.toState
  have slot := GeneralBorrowStructuralHistoryDefault.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildDefault.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        noFree,aligned,fits,offset,len,nonzero,runtime.formed.well,bounds⟩
    let child := GeneralBorrowFreshMetadataChildDefault.index input
    have vacant : tree.nodes.get child = none := by
      have atEnd : child.toNat = tree.nodes.data.size := GeneralBorrowFreshMetadataChildDefault.at_end input
      simp only [UniValMap.get,atEnd,Array.getElem?_eq_none (Nat.le_refl _)]
    have notChild : target ≠ child := by intro same; rw [same,vacant] at targetAt; cases targetAt
    have staged : GeneralBorrowFreshActiveWithin.ActiveWithin (GeneralBorrowFreshMetadataChildDefault.stage input) target kind lower upper :=
      materialized_active tree child target notChild (Size.ofBytes offset) (Size.ofBytes len) kind lower upper runtime.formed.well bounds active
    exact ⟨old_node tree _ child parent target parentNode targetNode newTag _ _ vacant targetAt different
      (GeneralBorrowFreshMetadataChildDefault.shape input) (GeneralBorrowFreshMetadataChildDefault.exposure input),
      GeneralBorrowFreshActiveWithin.shape_preserves _ _ (GeneralBorrowFreshMetadataChildDefault.shape input) target kind lower upper staged⟩
  | reuse child available bounded vacant slack =>
    let input : GeneralBorrowFreshMetadataChildDefaultReuse.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        child,available,bounded,vacant,slack,offset,len,nonzero,runtime.formed.well,bounds⟩
    have notChild : target ≠ child := by intro same; rw [same,vacant] at targetAt; cases targetAt
    have staged : GeneralBorrowFreshActiveWithin.ActiveWithin (GeneralBorrowFreshMetadataChildDefaultReuse.stage input) target kind lower upper :=
      materialized_active tree child target notChild (Size.ofBytes offset) (Size.ofBytes len) kind lower upper runtime.formed.well bounds active
    exact ⟨old_node tree _ child parent target parentNode targetNode newTag _ _ vacant targetAt different
      (GeneralBorrowFreshMetadataChildDefaultReuse.shape input) (GeneralBorrowFreshMetadataChildDefaultReuse.exposure input),
      GeneralBorrowFreshActiveWithin.shape_preserves _ _ (GeneralBorrowFreshMetadataChildDefaultReuse.shape input) target kind lower upper staged⟩


end
end DuplicatePrefix.CurrentCallDefaultMutableDisjoint
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallDefaultMutableDisjoint" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved Default mutable disjoint dependency {dependency}"
