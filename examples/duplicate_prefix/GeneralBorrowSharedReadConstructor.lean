import duplicate_prefix.GeneralBorrowSharedCapabilityConstructor
import duplicate_prefix.GeneralBorrowReadRowRange
namespace DuplicatePrefix.GeneralBorrowSharedReadConstructor
open Miri Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowFreshAnchor GeneralBorrowFreshMaterialization
open GeneralBorrowFreshNormalComponent GeneralBorrowSharedNormalRelations GeneralBorrowSharedNormalTables
open GeneralRangeMapOrigins GeneralBorrowFreshInstallation
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Raw shared materialization data; the fresh protector is unconstrained. -/
structure Extension (before after : NormalTreeState) (parent child : Nat) : Prop where
  patch : Patch before.topology after.topology parent child
  paths : GeneralBorrowFreshSharedPaths.Attach before.topology after.topology parent child
  oldValid : ∀ index, index < after.topology.nodes.size → index ≠ child → index < before.topology.nodes.size
  oldState : ∀ index, index < before.topology.nodes.size → index ≠ child → after.stateAt index = before.stateAt index
  newState : after.stateAt child = some sharedState
  oldProtected : ∀ index, index < before.topology.nodes.size → index ≠ child → after.protectedNodes.contains index = before.protectedNodes.contains index

private theorem topology_size (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) :
    (source_normal_projection tree location protections).topology.nodes.size = tree.nodes.data.size := by
  unfold_general_projection
  unfold_general_topology
  simp only [Array.size_map]

theorem append_extension (tree : BorrowTree) (index parent : UniIndex) (parentNode : TreeNode) (tag : BorTag)
    (atEnd : index.toNat = tree.nodes.data.size) (present : tree.nodeAt parent = some parentNode)
    (location : LocationTree) (protections : ProtectedTags)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology) :
    Extension (source_normal_projection tree location protections)
      (source_normal_projection (GeneralBorrowFreshGraph.attached tree index parent parentNode (sharedNode tag parent))
        (materialized location index sharedState) protections) parent.toNat index.toNat := by
  let afterLocation := materialized location index sharedState
  have extension := GeneralBorrowFreshProjection.topology_extension tree index parent parentNode (sharedNode tag parent)
    atEnd present rfl rfl location afterLocation protections
  have size := topology_size tree location protections
  have indexEq : index.toNat = (source_normal_projection tree location protections).topology.nodes.size := atEnd.trans size.symm
  have patch := GeneralBorrowFreshNormalComponent.of_append _ _ parent.toNat extension
  have paths := GeneralBorrowFreshSharedPaths.of_append _ _ parent.toNat extension forest
  rw [←indexEq] at patch paths
  refine ⟨patch,paths,?_,?_,?_,?_⟩
  · intro query valid different
    rw [extension.length] at valid
    rw [indexEq] at different
    omega
  · intro query valid different
    exact GeneralBorrowFreshMaterialization.state_old tree index parent parentNode (sharedNode tag parent) atEnd present location sharedState protections query (by rw [←size];exact valid)
  · exact GeneralBorrowFreshMaterialization.state_new tree index parent parentNode (sharedNode tag parent) atEnd present location sharedState protections
  · intro query valid different
    exact GeneralBorrowFreshMaterialization.protection_old tree index parent parentNode (sharedNode tag parent) atEnd present location afterLocation protections query (by rw [←size];exact valid)

theorem reuse_extension (tree : BorrowTree) (index parent : UniIndex) (parentNode : TreeNode) (tag : BorTag)
    (bounded : index.toNat < tree.nodes.data.size) (vacant : tree.nodes.get index = none)
    (fits : tree.nodes.data.size ≤ 4294967296) (present : tree.nodeAt parent = some parentNode)
    (location : LocationTree) (protections : ProtectedTags)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology) :
    Extension (source_normal_projection tree location protections)
      (source_normal_projection (GeneralBorrowFreshGraph.attached tree index parent parentNode (sharedNode tag parent))
        (materialized location index sharedState) protections) parent.toNat index.toNat := by
  let afterLocation := materialized location index sharedState
  have extension := GeneralBorrowFreshReuseProjection.topology_extension tree index parent parentNode (sharedNode tag parent)
    bounded vacant present rfl rfl location afterLocation protections
  have size := topology_size tree location protections
  refine ⟨GeneralBorrowFreshNormalComponent.of_reuse _ _ index.toNat parent.toNat extension,
    GeneralBorrowFreshSharedPaths.of_reuse _ _ index.toNat parent.toNat extension forest,?_,?_,?_,?_⟩
  · intro query valid different
    rw [extension.length] at valid
    exact valid
  · intro query valid different
    exact GeneralBorrowFreshReuseState.state_old tree index parent parentNode (sharedNode tag parent) bounded vacant present fits location sharedState protections query (by rw [←size];exact valid) different
  · exact GeneralBorrowFreshReuseState.state_new tree index parent parentNode (sharedNode tag parent) bounded vacant present location sharedState protections
  · intro query valid different
    exact GeneralBorrowFreshReuseProtection.protection_position tree index parent parentNode (sharedNode tag parent) vacant present location afterLocation protections fits query (by rw [←size];exact valid) different

/-- Read tables extend to BOTH the old and new source even for a held fresh
Frozen tag. No Write table is asserted. -/
theorem certificates (before after : NormalTreeState) (parent child : Nat)
    (old : GeneralBorrowExposedScopedNormal.Component before.topology parent)
    (extension : Extension before after parent child)
    (permissions : Table before parent .Read old.support) :
    ∃ original : GeneralBorrowExposedScopedNormal.Component after.topology parent,
      ∃ shared : GeneralBorrowExposedScopedNormal.Component after.topology child,
        Table after parent .Read original.support ∧ Table after child .Read shared.support := by
  let original := component before.topology after.topology parent child old extension.patch parent (.inl rfl)
  let shared := component before.topology after.topology parent child old extension.patch child (.inr rfl)
  refine ⟨original,shared,?_,?_⟩
  · intro index included valid
    by_cases fresh : index = child
    · subst index
      refine ⟨sharedState,extension.newState,?_⟩
      rw [original_child_foreign before after parent child parent extension.paths extension.paths.parentValid extension.paths.parentDifferent]
      cases after.protectedNodes.contains child <;>
        simp [sharedState,DuplicatePrefixScalarAuthorization.Compatible,GeneralBorrowProtectedReadCompatible.Compatible,
          LocationState.possible,Permission.isUnique]
    · have oldValid := extension.oldValid index valid fresh
      obtain ⟨state,present,compatible⟩ := permissions index (included.resolve_left fresh) oldValid
      refine ⟨state,(extension.oldState index oldValid fresh).trans present,?_⟩
      rw [GeneralBorrowSharedNormalRelations.original before after parent child parent index extension.paths
        extension.paths.parentValid extension.paths.parentDifferent,extension.oldProtected index oldValid fresh]
      exact compatible
  · intro index included valid
    by_cases fresh : index = child
    · subst index
      refine ⟨sharedState,extension.newState,?_⟩
      rw [child_self]
      exact DuplicatePrefixConstructorNormalShape.shared_local_read _
    · have oldValid := extension.oldValid index valid fresh
      obtain ⟨state,present,compatible⟩ := permissions index (included.resolve_left fresh) oldValid
      refine ⟨state,(extension.oldState index oldValid fresh).trans present,?_⟩
      rw [child_old before after parent child index extension.paths fresh,extension.oldProtected index oldValid fresh]
      exact compatible

def Capabilities (tree : BorrowTree) (protections : ProtectedTags) (parent child : UniIndex) (location : LocationTree) : Prop :=
  Nonempty (DuplicatePrefixNormalKind.Capability tree location protections parent .Read) ∧
  Nonempty (DuplicatePrefixNormalKind.Capability tree location protections child .Read)

def Parent (tree : BorrowTree) (protections : ProtectedTags) (parent : UniIndex) (location : LocationTree) : Prop :=
  Nonempty (GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology) ∧
  Nonempty (DuplicatePrefixNormalKind.Capability tree location protections parent .Read)

theorem from_extension (before after : BorrowTree) (oldLocation newLocation : LocationTree) (protections : ProtectedTags)
    (parent child : UniIndex) (normal : DuplicatePrefixNormalKind.Capability before oldLocation protections parent .Read)
    (extension : Extension (source_normal_projection before oldLocation protections)
      (source_normal_projection after newLocation protections) parent.toNat child.toNat) :
    Capabilities after protections parent child newLocation := by
  have table : Table (source_normal_projection before oldLocation protections) parent.toNat .Read normal.component.support := by
    intro index included valid
    exact normal.permissions index included (by rw [←topology_size before oldLocation protections];exact valid)
  obtain ⟨original,shared,parentRead,childRead⟩ := certificates (source_normal_projection before oldLocation protections)
    (source_normal_projection after newLocation protections) parent.toNat child.toNat normal.component extension table
  refine ⟨⟨⟨original,?_⟩⟩,⟨⟨shared,?_⟩⟩⟩
  · intro index included valid
    exact parentRead index included (by rw [topology_size after newLocation protections];exact valid)
  · intro index included valid
    exact childRead index included (by rw [topology_size after newLocation protections];exact valid)

theorem context (tree : BorrowTree) (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree)
    (protections : ProtectedTags) (parent child : UniIndex) (location : LocationTree) :
    Capabilities {tree with tagMapping := mapping,locations := locations} protections parent child location =
      Capabilities tree protections parent child location := by
  apply propext
  constructor
  all_goals
    rintro ⟨⟨parentRead⟩,⟨childRead⟩⟩
    exact ⟨⟨⟨parentRead.component,parentRead.permissions⟩⟩,⟨⟨childRead.component,childRead.permissions⟩⟩⟩

/-- Predicate-parametric materialization, using the exact source modifyRange
map rather than a new specialized iterator proof. -/
theorem materialize_owned (locations : DedupRangeMap LocationTree) (offset len : Size)
    (index : UniIndex) (state : LocationState) (before after : LocationTree → Prop)
    (well : locations.WellFormed) (bounds : offset.bytes.toNat + len.bytes.toNat ≤ locations.size.bytes.toNat)
    (owned : OwnedOn before offset.bytes (offset.bytes+len.bytes) locations)
    (step : ∀ location, before location → after (materialized location index state)) :
    OwnedOn after offset.bytes (offset.bytes+len.bytes)
      (locations.modifyRange offset len (fun _ location => materialized location index state)).state := by
  let prepared := locations.iterMut offset len
  let modify : ByteRange → LocationTree → LocationTree := fun _ location => materialized location index state
  let changed := locations.modifyRange offset len modify
  have owners := GeneralRangeMapOriginPrepare.selected_owned_on locations offset len well bounds
    before offset.bytes (offset.bytes+len.bytes) owned (Nat.le_refl _) (Nat.le_refl _)
  have sizes : changed.state.entries.size = prepared.state.entries.size := by
    dsimp only [changed,prepared]
    rw [GeneralBorrowFreshModify.state_exact locations offset len modify well bounds,GeneralBorrowFreshModify.fold_size]
  intro position valid positive start stop
  have oldValid : position < prepared.state.entries.size := by rw [←sizes];exact valid
  obtain ⟨outputValid,entryEq⟩ := GeneralBorrowFreshModify.entry_exact locations offset len modify
    (fun _ location => materialized_idempotent location index state) well bounds position oldValid
  have rangeEq : (changed.state.entries[position]'valid).range = (prepared.state.entries[position]'oldValid).range := by
    have known := congrArg RangeMapSegment.range entryEq
    by_cases member : position ∈ (locations.iterMut offset len).positions.toList <;> simpa only [member,↓reduceIte] using known
  rw [rangeEq] at start stop
  have beforeRow := owners.2.1 position oldValid positive start stop
  obtain ⟨cursor,bounded,same⟩ := GeneralRangeMapCoverage.overlap_selected locations offset len well bounds
    positive position oldValid start stop
  have member : position ∈ (locations.iterMut offset len).positions.toList := by
    rw [←same]
    exact Array.mem_toList_iff.mpr (Array.getElem_mem bounded)
  simp only [member,↓reduceIte] at entryEq
  have dataEq := congrArg RangeMapSegment.data entryEq
  change after (changed.state.entries[position]'valid).data
  rw [dataEq]
  exact step _ beforeRow


theorem append_ranged_owned (tree : BorrowTree) (index parent : UniIndex) (parentNode : TreeNode) (tag : BorTag)
    (atEnd : index.toNat = tree.nodes.data.size) (present : tree.nodeAt parent = some parentNode)
    (protections : ProtectedTags) (offset len : Size) (well : tree.locations.WellFormed)
    (bounds : offset.bytes.toNat+len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (owned : OwnedOn (Parent tree protections parent) offset.bytes (offset.bytes+len.bytes) tree.locations) :
    let changed := tree.locations.modifyRange offset len (fun _ location => materialized location index sharedState)
    let installed := {(GeneralBorrowFreshGraph.attached tree index parent parentNode (sharedNode tag parent)) with locations := changed.state}
    OwnedOn (Capabilities installed protections parent index) offset.bytes (offset.bytes+len.bytes) changed.state := by
  dsimp only
  have installed := materialize_owned tree.locations offset len index sharedState (Parent tree protections parent)
    (Capabilities (GeneralBorrowFreshGraph.attached tree index parent parentNode (sharedNode tag parent)) protections parent index)
    well bounds owned (by
      intro location initial
      obtain ⟨⟨forest⟩,⟨normal⟩⟩ := initial
      exact from_extension tree _ location _ protections parent index normal
        (append_extension tree index parent parentNode tag atEnd present location protections forest))
  intro position valid positive start stop
  rw [context]
  exact installed position valid positive start stop

theorem reuse_ranged_owned (tree : BorrowTree) (index parent : UniIndex) (parentNode : TreeNode) (tag : BorTag)
    (bounded : index.toNat < tree.nodes.data.size) (vacant : tree.nodes.get index = none)
    (fits : tree.nodes.data.size ≤ 4294967296) (present : tree.nodeAt parent = some parentNode)
    (protections : ProtectedTags) (offset len : Size) (well : tree.locations.WellFormed)
    (bounds : offset.bytes.toNat+len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (owned : OwnedOn (Parent tree protections parent) offset.bytes (offset.bytes+len.bytes) tree.locations) :
    let changed := tree.locations.modifyRange offset len (fun _ location => materialized location index sharedState)
    let installed := {(GeneralBorrowFreshGraph.attached tree index parent parentNode (sharedNode tag parent)) with locations := changed.state}
    OwnedOn (Capabilities installed protections parent index) offset.bytes (offset.bytes+len.bytes) changed.state := by
  dsimp only
  have installed := materialize_owned tree.locations offset len index sharedState (Parent tree protections parent)
    (Capabilities (GeneralBorrowFreshGraph.attached tree index parent parentNode (sharedNode tag parent)) protections parent index)
    well bounds owned (by
      intro location initial
      obtain ⟨⟨forest⟩,⟨normal⟩⟩ := initial
      exact from_extension tree _ location _ protections parent index normal
        (reuse_extension tree index parent parentNode tag bounded vacant fits present location protections forest))
  intro position valid positive start stop
  rw [context]
  exact installed position valid positive start stop

open GeneralBorrowView GeneralBorrowFreshOwnership GeneralBorrowNodeUpdate in
theorem shape_preserves (before after : BorrowTree) (same : treeShape after = treeShape before)
    (protections : ProtectedTags) (parent child : UniIndex) (lower upper : UInt64)
    (owned : OwnedOn (Capabilities before protections parent child) lower upper before.locations) :
    OwnedOn (Capabilities after protections parent child) lower upper after.locations := by
  have nodes : after.nodes.data.map (Option.map nodeShape) = before.nodes.data.map (Option.map nodeShape) :=
    congrArg (fun row => row.2.1) same
  have ranges : after.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) =
      before.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) :=
    congrArg (fun row => row.2.2.1) same
  have sizes : after.locations.entries.size = before.locations.entries.size := by
    have known := congrArg Array.size ranges
    simpa only [Array.size_map] using known
  intro position valid positive beforeUpper afterLower
  have oldValid : position < before.locations.entries.size := by rw [←sizes];exact valid
  have entriesSame : (after.locations.entries[position]'valid).range =
        (before.locations.entries[position]'oldValid).range ∧
      locationShape (after.locations.entries[position]'valid).data =
        locationShape (before.locations.entries[position]'oldValid).data := by
    have known := congrArg (fun rows => rows[position]?) ranges
    simp only [Array.getElem?_map,Array.getElem?_eq_getElem valid,
      Array.getElem?_eq_getElem oldValid,Option.map_some] at known
    exact Prod.mk.inj (Option.some.inj known)
  rw [entriesSame.1] at beforeUpper afterLower
  obtain ⟨⟨normal⟩,⟨read⟩⟩ := owned position oldValid positive beforeUpper afterLower
  have profiles := GeneralBorrowFreshOwnership.projection_shape before after
    (before.locations.entries[position]'oldValid).data
    (after.locations.entries[position]'valid).data protections nodes entriesSame.2
  exact ⟨GeneralBorrowNormalCapabilityShape.capability before after _ _ protections parent .Read profiles normal,
    GeneralBorrowNormalCapabilityShape.capability before after _ _ protections child .Read profiles read⟩

namespace Append
open GeneralBorrowFreshMetadataChildShared
/-- Real append plus ancestor SIFA weakening preserves parent Capabilities and creates child Read. -/
theorem capabilities (input : Input) (protections : ProtectedTags)
    (before : OwnedOn (Parent input.tree protections input.parent)
      input.offset (input.offset+input.len) input.tree.locations) :
    OwnedOn (Capabilities (result input) protections input.parent (index input))
      input.offset (input.offset+input.len) (result input).locations := by
  have installed := append_ranged_owned input.tree (index input) input.parent input.parentNode input.newTag
    (at_end input) input.parentPresent protections (Size.ofBytes input.offset) (Size.ofBytes input.len)
    input.well input.bounds before
  have staged : OwnedOn (Capabilities (stage input) protections input.parent (index input))
      input.offset (input.offset+input.len) (stage input).locations := by
    intro position valid positive start stop
    have row := installed position valid positive start stop
    dsimp only [stage,GeneralBorrowFreshMetadataChildAttach.staged] at *
    rw [context] at row ⊢
    exact row
  exact shape_preserves (stage input) (result input) (shape input)
    protections input.parent (index input) input.offset (input.offset+input.len) staged
end Append

namespace Reuse
open GeneralBorrowFreshMetadataChildSharedReuse
/-- Vacant-slot reuse plus actual ancestor SIFA weakening yields the same capabilities. -/
theorem capabilities (input : Input) (protections : ProtectedTags)
    (fits : input.tree.nodes.data.size ≤ 4294967296)
    (before : OwnedOn (Parent input.tree protections input.parent)
      input.offset (input.offset+input.len) input.tree.locations) :
    OwnedOn (Capabilities (result input) protections input.parent input.index)
      input.offset (input.offset+input.len) (result input).locations := by
  have installed := reuse_ranged_owned input.tree input.index input.parent input.parentNode input.newTag
    input.valid input.vacant fits input.parentPresent protections (Size.ofBytes input.offset) (Size.ofBytes input.len)
    input.well input.bounds before
  have staged : OwnedOn (Capabilities (stage input) protections input.parent input.index)
      input.offset (input.offset+input.len) (stage input).locations := by
    intro position valid positive start stop
    have row := installed position valid positive start stop
    dsimp only [stage,GeneralBorrowFreshMetadataChildAttach.staged] at *
    rw [context] at row ⊢
    exact row
  exact shape_preserves (stage input) (result input) (shape input)
    protections input.parent input.index input.offset (input.offset+input.len) staged
end Reuse

/-- Actual shared constructor from a Read-only parent, retaining parent Read
and fresh-child Read for either fresh protector state and arbitrary runtime pool. -/
theorem construct (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (tagBound : newTag.value.toNat < global.nextPointerTag.value.toNat)
    (held : Bool) (aligned : global.protectedTags.contains newTag = held)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (before : OwnedOn (fun location => Nonempty (DuplicatePrefixNormalKind.Capability tree location global.protectedTags parent .Read))
      offset (offset+len) tree.locations) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen held
    actual.outcome = .ok () ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global ∧
    actual.tree.locations.size = tree.locations.size ∧ actual.tree.nodes.size ≤ tree.nodes.size+1 ∧
    ∃ child, actual.tree.indexOfTag newTag = some child ∧
      OwnedOn (Capabilities actual.tree global.protectedTags parent child) offset (offset+len) actual.tree.locations := by
  have initial : OwnedOn (Parent tree global.protectedTags parent) offset (offset+len) tree.locations := by
    intro position valid positive start stop
    exact ⟨runtime.formed.toState.forest _ _,before position valid positive start stop⟩
  have output := GeneralBorrowSharedConstructorRuntime.construct tree global runtime parentTag newTag parent parentNode
    tagged present fresh room tagBound held aligned offset len nonzero bounds
  refine ⟨output.1,output.2.1,output.2.2.1,output.2.2.2,?_⟩
  let rank := GeneralBorrowStructuralHistoryShared.depth tree runtime.formed.toState
  have slot := GeneralBorrowStructuralHistoryShared.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree accounting fits =>
    let input : GeneralBorrowFreshMetadataChildShared.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        noFree,accounting,fits,held,offset,len,nonzero,runtime.formed.well,bounds⟩
    exact ⟨GeneralBorrowFreshMetadataChildShared.index input,
      (GeneralBorrowFreshMetadataChildShared.append input).freshLookup,Append.capabilities input global.protectedTags initial⟩
  | reuse index available valid vacant slack =>
    let input : GeneralBorrowFreshMetadataChildSharedReuse.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        index,available,valid,vacant,slack,held,offset,len,nonzero,runtime.formed.well,bounds⟩
    have fits : tree.nodes.data.size ≤ 4294967296 := by change tree.nodes.data.size+1 ≤ _ at room;omega
    exact ⟨index,(GeneralBorrowFreshMetadataChildSharedReuse.reuse input).freshLookup,
      Reuse.capabilities input global.protectedTags fits initial⟩

end DuplicatePrefix.GeneralBorrowSharedReadConstructor
