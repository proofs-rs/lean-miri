import duplicate_prefix.GeneralBorrowDefaultMaterializedNormal
import duplicate_prefix.GeneralBorrowNormalCapabilityShape
import duplicate_prefix.GeneralBorrowProtectedConstructorRuntime
import duplicate_prefix.GeneralBorrowFreshInstallation

namespace DuplicatePrefix.CurrentCallEmptyEntryBoolChildNormal
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowView GeneralBorrowFreshOwnership GeneralRangeMapOrigins
open GeneralBorrowFreshNormalComponent GeneralBorrowSharedNormalRelations
open GeneralBorrowDefaultNormalTables (Table)
open GeneralBorrowFreshChild (child inside)
open GeneralBorrowFreshMaterialization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 200000
structure Extension (before after : NormalTreeState) (parent child : Nat) : Prop where
  patch : Patch before.topology after.topology parent child
  paths : GeneralBorrowFreshSharedPaths.Attach before.topology after.topology parent child
  oldValid : ∀ index, index < after.topology.nodes.size → index ≠ child → index < before.topology.nodes.size
  oldState : ∀ index, index < before.topology.nodes.size → index ≠ child → after.stateAt index = before.stateAt index
  newState : after.stateAt child = some GeneralBorrowFreshChild.inside
  oldProtected : ∀ index, index < before.topology.nodes.size → index ≠ child → after.protectedNodes.contains index = before.protectedNodes.contains index

/-- Exact per-kind table extension to the unprotected mutable reservation. -/
private theorem child_table (before after : NormalTreeState) (parent child : Nat) (kind : AccessKind)
    (old : GeneralBorrowExposedScopedNormal.Component before.topology parent)
    (extension : Extension before after parent child)
    (permissions : Table before parent kind old.support) :
    Table after child kind (extended old.support child) := by
  intro index included valid
  by_cases fresh : index = child
  · subst index
    refine ⟨GeneralBorrowFreshChild.inside,extension.newState,?_⟩
    rw [child_self]
    cases kind <;> cases after.protectedNodes.contains child <;>
      simp [DuplicatePrefixScalarAuthorization.Compatible,GeneralBorrowProtectedReadCompatible.Compatible,
        GeneralBorrowExposedConditionalWritePermissions.Compatible,GeneralBorrowFreshChild.inside,LocationState.possible,Permission.isUnique]
  · have oldValid := extension.oldValid index valid fresh
    obtain ⟨state,present,compatible⟩ := permissions index (included.resolve_left fresh) oldValid
    refine ⟨state,(extension.oldState index oldValid fresh).trans present,?_⟩
    rw [child_old before after parent child index extension.paths fresh,extension.oldProtected index oldValid fresh]
    exact compatible

private theorem topology_size (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) :
    (source_normal_projection tree location protections).topology.nodes.size = tree.nodes.data.size := by
  unfold_general_projection
  unfold_general_topology
  simp only [Array.size_map]

/-- Real append attachment and inside mutable materialization form exact scalar
state/protector/path extension data, with arbitrary old permission states. -/
private theorem append_extension (tree : BorrowTree) (index parent : UniIndex) (parentNode : TreeNode) (tag : BorTag)
    (atEnd : index.toNat = tree.nodes.data.size) (present : tree.nodeAt parent = some parentNode)
    (location : LocationTree) (protections : ProtectedTags)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology) :
    Extension (source_normal_projection tree location protections)
      (source_normal_projection (GeneralBorrowFreshGraph.attached tree index parent parentNode (child tag parent))
        (materialized location index inside) protections) parent.toNat index.toNat := by
  let afterLocation := materialized location index inside
  have extension := GeneralBorrowFreshProjection.topology_extension tree index parent parentNode (child tag parent)
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
    exact GeneralBorrowFreshMaterialization.state_old tree index parent parentNode (child tag parent) atEnd present location inside protections query (by rw [←size];exact valid)
  · exact GeneralBorrowFreshMaterialization.state_new tree index parent parentNode (child tag parent) atEnd present location inside protections
  · intro query valid different
    exact GeneralBorrowFreshMaterialization.protection_old tree index parent parentNode (child tag parent) atEnd present location afterLocation protections query (by rw [←size];exact valid)
/-- The same exact table extension for a genuinely vacant reusable slot; old
optional permission slots need not be Clean inside the overwritten row. -/
private theorem reuse_extension (tree : BorrowTree) (index parent : UniIndex) (parentNode : TreeNode) (tag : BorTag)
    (bounded : index.toNat < tree.nodes.data.size) (vacant : tree.nodes.get index = none)
    (fits : tree.nodes.data.size ≤ 4294967296) (present : tree.nodeAt parent = some parentNode)
    (location : LocationTree) (protections : ProtectedTags)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology) :
    Extension (source_normal_projection tree location protections)
      (source_normal_projection (GeneralBorrowFreshGraph.attached tree index parent parentNode (child tag parent))
        (materialized location index inside) protections) parent.toNat index.toNat := by
  let afterLocation := materialized location index inside
  have extension := GeneralBorrowFreshReuseProjection.topology_extension tree index parent parentNode (child tag parent)
    bounded vacant present rfl rfl location afterLocation protections
  have size := topology_size tree location protections
  refine ⟨GeneralBorrowFreshNormalComponent.of_reuse _ _ index.toNat parent.toNat extension,
    GeneralBorrowFreshSharedPaths.of_reuse _ _ index.toNat parent.toNat extension forest,?_,?_,?_,?_⟩
  · intro query valid different
    rw [extension.length] at valid
    exact valid
  · intro query valid different
    exact GeneralBorrowFreshReuseState.state_old tree index parent parentNode (child tag parent) bounded vacant present fits location inside protections query (by rw [←size];exact valid) different
  · exact GeneralBorrowFreshReuseState.state_new tree index parent parentNode (child tag parent) bounded vacant present location inside protections
  · intro query valid different
    exact GeneralBorrowFreshReuseProtection.protection_position tree index parent parentNode (child tag parent) vacant present location afterLocation protections fits query (by rw [←size];exact valid) different

private theorem projection_context (tree : BorrowTree) (mapping : UniKeyMap BorTag)
    (locations : DedupRangeMap LocationTree) (row : LocationTree) (held : ProtectedTags) :
    source_normal_projection {tree with tagMapping := mapping,locations := locations} row held =
      source_normal_projection tree row held := rfl

private theorem materialized_normal (tree : BorrowTree) (after : BorrowTree) (location : LocationTree)
    (held : ProtectedTags) (parent index : UniIndex)
    (extension : Extension (source_normal_projection tree location held)
      (source_normal_projection after (materialized location index inside) held) parent.toNat index.toNat)
    (old : DuplicatePrefixBorrowAuthorization.Normal tree location held parent) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Normal after (materialized location index inside) held index) := by
  let next := GeneralBorrowFreshNormalComponent.component _ _ parent.toNat index.toNat old.component extension.patch index.toNat (.inr rfl)
  refine ⟨⟨next,?_⟩⟩
  intro kind query included valid
  exact child_table (source_normal_projection tree location held)
    (source_normal_projection after (materialized location index inside) held) parent.toNat index.toNat kind old.component extension
    (fun q supported bound => old.permissions kind q supported (by rw [topology_size] at bound;exact bound))
    query included (by rw [topology_size];exact valid)

private theorem shape_normal (before after : BorrowTree) (first second : LocationTree) (held : ProtectedTags)
    (index : UniIndex) (nodes : treeShape after = treeShape before)
    (locations : locationShape second = locationShape first)
    (old : DuplicatePrefixBorrowAuthorization.Normal before first held index) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Normal after second held index) := by
  have nodeEq : after.nodes.data.map (Option.map nodeShape) = before.nodes.data.map (Option.map nodeShape) :=
    congrArg (fun shape => shape.2.1) nodes
  exact GeneralBorrowNormalCapabilityShape.normal before after first second held index
    (GeneralBorrowFreshOwnership.projection_shape before after first second held nodeEq locations) old

private theorem modify_owned (map : DedupRangeMap LocationTree) (offset len : Size)
    (well : map.WellFormed) (bounds : offset.bytes.toNat+len.bytes.toNat ≤ map.size.bytes.toNat)
    (modify : LocationTree → LocationTree) (idempotent : ∀ location, modify (modify location) = modify location)
    (P Q : LocationTree → Prop) (step : ∀ location, P location → Q (modify location))
    (owned : OwnedOn P offset.bytes (offset.bytes+len.bytes) map) :
    OwnedOn Q offset.bytes (offset.bytes+len.bytes)
      (map.modifyRange offset len (fun _ location => modify location)).state := by
  let prepared := map.iterMut offset len
  let changed := map.modifyRange offset len (fun _ location => modify location)
  have preparedGood := GeneralRangeMapOriginPrepare.iter_mut map offset len well bounds
  have preparedOwned := GeneralRangeMapOriginPrepare.selected_owned_on map offset len well bounds P
    offset.bytes (offset.bytes+len.bytes) owned (Nat.le_refl _) (Nat.le_refl _)
  have sizes : changed.state.entries.size = prepared.state.entries.size := by
    dsimp only [changed,prepared]
    rw [GeneralBorrowFreshModify.state_exact map offset len _ well bounds,GeneralBorrowFreshModify.fold_size]
  intro position valid positive start stop
  have oldValid : position < prepared.state.entries.size := by
    change position < changed.state.entries.size at valid
    omega
  obtain ⟨outputValid,entryEq⟩ := GeneralBorrowFreshModify.entry_exact map offset len (fun _ location => modify location)
    (fun _ location => idempotent location) well bounds position oldValid
  have rangeEq : (changed.state.entries[position]'valid).range = (prepared.state.entries[position]'oldValid).range := by
    have known := congrArg RangeMapSegment.range entryEq
    split at known <;> exact known
  rw [rangeEq] at start stop
  obtain ⟨cursor,bounded,same⟩ := GeneralRangeMapCoverage.overlap_selected map offset len well bounds positive position oldValid start stop
  have member : position ∈ prepared.positions.toList := by
    rw [←same]
    exact Array.mem_def.mp (Array.mem_iff_getElem.mpr ⟨cursor,bounded,rfl⟩)
  simp only [show position ∈ (map.iterMut offset len).positions.toList from member,↓reduceIte] at entryEq
  rw [entryEq]
  apply step
  have segmentValid : cursor < prepared.segments.size := by rw [←preparedGood.1.lengths];exact bounded
  have selected := preparedOwned.2.2 cursor segmentValid
  have selectedEq := preparedGood.1.selected cursor bounded
  rw [selectedEq.2] at selected
  simpa only [same] using selected

private theorem shape_owned (before after : BorrowTree) (held : ProtectedTags) (index : UniIndex) (lower upper : UInt64)
    (same : treeShape after = treeShape before)
    (owned : OwnedOn (fun row => Nonempty (DuplicatePrefixBorrowAuthorization.Normal before row held index)) lower upper before.locations) :
    OwnedOn (fun row => Nonempty (DuplicatePrefixBorrowAuthorization.Normal after row held index)) lower upper after.locations := by
  have entries := congrArg (fun shape => shape.2.2.1) same
  have sizes : after.locations.entries.size = before.locations.entries.size := by
    simpa only [treeShape,Array.size_map] using congrArg Array.size entries
  intro position valid positive lowerBound upperBound
  have oldValid : position < before.locations.entries.size := by omega
  have cell := congrArg (fun rows => rows[position]?) entries
  simp only [treeShape,Array.getElem?_map,Array.getElem?_eq_getElem valid,
    Array.getElem?_eq_getElem oldValid,Option.map_some,Option.some.injEq,Prod.mk.injEq] at cell
  obtain ⟨old⟩ := owned position oldValid positive (by simpa only [←cell.1] using lowerBound)
    (by simpa only [←cell.1] using upperBound)
  exact shape_normal before after _ _ held index same cell.2 old

private theorem stage_owned (tree stage : BorrowTree) (held : ProtectedTags) (parent index : UniIndex)
    (offset len : UInt64) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (locations : stage.locations = (tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len)
      (fun _ row => materialized row index inside)).state)
    (extension : ∀ row, Extension (source_normal_projection tree row held)
      (source_normal_projection stage (materialized row index inside) held) parent.toNat index.toNat)
    (owned : OwnedOn (fun row => Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree row held parent))
      offset (offset+len) tree.locations) :
    OwnedOn (fun row => Nonempty (DuplicatePrefixBorrowAuthorization.Normal stage row held index))
      offset (offset+len) stage.locations := by
  rw [locations]
  refine modify_owned tree.locations (Size.ofBytes offset) (Size.ofBytes len) well bounds
    (fun row => materialized row index inside) (fun row => GeneralBorrowFreshInstallation.materialized_idempotent row index inside)
    (fun row => Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree row held parent))
    (fun row => Nonempty (DuplicatePrefixBorrowAuthorization.Normal stage row held index)) ?_ owned
  intro row normal
  obtain ⟨normal⟩ := normal
  exact materialized_normal tree stage row held parent index (extension row) normal
theorem construct (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (tagBound : newTag.value.toNat < global.nextPointerTag.value.toNat)
    (held : global.protectedTags.contains newTag = true)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (owned : OwnedOn (fun row => Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree row global.protectedTags parent)) offset (offset+len) tree.locations) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    actual.outcome = .ok () ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global ∧
      actual.tree.locations.size = tree.locations.size ∧ actual.tree.nodes.size ≤ tree.nodes.size+1 ∧
      ∃ child, actual.tree.indexOfTag newTag = some child ∧
        OwnedOn (fun row => Nonempty (DuplicatePrefixBorrowAuthorization.Normal actual.tree row global.protectedTags child))
          offset (offset+len) actual.tree.locations := by
  have output := GeneralBorrowProtectedConstructorRuntime.construct tree global runtime parentTag newTag parent parentNode
    tagged present fresh room tagBound held offset len nonzero bounds
  refine ⟨output.1,output.2.1,output.2.2.1,output.2.2.2,?_⟩
  let rank := GeneralBorrowStructuralHistoryMutable.depth tree runtime.formed.toState
  let slot := GeneralBorrowStructuralHistoryMutable.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildMutable.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        noFree,aligned,fits,offset,len,nonzero,runtime.formed.well,bounds⟩
    have data := GeneralBorrowFreshMetadataChildMutable.append input
    have atEnd : (GeneralBorrowFreshMetadataChildMutable.index input).toNat = tree.nodes.data.size := GeneralBorrowFreshMetadataChildMutable.at_end input
    have vacant : tree.nodes.get (GeneralBorrowFreshMetadataChildMutable.index input) = none := by
      simp only [UniValMap.get,atEnd,Array.getElem?_eq_none (Nat.le_refl _)]
    have staged := stage_owned tree (GeneralBorrowFreshMetadataChildMutable.stage input) global.protectedTags parent
      (GeneralBorrowFreshMetadataChildMutable.index input) offset len runtime.formed.well bounds rfl
      (fun row => by
        obtain ⟨forest⟩ := runtime.formed.toState.forest row global.protectedTags
        have extension := append_extension tree (GeneralBorrowFreshMetadataChildMutable.index input) parent parentNode newTag atEnd present row global.protectedTags forest
        simpa only [GeneralBorrowFreshMetadataChildMutable.stage,input,GeneralBorrowFreshMetadataChildAttach.staged,projection_context] using extension) owned
    have result := shape_owned (GeneralBorrowFreshMetadataChildMutable.stage input)
      (GeneralBorrowFreshMetadataChildMutable.result input) global.protectedTags (GeneralBorrowFreshMetadataChildMutable.index input)
      offset (offset+len) (GeneralBorrowFreshMetadataChildMutable.shape input) staged
    exact ⟨GeneralBorrowFreshMetadataChildMutable.index input,data.freshLookup,result⟩
  | reuse index available bounded vacant slack =>
    let input : GeneralBorrowFreshMetadataChildMutableReuse.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        index,available,bounded,vacant,slack,offset,len,nonzero,runtime.formed.well,bounds⟩
    have data := GeneralBorrowFreshMetadataChildMutableReuse.reuse input
    have staged := stage_owned tree (GeneralBorrowFreshMetadataChildMutableReuse.stage input) global.protectedTags parent index
      offset len runtime.formed.well bounds rfl
      (fun row => by
        obtain ⟨forest⟩ := runtime.formed.toState.forest row global.protectedTags
        have extension := reuse_extension tree index parent parentNode newTag bounded vacant runtime.formed.fits present row global.protectedTags forest
        simpa only [GeneralBorrowFreshMetadataChildMutableReuse.stage,GeneralBorrowFreshMetadataChildMutableReuse.index,input,GeneralBorrowFreshMetadataChildAttach.staged,projection_context] using extension) owned
    have result := shape_owned (GeneralBorrowFreshMetadataChildMutableReuse.stage input)
      (GeneralBorrowFreshMetadataChildMutableReuse.result input) global.protectedTags index
      offset (offset+len) (GeneralBorrowFreshMetadataChildMutableReuse.shape input) staged
    exact ⟨index,data.freshLookup,result⟩

end DuplicatePrefix.CurrentCallEmptyEntryBoolChildNormal
