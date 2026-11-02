import duplicate_prefix.GeneralBorrowExposedScopedMixedRebase
namespace DuplicatePrefix.GeneralBorrowExposedScopedMixedClosedData
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open GeneralBorrowExposedKnownRootState (Scope)
open GeneralBorrowExposedScopedMixedRangeData (Data)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- The output is another complete raw initial contract, suitable for another
physical Read or protector-end callback without a new success assumption. -/
theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor selected head : UniIndex) (tail : List UniIndex) (mode : ChildrenVisitMode) (range : ByteRange)
    (context : GeneralBorrowExposedKnownRootRangeData.Context tree anchor selected head tail)
    (support : Nat → Prop) (writable : Nat → Bool) (fits : tree.nodes.data.size ≤ 4294967296)
    (data : Data tree location protections anchor selected head tail support writable) :
    source_access_status (source_tree_access_at tree location (some anchor) .Read protections mode range) = none ∧
      Nonempty (Data tree (source_access_location (source_tree_access_at tree location (some anchor) .Read protections mode range))
        protections anchor selected head tail support writable) := by
  obtain ⟨after,actual,status,frame,profile,coherent,outside⟩ := GeneralBorrowExposedScopedReadFrameAccess.access tree location protections
    anchor selected head context.anchorNode context.selectedNode tail mode range context.roots data.base.forest data.base.component data.base.owned
    context.depth context.children context.anchorPresent context.selectedPresent data.base.rootPath data.base.hidden data.base.separate
    data.base.coherent data.base.profile context.tags data.base.primary data.base.virtual
  have complete := GeneralBorrowExposedScopedMixedRangeData.access tree location protections anchor selected head tail mode range context support writable fits data
  have mixed := complete.2.2
  rw [actual] at mixed
  refine ⟨status,?_⟩
  rw [actual]
  exact ⟨GeneralBorrowExposedScopedMixedRebase.rebase data after frame coherent profile mixed⟩

private theorem path_map {tree : BorrowTree} (map : DedupRangeMap LocationTree) {root index : UniIndex}
    (path : GeneralBorrowExposedNonleafPrimaryPath.Path tree root index) :
    GeneralBorrowExposedNonleafPrimaryPath.Path {tree with locations := map} root index := by
  induction path with
  | refl node present => exact .refl _ node present
  | step earlier node present edge ih => exact .step ih node present edge

private def virtual_map {tree location protections root} (map : DedupRangeMap LocationTree)
    (data : GeneralBorrowExposedKnownRootState.Data tree location root protections) :
    GeneralBorrowExposedKnownRootState.Data {tree with locations := map} location root protections where
  support := data.support
  rooted := data.rooted
  present := data.present
  children := data.children
  covers := data.covers
  coherent := data.coherent
  short := data.short
  depth := data.depth
  included := data.included
  readable := data.readable

private def primary_map {tree location protections root} (map : DedupRangeMap LocationTree)
    (data : GeneralBorrowExposedKnownRootPrimaryWitness.Data tree location root protections) :
    GeneralBorrowExposedKnownRootPrimaryWitness.Data {tree with locations := map} location root protections where
  base := virtual_map map data.base
  graph := data.graph
  witness := data.witness
  node := data.node
  present := data.present
  exposed := data.exposed
  support := data.support
  path := path_map map data.path

private def data_map {tree location protections anchor selected head tail support writable}
    (map : DedupRangeMap LocationTree) (data : Data tree location protections anchor selected head tail support writable) :
    Data {tree with locations := map} location protections anchor selected head tail support writable where
  base := {
    forest := data.base.forest
    component := data.base.component
    owned := data.base.owned
    rootPath := data.base.rootPath
    hidden := data.base.hidden
    separate := data.base.separate
    coherent := data.base.coherent
    profile := data.base.profile
    primary := fun different => primary_map map (data.base.primary different)
    virtual := fun root member different => virtual_map map (data.base.virtual root member different) }
  support_eq := data.support_eq
  mixed := data.mixed

theorem post_map (tree : BorrowTree) (map : DedupRangeMap LocationTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor selected head : UniIndex) (tail : List UniIndex) (support : Nat → Prop) (writable : Nat → Bool) :
    Nonempty (Data {tree with locations := map} location protections anchor selected head tail support writable) =
      Nonempty (Data tree location protections anchor selected head tail support writable) := by
  apply propext
  constructor
  · rintro ⟨data⟩
    exact ⟨data_map (tree := {tree with locations := map}) tree.locations data⟩
  · rintro ⟨data⟩
    exact ⟨data_map map data⟩
end DuplicatePrefix.GeneralBorrowExposedScopedMixedClosedData
