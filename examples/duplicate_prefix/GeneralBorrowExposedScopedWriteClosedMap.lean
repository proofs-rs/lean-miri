import duplicate_prefix.GeneralBorrowExposedScopedWriteClosedData
namespace DuplicatePrefix.GeneralBorrowExposedScopedWriteClosedMap
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
private theorem path_map {tree : BorrowTree} (map : DedupRangeMap LocationTree) {root index : UniIndex}
    (path : GeneralBorrowExposedNonleafPrimaryPath.Path tree root index) :
    GeneralBorrowExposedNonleafPrimaryPath.Path {tree with locations := map} root index := by
  induction path with
  | refl node present => exact .refl _ node present
  | step earlier node present edge ih => exact .step ih node present edge

private def virtual_map {tree location protections root} (map : DedupRangeMap LocationTree)
    (data : GeneralBorrowExposedKnownRootWriteState.Data tree location root protections) :
    GeneralBorrowExposedKnownRootWriteState.Data {tree with locations := map} location root protections where
  support := data.support
  rooted := data.rooted
  present := data.present
  children := data.children
  covers := data.covers
  coherent := data.coherent
  short := data.short
  depth := data.depth
  included := data.included
  profile := data.profile

private def primary_map {tree location protections root} (map : DedupRangeMap LocationTree)
    (data : GeneralBorrowExposedKnownRootWritePrimaryWitness.Data tree location root protections) :
    GeneralBorrowExposedKnownRootWritePrimaryWitness.Data {tree with locations := map} location root protections where
  base := virtual_map map data.base
  graph := data.graph
  witness := data.witness
  node := data.node
  present := data.present
  exposed := data.exposed
  support := data.support
  path := path_map map data.path

private def data_map {tree location protections anchor selected head tail}
    (map : DedupRangeMap LocationTree)
    (data : GeneralBorrowExposedKnownRootRangeData.Data tree location protections anchor selected head tail .Write) :
    GeneralBorrowExposedKnownRootRangeData.Data {tree with locations := map} location protections anchor selected head tail .Write where
  forest := data.forest
  component := data.component
  owned := data.owned
  rootPath := data.rootPath
  hidden := data.hidden
  separate := data.separate
  coherent := data.coherent
  profile := data.profile
  primary := fun different => primary_map map (data.primary different)
  virtual := fun root member different => virtual_map map (data.virtual root member different)

theorem post_map (tree : BorrowTree) (map : DedupRangeMap LocationTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor selected head : UniIndex) (tail : List UniIndex) :
    Nonempty (GeneralBorrowExposedKnownRootRangeData.Data {tree with locations := map} location protections anchor selected head tail .Write) =
      Nonempty (GeneralBorrowExposedKnownRootRangeData.Data tree location protections anchor selected head tail .Write) := by
  apply propext
  constructor
  · rintro ⟨data⟩
    exact ⟨data_map (tree := {tree with locations := map}) tree.locations data⟩
  · rintro ⟨data⟩
    exact ⟨data_map map data⟩
end DuplicatePrefix.GeneralBorrowExposedScopedWriteClosedMap
