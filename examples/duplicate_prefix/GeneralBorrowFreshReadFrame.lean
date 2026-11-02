import duplicate_prefix.GeneralBorrowRangeLocal
import duplicate_prefix.GeneralBorrowProtector
namespace DuplicatePrefix.GeneralBorrowFreshReadFrame
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapOrigins
set_option maxRecDepth 65536
set_option maxHeartbeats 300000

/-- Ranged access changes only location data, on either outcome. This equality
transports topology, tags, roots and allocator metadata without assuming access
completion or replacing a failed operation by successful execution. -/
theorem frame (tree : BorrowTree) (provenance : ProvenanceExtra) (offset len : Size)
    (kind : AccessKind) (protections : ProtectedTags) (mode : ChildrenVisitMode) :
    let result := tree.performBorrowAccessRange provenance offset len kind protections mode
    result.tree = {tree with locations := result.tree.locations} := by
  cases provenance with
  | concrete tag =>
    cases found : tree.indexOfTag tag with
    | none =>
      simp only [BorrowTree.performBorrowAccessRange,found,Option.isNone_none,↓reduceIte,Id.run,pure]
    | some index =>
      simp only [BorrowTree.performBorrowAccessRange,found,Option.isNone_some,Bool.false_eq_true,↓reduceIte,Id.run,bind,pure]
      cases outcome : (tree.locations.iterMut offset len).outcome <;> rfl
  | wildcard =>
    simp only [BorrowTree.performBorrowAccessRange,Id.run,bind,pure]
    cases outcome : (tree.locations.iterMut offset len).outcome <;> rfl

/-- Transport the data certificate while retaining its exact rank function. -/
def depth_on (before after : BorrowTree) (same : after.nodes = before.nodes)
    (depth : GeneralBorrowExposure.ParentDepth before.nodes) : GeneralBorrowExposure.ParentDepth after.nodes where
  depth := depth.depth
  bounded := by
    intro index node lookup
    rw [same] at lookup ⊢
    exact depth.bounded index node lookup
  parent := by
    intro index node lookup earlier edge
    rw [same] at lookup
    obtain ⟨ancestor,present,smaller⟩ := depth.parent index node lookup earlier edge
    exact ⟨ancestor,by rw [same];exact present,smaller⟩

/-- Child-reference validity and root coverage depend on unchanged metadata,
so both survive an arbitrary replacement of location state. -/
theorem graph_on (tree : BorrowTree) (locations : Miri.DataStructures.DedupRangeMap LocationTree)
    (children : GeneralBorrowGraph.ChildNodes tree) (covered : GeneralBorrowGraph.RootsCover tree) :
    GeneralBorrowGraph.ChildNodes {tree with locations := locations} ∧
      GeneralBorrowGraph.RootsCover {tree with locations := locations} := ⟨children,covered⟩

/-- Registering a genuinely fresh protector preserves slice-local ownership
at the old anchor. No property is imposed on disjoint allocation segments. -/
theorem protector_owned_on (tree : BorrowTree) (protections : ProtectedTags)
    (tag : BorTag) (protector : ProtectorKind) (fresh : GeneralBorrowProtector.Fresh tree tag)
    (anchor : UniIndex) (kind : AccessKind) (lower upper : UInt64)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned tree protections anchor kind) lower upper tree.locations) :
    OwnedOn (GeneralBorrowRange.LocationOwned tree (protections.insert tag protector) anchor kind) lower upper tree.locations := by
  intro position valid positive start stop
  have previous := owned position valid positive start stop
  unfold GeneralBorrowRange.LocationOwned at previous ⊢
  rw [GeneralBorrowProtector.normal_projection tree _ protections tag protector fresh]
  exact previous
end DuplicatePrefix.GeneralBorrowFreshReadFrame
#print axioms DuplicatePrefix.GeneralBorrowFreshReadFrame.frame

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshReadFrame." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved ranged metadata dependency {dependency}"
