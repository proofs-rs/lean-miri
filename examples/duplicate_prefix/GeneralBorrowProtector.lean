import duplicate_prefix.GeneralBorrowRange
import duplicate_prefix.ProtectorInsertion
namespace DuplicatePrefix.GeneralBorrowProtector
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open DuplicatePrefix.GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

private theorem filterMap_congr_on {α β : Type} (rows : List α) (left right : α → Option β)
    (same : ∀ row ∈ rows, left row = right row) : rows.filterMap left = rows.filterMap right := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    rw [List.filterMap_cons,List.filterMap_cons,same row (by simp)]
    rw [ih (fun other member => same other (by simp [member]))]

/-- Freshness of a new protector for the allocation's existing node data.
This condition concerns actual stored nodes, rather than an operation outcome. -/
def Fresh (tree : BorrowTree) (tag : BorTag) : Prop :=
  ∀ row ∈ tree.nodes.entries, row.2.tag ≠ tag

/-- Installing a protector for a fresh tag changes no projected permission,
ancestor or existing protector data of an arbitrary caller tree. -/
theorem normal_projection (tree : BorrowTree) (location : LocationTree)
    (protections : ProtectedTags) (tag : BorTag) (kind : ProtectorKind)
    (fresh : Fresh tree tag) :
    source_normal_projection tree location (protections.insert tag kind) =
      source_normal_projection tree location protections := by
  have projected : tree.nodes.entries.toList.filterMap
      (fun row => if (protections.insert tag kind).contains row.2.tag then some row.1.toNat else none) =
      tree.nodes.entries.toList.filterMap
      (fun row => if protections.contains row.2.tag then some row.1.toNat else none) := by
    apply filterMap_congr_on
    intro row member
    rw [ProtectorInsertion.contains_other protections tag row.2.tag kind
      (fresh row (by simpa only [Array.mem_def] using member))]
  unfold_general_projection
  rw [projected]

/-- The ownership invariant of any old anchor survives actual fresh protector
insertion. The new child's topology and state still need separate construction. -/
theorem anchor_owned (tree : BorrowTree) (location : LocationTree)
    (protections : ProtectedTags) (tag : BorTag) (protector : ProtectorKind)
    (fresh : Fresh tree tag) (anchor : Nat) (kind : AccessKind)
    (owned : GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree location protections) anchor kind) :
    GeneralBorrowAnchor.AnchorOwned
      (source_normal_projection tree location (protections.insert tag protector)) anchor kind := by
  rw [normal_projection tree location protections tag protector fresh]
  exact owned

/-- The full data invariant for all range-map segments is preserved. -/
theorem range_owned (tree : BorrowTree) (protections : ProtectedTags)
    (tag : BorTag) (protector : ProtectorKind) (fresh : Fresh tree tag)
    (anchor : UniIndex) (kind : AccessKind)
    (owned : Every (GeneralBorrowRange.LocationOwned tree protections anchor kind) tree.locations) :
    Every (GeneralBorrowRange.LocationOwned tree (protections.insert tag protector) anchor kind) tree.locations := by
  intro position valid
  have old := owned position valid
  unfold GeneralBorrowRange.LocationOwned at old ⊢
  rw [normal_projection tree _ protections tag protector fresh]
  exact old

/-- Concrete ranged accesses through old tags remain proved after the real
insertion of an unrelated fresh protector, under the same caller-data contract. -/
theorem access (tree : BorrowTree) (protections : ProtectedTags)
    (newTag tag : BorTag) (protector : ProtectorKind) (fresh : Fresh tree newTag)
    (anchor root : UniIndex) (offset len : Miri.ABI.Size) (kind : AccessKind) (mode : ChildrenVisitMode)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (roots : tree.roots = #[root]) (covered : GeneralBorrowGraph.RootsCover tree)
    (tagPresent : tree.indexOfTag tag = some anchor) (well : tree.locations.WellFormed)
    (owned : Every (GeneralBorrowRange.LocationOwned tree protections anchor kind) tree.locations)
    (bounds : offset.bytes.toNat + len.bytes.toNat ≤ tree.locations.size.bytes.toNat) :
    (tree.performNormalAccessRange tag offset len kind (protections.insert newTag protector) mode).status = .Completed := by
  exact GeneralBorrowRange.access tree (protections.insert newTag protector) tag anchor root offset len kind mode
    depth children anchorNode anchorPresent roots covered tagPresent well
    (range_owned tree protections newTag protector fresh anchor kind owned) bounds

end DuplicatePrefix.GeneralBorrowProtector
#print axioms DuplicatePrefix.GeneralBorrowProtector.access
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowProtector." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved general protector dependency {dependency}"
