import duplicate_prefix.GeneralBorrowFreshStagePool
import duplicate_prefix.GeneralBorrowTightAncestry
import duplicate_prefix.GeneralBorrowFreshSharedStagePaths
namespace DuplicatePrefix.GeneralBorrowFreshSharedNextPool
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralBorrowFreshSharedSequence DuplicatePrefix.GeneralBorrowFreshMixedChild
open DuplicatePrefix.GeneralBorrowFreshAllocatorInvariant DuplicatePrefix.GeneralBorrowFreshStagePool
open DuplicatePrefix.GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

private theorem projection_size (tree : BorrowTree) (location : LocationTree) (tags : ProtectedTags) :
    (source_normal_projection tree location tags).topology.nodes.size = tree.nodes.size := by
  unfold_general_projection
  unfold_general_topology
  simp only [Array.size_map,UniValMap.size]

private noncomputable def finish (tree : BorrowTree) (protections : ProtectedTags) (target : UniIndex)
    (exprTag nextTag : BorTag) (offset len : UInt64) (first : Data tree exprTag target offset len)
    (room : tree.nodes.size+1 ≤ 4294967295)
    (freshTag : GeneralBorrowTagMap.Fresh tree.tagMapping nextTag)
    (freshProtector : GeneralBorrowProtector.Fresh tree nextTag) (different : exprTag ≠ nextTag)
    (cleanVacant : ∀ query, tree.nodes.get query = none → GeneralBorrowFreshFutureClean.Clean tree query)
    (combined : OwnedOn (GeneralBorrowFreshReleaseMixed.Combined tree protections target (fun _ => true))
      offset (offset+len) tree.locations)
    (metadata : GeneralBorrowFreshStageMetadata.Output tree exprTag target offset len first protections false)
    (pool : Pool (child first protections false).tree.nodes (child first protections false).tree.tagMapping.deassigned)
    (accounting : Accounting (child first protections false).tree) :
    {second : Data (child first protections false).tree nextTag (index first) offset len //
      tree.nodes.get (index second) = none ∧ index second ≠ index first} := by
  classical
  let after := (child first protections false).tree
  let node := Classical.choose metadata.node
  have nodeFacts := Classical.choose_spec metadata.node
  have present : after.nodes.get (index first) = some node := nodeFacts.1
  have tableBound : after.nodes.size ≤ tree.nodes.size+1 := by
    have extension := metadata.extension default default protections
    rcases extension with appended | reused
    · have sizes := appended.length
      rw [projection_size,projection_size] at sizes
      change after.nodes.size = tree.nodes.size+1 at sizes
      exact Nat.le_of_eq sizes
    · have sizes := reused.length
      rw [projection_size,projection_size] at sizes
      change after.nodes.size = tree.nodes.size at sizes
      omega
  let depth := GeneralBorrowTightAncestry.tight after.nodes metadata.certificates.depth
  have slack : depth.depth (index first) < after.nodes.size :=
    GeneralBorrowTightAncestry.present_slack after.nodes metadata.certificates.depth (index first) node present
  have fits : after.tagMapping.mapping.size ≤ 4294967295 := by
    change Accounting after at accounting
    unfold Accounting at accounting
    omega
  let slot := GeneralBorrowFreshAllocatorInvariant.slot after depth (index first) pool
    (empty_aligned after accounting) (fun _ => fits) slack
  let query := GeneralBorrowFreshSharedWithinStages.slot_index slot
  have vacant : after.nodes.get query = none :=
    GeneralBorrowFreshSharedWithinStages.slot_vacant after depth (index first) slot
  have distinct : query ≠ index first := by
    intro equal
    rw [equal,present] at vacant
    cases vacant
  have initiallyVacant : tree.nodes.get query = none := by
    cases initial : tree.nodes.get query with
    | none => rfl
    | some old =>
      obtain ⟨next,lookup,_,_⟩ := GeneralBorrowFreshSharedStagePaths.old_node tree exprTag target offset len first protections false
        (fun _ => true) combined query old initial
      change after.nodes.get query = some next at lookup
      rw [vacant] at lookup
      cases lookup
  have cleaned := metadata.futureClean query initiallyVacant distinct (cleanVacant query initiallyVacant)
  have bounded : offset.toNat+len.toNat ≤ after.locations.size.bytes.toNat := by
    rw [metadata.capacity]
    exact first.bounds
  let second : Data after nextTag (index first) offset len := {
    parentTag := exprTag,root := first.root,parentNode := node,depth := depth
    children := metadata.certificates.children,parentPresent := present
    roots := metadata.roots.trans first.roots,covered := metadata.certificates.covered,parentTagPresent := metadata.lookup
    tagFresh := metadata.freshTag nextTag freshTag different
    protectorFresh := metadata.freshProtector nextTag freshProtector different
    nodeFits := by change after.nodes.data.size ≤ 4294967296;change after.nodes.size ≤ 4294967296;omega
    slot := slot,nonzero := first.nonzero,well := metadata.well,bounds := bounded,clean := cleaned }
  exact ⟨second,initiallyVacant,distinct⟩

/-- Build the second shared input after an actual first shared stage with any
coherent free pool. The initial room bound and all-vacant-slot cleanliness are
explicit conservative data; neither noFree nor post-state success/data is an
input. Tight ancestry reconstructs the next parent's rank slack. -/
noncomputable def next (tree : BorrowTree) (protections : ProtectedTags) (target : UniIndex)
    (exprTag nextTag : BorTag) (offset len : UInt64) (first : Data tree exprTag target offset len)
    (pool : Pool tree.nodes tree.tagMapping.deassigned) (accounting : Accounting tree)
    (room : tree.nodes.size+1 ≤ 4294967295)
    (freshTag : GeneralBorrowTagMap.Fresh tree.tagMapping nextTag)
    (freshProtector : GeneralBorrowProtector.Fresh tree nextTag) (different : exprTag ≠ nextTag)
    (cleanVacant : ∀ query, tree.nodes.get query = none → GeneralBorrowFreshFutureClean.Clean tree query)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned tree protections target .Write) offset (offset+len) tree.locations) :
    {second : Data (child first protections false).tree nextTag (index first) offset len //
      tree.nodes.get (index second) = none ∧ index second ≠ index first} := by
  have combined : OwnedOn (GeneralBorrowFreshReleaseMixed.Combined tree protections target (fun _ => true))
      offset (offset+len) tree.locations := by
    intro position valid positive lower upper
    exact write_combined tree _ protections target (owned position valid positive lower upper)
  have metadata := GeneralBorrowFreshStageMetadata.build tree exprTag target offset len first protections false (fun _ => true) combined
  have allocator := GeneralBorrowFreshStagePool.stage tree exprTag target offset len first protections false (fun _ => true) combined pool accounting
  exact finish tree protections target exprTag nextTag offset len first room freshTag freshProtector different cleanVacant combined
    metadata allocator.1 allocator.2

/-- Both actual shared stages complete using only original allocator and
ownership data, including reuse at either stage. The exact second Data is
constructed internally rather than supplied as an operation-success premise. -/
theorem two (tree : BorrowTree) (protections : ProtectedTags) (target : UniIndex)
    (exprTag nextTag : BorTag) (offset len : UInt64) (first : Data tree exprTag target offset len)
    (pool : Pool tree.nodes tree.tagMapping.deassigned) (accounting : Accounting tree)
    (room : tree.nodes.size+1 ≤ 4294967295)
    (freshTag : GeneralBorrowTagMap.Fresh tree.tagMapping nextTag)
    (freshProtector : GeneralBorrowProtector.Fresh tree nextTag) (different : exprTag ≠ nextTag)
    (cleanVacant : ∀ query, tree.nodes.get query = none → GeneralBorrowFreshFutureClean.Clean tree query)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned tree protections target .Write) offset (offset+len) tree.locations) :
    ∃ second : Data (child first protections false).tree nextTag (index first) offset len,
      tree.nodes.get (index second) = none ∧ index second ≠ index first ∧
      (read first protections false).status = .Completed ∧ (child first protections false).outcome = .ok () ∧
      (read second protections true).status = .Completed ∧ (child second protections true).outcome = .ok () ∧
      OwnedOn (GeneralBorrowFreshReleaseMixed.Combined (child second protections true).tree (registered protections nextTag true)
        (index second) (GeneralBorrowFreshSharedPrefix.labels (index first) (index second))) offset (offset+len)
        (child second protections true).tree.locations ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin (child second protections true).tree (index second) .Read offset (offset+len) := by
  let second := next tree protections target exprTag nextTag offset len first pool accounting room freshTag freshProtector different cleanVacant owned
  exact ⟨second.val,second.property.1,second.property.2,
    GeneralBorrowFreshSharedSequence.two tree protections target exprTag nextTag offset len first second.val owned⟩

end DuplicatePrefix.GeneralBorrowFreshSharedNextPool
