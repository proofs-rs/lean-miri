import duplicate_prefix.GeneralBorrowFreshSharedTwoTargetWithin
import duplicate_prefix.GeneralBorrowFreshSharedReleaseWithin
namespace DuplicatePrefix.GeneralBorrowFreshSharedTwoReleaseWithin
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralBorrowFreshSharedSequence DuplicatePrefix.GeneralBorrowFreshMixedChild
open DuplicatePrefix.GeneralBorrowFreshReleaseMixed DuplicatePrefix.GeneralBorrowFreshActiveWithin
set_option maxRecDepth 65536
set_option maxHeartbeats 800000

private theorem projection_size (tree : BorrowTree) (location : LocationTree) (tags : ProtectedTags) :
    (source_normal_projection tree location tags).topology.nodes.size = tree.nodes.size := by
  unfold_general_projection
  unfold_general_topology
  simp only [Array.size_map,UniValMap.size]

private theorem table_bound (tree : BorrowTree) (newTag : BorTag) (parent : UniIndex) (offset len : UInt64)
    (data : Data tree newTag parent offset len) (protections : ProtectedTags) (protectedFlag : Bool)
    (metadata : GeneralBorrowFreshStageMetadata.Output tree newTag parent offset len data protections protectedFlag) :
    (child data protections protectedFlag).tree.nodes.size ≤ tree.nodes.size+1 := by
  rcases metadata.extension default default protections with appended | reused
  · have same := appended.length
    rw [projection_size,projection_size] at same
    omega
  · have same := reused.length
    rw [projection_size,projection_size] at same
    omega

private theorem capacity_tail (P Q R S T : Prop) (a b c : Size)
    (facts : P ∧ Q ∧ R ∧ S ∧ T ∧ a = b) (same : b = c) : P ∧ Q ∧ R ∧ S ∧ T ∧ a = c :=
  ⟨facts.1,facts.2.1,facts.2.2.1,facts.2.2.2.1,facts.2.2.2.2.1,facts.2.2.2.2.2.trans same⟩

private theorem finish_second (middle : BorrowTree) (protections : ProtectedTags) (target expr : UniIndex)
    (nextTag : BorTag) (offset len : UInt64) (second : Data middle nextTag expr offset len)
    (roomData : middle.nodes.size ≤ 4294967295)
    (owned : OwnedOn (Combined middle protections expr (extend (fun _ => true) expr.toNat)) offset (offset+len) middle.locations)
    (positive : offset.toNat < (offset+len).toNat)
    (active : ActiveWithin middle target .Write offset (offset+len)) :
    let finalTree := (child second protections true).tree
    let result := finalTree.releaseProtector nextTag (registered protections nextTag true)
    result.status = .Released ∧ result.tree = {finalTree with locations := result.tree.locations} ∧
    OwnedOn (GeneralBorrowRange.LocationOwned result.tree (registered protections nextTag true) (index second) .Read)
      offset (offset+len) result.tree.locations ∧
    ActiveWithin result.tree target .Write offset (offset+len) ∧ result.tree.locations.WellFormed ∧
    result.tree.locations.size = middle.locations.size := by
  have completed := GeneralBorrowFreshSharedSequence.run middle nextTag expr offset len second protections true
    (extend (fun _ => true) expr.toNat) owned
  have built := GeneralBorrowFreshStageMetadata.build middle nextTag expr offset len second protections true
    (extend (fun _ => true) expr.toNat) owned
  obtain ⟨metadata⟩ : Nonempty (GeneralBorrowFreshStageMetadata.Output middle nextTag expr offset len second protections true) := ⟨built⟩
  have bounded := table_bound middle nextTag expr offset len second protections true metadata
  have fit : (child second protections true).tree.nodes.data.size ≤ 4294967296 := by
    change (child second protections true).tree.nodes.size ≤ 4294967296
    omega
  obtain ⟨node,nodePresent,nodeTag,nodeUnexposed⟩ := metadata.node
  have childOwners : OwnedOn (GeneralBorrowRange.LocationOwned (child second protections true).tree
      (registered protections nextTag true) (index second) .Read) offset (offset+len) (child second protections true).tree.locations := by
    intro position valid pos lower upper
    exact (completed.2.2.1 position valid pos lower upper).1
  have targetActive := GeneralBorrowFreshSharedTargetActivity.preserves_target middle nextTag expr offset len second protections true
    (extend (fun _ => true) expr.toNat) owned target offset (offset+len) (Nat.le_refl _) (Nat.le_refl _) active
  have ready := GeneralBorrowFreshSharedReleaseWithin.release (child second protections true).tree (registered protections nextTag true)
    nextTag (index second) second.root .Read offset (offset+len) positive fit metadata.certificates.depth metadata.certificates.children
    node nodePresent nodeUnexposed (metadata.roots.trans second.roots) metadata.certificates.covered metadata.lookup completed.2.2.2
    target metadata.well targetActive childOwners
  exact capacity_tail _ _ _ _ _ _ _ _ ready metadata.capacity

/-- Arbitrary allocator slots in both actual shared stages preserve the older
mutable anchor's strong Write profile through actual protector release. The
second structural input is independent of append/reuse; no success is assumed. -/
theorem complete_data (tree : BorrowTree) (protections : ProtectedTags) (target : UniIndex)
    (exprTag nextTag : BorTag) (offset len : UInt64) (first : Data tree exprTag target offset len)
    (second : Data (child first protections false).tree nextTag (index first) offset len)
    (roomData : tree.nodes.data.size+1 ≤ 4294967295)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned tree protections target .Write) offset (offset+len) tree.locations)
    (positive : offset.toNat < (offset+len).toNat)
    (active : ActiveWithin tree target .Write offset (offset+len)) :
    let finalTree := (child second protections true).tree
    let result := finalTree.releaseProtector nextTag (registered protections nextTag true)
    result.status = .Released ∧ result.tree = {finalTree with locations := result.tree.locations} ∧
    OwnedOn (GeneralBorrowRange.LocationOwned result.tree (registered protections nextTag true) (index second) .Read)
      offset (offset+len) result.tree.locations ∧
    ActiveWithin result.tree target .Write offset (offset+len) ∧ result.tree.locations.WellFormed ∧
    result.tree.locations.size = tree.locations.size := by
  have initial : OwnedOn (Combined tree protections target (fun _ => true)) offset (offset+len) tree.locations := by
    intro position valid pos lower upper
    exact write_combined tree _ protections target (owned position valid pos lower upper)
  have one := GeneralBorrowFreshSharedSequence.run tree exprTag target offset len first protections false (fun _ => true) initial
  have firstOwned := one.2.2.1
  have regFalse : registered protections exprTag false = protections := by simp only [registered,Bool.false_eq_true,↓reduceIte]
  rw [regFalse] at firstOwned
  have built := GeneralBorrowFreshStageMetadata.build tree exprTag target offset len first protections false (fun _ => true) initial
  obtain ⟨metadata⟩ : Nonempty (GeneralBorrowFreshStageMetadata.Output tree exprTag target offset len first protections false) := ⟨built⟩
  have bounded := table_bound tree exprTag target offset len first protections false metadata
  have middleRoom : (child first protections false).tree.nodes.size ≤ 4294967295 := by
    change tree.nodes.size+1 ≤ 4294967295 at roomData
    omega
  have firstActive := GeneralBorrowFreshSharedTargetActivity.preserves_target tree exprTag target offset len first protections false
    (fun _ => true) initial target offset (offset+len) (Nat.le_refl _) (Nat.le_refl _) active
  have answer := finish_second (child first protections false).tree protections target (index first) nextTag offset len second
    middleRoom firstOwned positive firstActive
  exact capacity_tail _ _ _ _ _ _ _ _ answer metadata.capacity

/-- Initial mutable ownership, initial strong activity and the original append
allocator data suffice for both actual shared stages and the actual protector
release. All final graph/child ownership/profile data is derived internally.
The exposed release result supplies frame, partition validity and original
capacity alongside target strong Write activity; global endCall changes none
of this tree data. Single-root append/append scope is explicit in Data/noFree. -/
theorem complete (tree : BorrowTree) (protections : ProtectedTags) (target : UniIndex)
    (exprTag nextTag : BorTag) (offset len : UInt64) (first : Data tree exprTag target offset len)
    (noFree : tree.tagMapping.deassigned.back? = none) (room : tree.tagMapping.mapping.size+1 ≤ 4294967295)
    (freshTag : GeneralBorrowTagMap.Fresh tree.tagMapping nextTag)
    (freshProtector : GeneralBorrowProtector.Fresh tree nextTag) (different : exprTag ≠ nextTag)
    (cleanFuture : Every (fun location : LocationTree => location.perms.get (GeneralBorrowFreshSharedNext.future tree) = none) tree.locations)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned tree protections target .Write) offset (offset+len) tree.locations)
    (positive : offset.toNat < (offset+len).toNat)
    (active : ActiveWithin tree target .Write offset (offset+len)) :
    let choice := GeneralBorrowFreshSharedNext.next tree protections target exprTag nextTag offset len first noFree room
      freshTag freshProtector different cleanFuture owned
    let finalTree := (child choice.val protections true).tree
    let result := finalTree.releaseProtector nextTag (registered protections nextTag true)
    result.status = .Released ∧ result.tree = {finalTree with locations := result.tree.locations} ∧
    OwnedOn (GeneralBorrowRange.LocationOwned result.tree (registered protections nextTag true) (index choice.val) .Read)
      offset (offset+len) result.tree.locations ∧
    ActiveWithin result.tree target .Write offset (offset+len) ∧ result.tree.locations.WellFormed ∧
    result.tree.locations.size = tree.locations.size := by
  generalize nextEq : GeneralBorrowFreshSharedNext.next tree protections target exprTag nextTag offset len first noFree room
    freshTag freshProtector different cleanFuture owned = choice
  rcases choice with ⟨second,nextIndex⟩
  dsimp only at ⊢
  have aligned : tree.tagMapping.mapping.size = tree.nodes.data.size := by
    cases first.slot with
    | append _ aligned _ => exact aligned
    | reuse candidate available bounded vacant slack => rw [noFree] at available;cases available
  have roomData : tree.nodes.data.size+1 ≤ 4294967295 := by rw [←aligned];exact room
  exact complete_data tree protections target exprTag nextTag offset len first second roomData owned positive active
end DuplicatePrefix.GeneralBorrowFreshSharedTwoReleaseWithin
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshSharedTwoReleaseWithin." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved shared two release within dependency {dependency}"
