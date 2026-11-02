import duplicate_prefix.GeneralBorrowFreshSharedNext
import duplicate_prefix.GeneralBorrowFreshReleaseClean
import duplicate_prefix.GeneralBorrowFreshReleaseMixed
namespace DuplicatePrefix.GeneralBorrowFreshSharedTwoFuture
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralBorrowFreshSharedSequence DuplicatePrefix.GeneralBorrowFreshMixedChild
open DuplicatePrefix.GeneralBorrowFreshReleaseMixed
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

set_option autoImplicit false in
structure ReleasedFresh (tree : BorrowTree) (protections : ProtectedTags) (releaseTag : BorTag)
    (query : UniIndex) (tag : BorTag) : Prop where
  clean : GeneralBorrowFreshFutureClean.Clean (tree.releaseProtector releaseTag protections).tree query
  mapFresh : GeneralBorrowTagMap.Fresh (tree.releaseProtector releaseTag protections).tree.tagMapping tag
  nodeFresh : GeneralBorrowProtector.Fresh (tree.releaseProtector releaseTag protections).tree tag

set_option autoImplicit false in
private theorem finish_second (middle : BorrowTree) (protections : ProtectedTags) (parent : UniIndex)
    (newTag : BorTag) (offset len : UInt64) (second : Data middle newTag parent offset len)
    (noFree : middle.tagMapping.deassigned.back? = none)
    (aligned : middle.tagMapping.mapping.size = middle.nodes.data.size)
    (owned : OwnedOn (Combined middle protections parent (extend (fun _ => true) parent.toNat)) offset (offset+len) middle.locations)
    (query : UniIndex) (bound : middle.tagMapping.mapping.size+1 ≤ query.toNat)
    (clean : GeneralBorrowFreshFutureClean.Clean middle query)
    (tag : BorTag) (mapFresh : GeneralBorrowTagMap.Fresh middle.tagMapping tag)
    (nodeFresh : GeneralBorrowProtector.Fresh middle tag) (different : newTag ≠ tag) :
    GeneralBorrowFreshFutureClean.Clean (child second protections true).tree query ∧
      (child second protections true).tree.nodes.data.size ≤ query.toNat ∧
      GeneralBorrowTagMap.Fresh (child second protections true).tree.tagMapping tag ∧
      GeneralBorrowProtector.Fresh (child second protections true).tree tag := by
  obtain ⟨metadata⟩ : Nonempty (GeneralBorrowFreshStageMetadata.Output middle newTag parent offset len second protections true) :=
    ⟨GeneralBorrowFreshStageMetadata.build middle newTag parent offset len second protections true (extend (fun _ => true) parent.toNat) owned⟩
  have allocator := metadata.allocator noFree
  have queryBound : query.toNat < 4294967296 := UInt32.toNat_lt_size query.idx
  have vacant : middle.nodes.get query = none := by
    unfold UniValMap.get
    rw [Array.getElem?_eq_none (by omega : middle.nodes.data.size ≤ query.toNat)]
  have secondNat : (index second).toNat = middle.tagMapping.mapping.size := by
    unfold index
    cases slotEq : second.slot with
    | append empty aligned fits =>
      simp only [GeneralBorrowFreshSharedWithinStages.slot_index,UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega : middle.tagMapping.mapping.size < 4294967296)]
    | reuse q available bounded vacant slack => rw [noFree] at available;cases available
  have distinct : query ≠ index second := by intro same;have eq := congrArg UniIndex.toNat same;omega
  have size := allocator.2.1.symm.trans allocator.2.2
  exact ⟨metadata.futureClean query vacant distinct clean,(by omega),metadata.freshTag tag mapFresh different,
    metadata.freshProtector tag nodeFresh different⟩

set_option autoImplicit false in
private theorem finish_release (middle : BorrowTree) (protections : ProtectedTags) (parent : UniIndex)
    (newTag : BorTag) (offset len : UInt64) (second : Data middle newTag parent offset len)
    (noFree : middle.tagMapping.deassigned.back? = none)
    (aligned : middle.tagMapping.mapping.size = middle.nodes.data.size)
    (owned : OwnedOn (Combined middle protections parent (extend (fun _ => true) parent.toNat)) offset (offset+len) middle.locations)
    (query : UniIndex) (bound : middle.tagMapping.mapping.size+1 ≤ query.toNat)
    (clean : GeneralBorrowFreshFutureClean.Clean middle query)
    (tag : BorTag) (mapFresh : GeneralBorrowTagMap.Fresh middle.tagMapping tag)
    (nodeFresh : GeneralBorrowProtector.Fresh middle tag) (different : newTag ≠ tag)
    (positive : offset.toNat < (offset+len).toNat) :
    ReleasedFresh (child second protections true).tree (registered protections newTag true) newTag query tag := by
  let finalTree := (child second protections true).tree
  let held := registered protections newTag true
  let released := finalTree.releaseProtector newTag held
  have future := finish_second middle protections parent newTag offset len second noFree aligned owned query bound clean tag mapFresh nodeFresh different
  obtain ⟨metadata⟩ : Nonempty (GeneralBorrowFreshStageMetadata.Output middle newTag parent offset len second protections true) :=
    ⟨GeneralBorrowFreshStageMetadata.build middle newTag parent offset len second protections true (extend (fun _ => true) parent.toNat) owned⟩
  have completed := run middle newTag parent offset len second protections true (extend (fun _ => true) parent.toNat) owned
  have mixed := completed.2.2.1
  have active := GeneralBorrowFreshActiveWithin.active_on finalTree (index second) .Read offset (offset+len) metadata.well completed.2.2.2
  obtain ⟨node,present,nodeTag,notExposed⟩ := metadata.node
  have fits : finalTree.nodes.data.size ≤ 4294967296 := by
    have bounded : query.toNat < 4294967296 := UInt32.toNat_lt_size query.idx
    exact Nat.le_trans future.2.1 (by omega)
  have childOwned : OwnedOn (GeneralBorrowRange.LocationOwned finalTree held (index second) .Read)
      offset (offset+len) finalTree.locations := by
    intro position valid pos lower upper
    exact (mixed position valid pos lower upper).1
  have cleaned := GeneralBorrowFreshReleaseClean.release finalTree held newTag (index second) second.root .Read
    offset (offset+len) positive fits metadata.certificates.depth metadata.certificates.children node present notExposed
    (metadata.roots.trans second.roots) metadata.certificates.covered metadata.lookup active childOwned query future.2.1 future.1
  have frame := (GeneralBorrowFreshReleaseMixed.release_shared_mixed finalTree held newTag (index second) second.root
    (extend (extend (fun _ => true) parent.toNat) (index second).toNat) offset (offset+len) positive fits
    metadata.certificates.depth metadata.certificates.children node present notExposed (metadata.roots.trans second.roots)
    metadata.certificates.covered metadata.lookup active mixed).2.1
  refine ⟨cleaned.2.2,?_,?_⟩
  · change GeneralBorrowTagMap.Fresh released.tree.tagMapping tag
    rw [frame]
    exact future.2.2.1
  · change GeneralBorrowProtector.Fresh released.tree tag
    rw [frame]
    exact future.2.2.2

set_option autoImplicit false in
/-- Initial future-slot cleanliness and future-tag freshness survive both real
shared stages. The future slot is beyond both appended nodes. -/
theorem two (tree : BorrowTree) (protections : ProtectedTags) (target : UniIndex)
    (exprTag nextTag : BorTag) (offset len : UInt64) (first : Data tree exprTag target offset len)
    (noFree : tree.tagMapping.deassigned.back? = none) (room : tree.tagMapping.mapping.size+1 ≤ 4294967295)
    (freshTag : GeneralBorrowTagMap.Fresh tree.tagMapping nextTag)
    (freshProtector : GeneralBorrowProtector.Fresh tree nextTag) (different : exprTag ≠ nextTag)
    (cleanFuture : Every (fun location : LocationTree => location.perms.get (GeneralBorrowFreshSharedNext.future tree) = none) tree.locations)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned tree protections target .Write) offset (offset+len) tree.locations)
    (query : UniIndex) (futureBound : tree.tagMapping.mapping.size+2 ≤ query.toNat)
    (clean : GeneralBorrowFreshFutureClean.Clean tree query)
    (tag : BorTag) (mapFresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (nodeFresh : GeneralBorrowProtector.Fresh tree tag) (notExpr : exprTag ≠ tag) (notNext : nextTag ≠ tag) :
    let second := (GeneralBorrowFreshSharedNext.next tree protections target exprTag nextTag offset len first noFree room
      freshTag freshProtector different cleanFuture owned).val
    let finalTree := (child second protections true).tree
    GeneralBorrowFreshFutureClean.Clean finalTree query ∧ finalTree.nodes.data.size ≤ query.toNat ∧
      GeneralBorrowTagMap.Fresh finalTree.tagMapping tag ∧ GeneralBorrowProtector.Fresh finalTree tag := by
  generalize nextEq : GeneralBorrowFreshSharedNext.next tree protections target exprTag nextTag offset len first noFree room
    freshTag freshProtector different cleanFuture owned = choice
  rcases choice with ⟨second,nextIndex⟩
  dsimp only at ⊢
  have initial : OwnedOn (Combined tree protections target (fun _ => true)) offset (offset+len) tree.locations := by
    intro position valid positive lower upper
    exact write_combined tree _ protections target (owned position valid positive lower upper)
  have firstOwned := (run tree exprTag target offset len first protections false (fun _ => true) initial).2.2.1
  change OwnedOn (Combined (child first protections false).tree protections (index first)
    (extend (fun _ => true) (index first).toNat)) offset (offset+len) (child first protections false).tree.locations at firstOwned
  obtain ⟨one⟩ : Nonempty (GeneralBorrowFreshStageMetadata.Output tree exprTag target offset len first protections false) :=
    ⟨GeneralBorrowFreshStageMetadata.build tree exprTag target offset len first protections false (fun _ => true) initial⟩
  let middle := (child first protections false).tree
  have allocator1 := one.allocator noFree
  have middleNodes : middle.nodes.data.size = tree.tagMapping.mapping.size+1 := allocator1.2.1.symm.trans allocator1.2.2
  have initialAligned : tree.tagMapping.mapping.size = tree.nodes.data.size := by
    cases first.slot with
    | append empty aligned fits => exact aligned
    | reuse q available bounded vacant slack => rw [noFree] at available;cases available
  have firstNat : (index first).toNat = tree.tagMapping.mapping.size := by
    unfold index
    cases slotEq : first.slot with
    | append empty aligned fits =>
      simp only [GeneralBorrowFreshSharedWithinStages.slot_index,UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega : tree.tagMapping.mapping.size < 4294967296)]
    | reuse q available bounded vacant slack => rw [noFree] at available;cases available
  have vacant : tree.nodes.get query = none := by
    unfold UniValMap.get
    rw [Array.getElem?_eq_none (by omega : tree.nodes.data.size ≤ query.toNat)]
  have distinct1 : query ≠ index first := by intro same;have eq := congrArg UniIndex.toNat same;omega
  have clean1 := one.futureClean query vacant distinct1 clean
  exact finish_second middle protections (index first) nextTag offset len second allocator1.1 allocator1.2.1 firstOwned
    query (by rw [allocator1.2.2];exact futureBound) clean1 tag (one.freshTag tag mapFresh notExpr)
    (one.freshProtector tag nodeFresh notExpr) notNext

theorem release (tree : BorrowTree) (protections : ProtectedTags) (target : UniIndex)
    (exprTag nextTag : BorTag) (offset len : UInt64) (first : Data tree exprTag target offset len)
    (noFree : tree.tagMapping.deassigned.back? = none) (room : tree.tagMapping.mapping.size+1 ≤ 4294967295)
    (freshTag : GeneralBorrowTagMap.Fresh tree.tagMapping nextTag)
    (freshProtector : GeneralBorrowProtector.Fresh tree nextTag) (different : exprTag ≠ nextTag)
    (cleanFuture : Every (fun location : LocationTree => location.perms.get (GeneralBorrowFreshSharedNext.future tree) = none) tree.locations)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned tree protections target .Write) offset (offset+len) tree.locations)
    (query : UniIndex) (futureBound : tree.tagMapping.mapping.size+2 ≤ query.toNat)
    (clean : GeneralBorrowFreshFutureClean.Clean tree query)
    (tag : BorTag) (mapFresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (nodeFresh : GeneralBorrowProtector.Fresh tree tag) (notExpr : exprTag ≠ tag) (notNext : nextTag ≠ tag)
    (positive : offset.toNat < (offset+len).toNat) :
    let second := (GeneralBorrowFreshSharedNext.next tree protections target exprTag nextTag offset len first noFree room
      freshTag freshProtector different cleanFuture owned).val
    ReleasedFresh (child second protections true).tree (registered protections nextTag true) nextTag query tag := by
  generalize nextEq : GeneralBorrowFreshSharedNext.next tree protections target exprTag nextTag offset len first noFree room
    freshTag freshProtector different cleanFuture owned = choice
  rcases choice with ⟨second,nextIndex⟩
  dsimp only at ⊢
  have initial : OwnedOn (Combined tree protections target (fun _ => true)) offset (offset+len) tree.locations := by
    intro position valid positive lower upper
    exact write_combined tree _ protections target (owned position valid positive lower upper)
  have firstOwned := (run tree exprTag target offset len first protections false (fun _ => true) initial).2.2.1
  change OwnedOn (Combined (child first protections false).tree protections (index first)
    (extend (fun _ => true) (index first).toNat)) offset (offset+len) (child first protections false).tree.locations at firstOwned
  obtain ⟨one⟩ : Nonempty (GeneralBorrowFreshStageMetadata.Output tree exprTag target offset len first protections false) :=
    ⟨GeneralBorrowFreshStageMetadata.build tree exprTag target offset len first protections false (fun _ => true) initial⟩
  let middle := (child first protections false).tree
  have allocator1 := one.allocator noFree
  have middleNodes : middle.nodes.data.size = tree.tagMapping.mapping.size+1 := allocator1.2.1.symm.trans allocator1.2.2
  have initialAligned : tree.tagMapping.mapping.size = tree.nodes.data.size := by
    cases first.slot with
    | append empty aligned fits => exact aligned
    | reuse q available bounded vacant slack => rw [noFree] at available;cases available
  have firstNat : (index first).toNat = tree.tagMapping.mapping.size := by
    unfold index
    cases slotEq : first.slot with
    | append empty aligned fits =>
      simp only [GeneralBorrowFreshSharedWithinStages.slot_index,UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega : tree.tagMapping.mapping.size < 4294967296)]
    | reuse q available bounded vacant slack => rw [noFree] at available;cases available
  have vacant : tree.nodes.get query = none := by
    unfold UniValMap.get
    rw [Array.getElem?_eq_none (by omega : tree.nodes.data.size ≤ query.toNat)]
  have distinct1 : query ≠ index first := by intro same;have eq := congrArg UniIndex.toNat same;omega
  have clean1 := one.futureClean query vacant distinct1 clean
  exact finish_release middle protections (index first) nextTag offset len second allocator1.1 allocator1.2.1 firstOwned
    query (by rw [allocator1.2.2];exact futureBound) clean1 tag (one.freshTag tag mapFresh notExpr)
    (one.freshProtector tag nodeFresh notExpr) notNext positive

end DuplicatePrefix.GeneralBorrowFreshSharedTwoFuture
