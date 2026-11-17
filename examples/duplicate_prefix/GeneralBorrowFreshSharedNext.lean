import duplicate_prefix.GeneralBorrowFreshStageMetadata
namespace DuplicatePrefix.GeneralBorrowFreshSharedNext
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralBorrowFreshSharedSequence DuplicatePrefix.GeneralBorrowFreshMixedChild
set_option maxRecDepth 65536
set_option maxHeartbeats 800000

def future (tree : BorrowTree) : UniIndex := ⟨UInt32.ofNat (tree.tagMapping.mapping.size+1)⟩

/-- Build the second append reborrow's complete input from initial caller data
and the actual first stage. No certificate, cleanliness, ownership or operation
success for a post-state is assumed. The two future slots must initially be
clean; free-index reuse and further roots remain separate cases. -/
noncomputable def next (tree : BorrowTree) (protections : ProtectedTags) (target : UniIndex)
    (exprTag nextTag : BorTag) (offset len : UInt64) (first : Data tree exprTag target offset len)
    (noFree : tree.tagMapping.deassigned.back? = none)
    (room : tree.tagMapping.mapping.size+1 ≤ 4294967295)
    (freshTag : GeneralBorrowTagMap.Fresh tree.tagMapping nextTag)
    (freshProtector : GeneralBorrowProtector.Fresh tree nextTag) (different : exprTag ≠ nextTag)
    (cleanFuture : Every (fun location : LocationTree => location.perms.get (future tree) = none) tree.locations)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned tree protections target .Write) offset (offset+len) tree.locations) :
    {second : Data (child first protections false).tree nextTag (index first) offset len // index second = future tree} := by
  classical
  have combined : OwnedOn (GeneralBorrowFreshReleaseMixed.Combined tree protections target (fun _ => true))
      offset (offset+len) tree.locations := by
    intro position valid positive lower upper
    exact write_combined tree _ protections target (owned position valid positive lower upper)
  let metadata := GeneralBorrowFreshStageMetadata.build tree exprTag target offset len first protections false (fun _ => true) combined
  have allocator := metadata.allocator noFree
  have nextFits : (child first protections false).tree.tagMapping.mapping.size ≤ 4294967295 := by rw [allocator.2.2];exact room
  have nodeFits : (child first protections false).tree.nodes.data.size ≤ 4294967296 := by
    rw [←allocator.2.1]
    omega
  have initialAligned : tree.tagMapping.mapping.size = tree.nodes.data.size := by
    cases first.slot with
    | append empty aligned fits => exact aligned
    | reuse candidate available bounded vacant slack => rw [noFree] at available;cases available
  have firstValue : (index first).toNat = tree.tagMapping.mapping.size := by
    cases slotEq : first.slot with
    | append empty aligned fits =>
      simp only [index,GeneralBorrowFreshSharedWithinStages.slot_index,slotEq,UniIndex.toNat,UInt32.toNat_ofNat',
        Nat.mod_eq_of_lt (by omega : tree.tagMapping.mapping.size < 2^32)]
    | reuse candidate available bounded vacant slack => rw [noFree] at available;cases available
  have futureValue : (future tree).toNat = tree.tagMapping.mapping.size+1 := by
    simp only [future,UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega : tree.tagMapping.mapping.size+1 < 2^32)]
  have vacantFuture : tree.nodes.get (future tree) = none := by
    unfold UniValMap.get
    rw [Array.getElem?_eq_none (by omega : tree.nodes.data.size ≤ (future tree).toNat)]
  have differentIndex : future tree ≠ index first := by
    intro equal
    have value := congrArg UniIndex.toNat equal
    omega
  have cleaned := metadata.futureClean (future tree) vacantFuture differentIndex cleanFuture
  have bounded : offset.toNat+len.toNat ≤ (child first protections false).tree.locations.size.bytes.toNat := by
    rw [metadata.capacity]
    exact first.bounds
  let nextSlot : GeneralBorrowFreshReborrowStages.Slot (child first protections false).tree metadata.certificates.depth (index first) :=
    GeneralBorrowFreshReborrowStages.Slot.append allocator.1 allocator.2.1 nextFits
  have nextIndex : GeneralBorrowFreshSharedWithinStages.slot_index nextSlot = future tree := by
    simp only [nextSlot,GeneralBorrowFreshSharedWithinStages.slot_index,future,allocator.2.2]
  let node := Classical.choose metadata.node
  have nodeFacts := Classical.choose_spec metadata.node
  let second : Data (child first protections false).tree nextTag (index first) offset len := {
    parentTag := exprTag,root := first.root,parentNode := node,depth := metadata.certificates.depth
    children := metadata.certificates.children,parentPresent := nodeFacts.1
    roots := metadata.roots.trans first.roots,covered := metadata.certificates.covered,parentTagPresent := metadata.lookup
    tagFresh := metadata.freshTag nextTag freshTag different
    protectorFresh := metadata.freshProtector nextTag freshProtector different
    nodeFits := nodeFits,slot := nextSlot,nonzero := first.nonzero,well := metadata.well,bounds := bounded
    clean := by rw [nextIndex];exact cleaned }
  exact ⟨second,nextIndex⟩

/-- An initial mutable slice and initial two-slot allocator data suffice for
both actual shared stages. The second stage's metadata is constructed, rather
than supplied as a post-state premise. -/
theorem two_append (tree : BorrowTree) (protections : ProtectedTags) (target : UniIndex)
    (exprTag nextTag : BorTag) (offset len : UInt64) (first : Data tree exprTag target offset len)
    (noFree : tree.tagMapping.deassigned.back? = none)
    (room : tree.tagMapping.mapping.size+1 ≤ 4294967295)
    (freshTag : GeneralBorrowTagMap.Fresh tree.tagMapping nextTag)
    (freshProtector : GeneralBorrowProtector.Fresh tree nextTag) (different : exprTag ≠ nextTag)
    (cleanFuture : Every (fun location : LocationTree => location.perms.get (future tree) = none) tree.locations)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned tree protections target .Write) offset (offset+len) tree.locations) :
    ∃ second : Data (child first protections false).tree nextTag (index first) offset len,
      index second = future tree ∧
      (read first protections false).status = .Completed ∧ (child first protections false).outcome = .ok () ∧
      (read second protections true).status = .Completed ∧ (child second protections true).outcome = .ok () ∧
      OwnedOn (GeneralBorrowFreshReleaseMixed.Combined (child second protections true).tree (registered protections nextTag true)
        (index second) (GeneralBorrowFreshSharedPrefix.labels (index first) (index second))) offset (offset+len)
        (child second protections true).tree.locations ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin (child second protections true).tree (index second) .Read offset (offset+len) := by
  let second := next tree protections target exprTag nextTag offset len first noFree room freshTag freshProtector different cleanFuture owned
  exact ⟨second.val,second.property,GeneralBorrowFreshSharedSequence.two tree protections target exprTag nextTag offset len first second.val owned⟩
end DuplicatePrefix.GeneralBorrowFreshSharedNext
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshSharedNext." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved shared next dependency {dependency}"
