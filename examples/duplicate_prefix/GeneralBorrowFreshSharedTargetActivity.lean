import duplicate_prefix.GeneralBorrowFreshStageMetadata
import duplicate_prefix.GeneralBorrowFreshSharedTargetWithin
namespace DuplicatePrefix.GeneralBorrowFreshSharedTargetActivity
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralBorrowFreshReleaseMixed
open DuplicatePrefix.GeneralBorrowFreshSharedSequence DuplicatePrefix.GeneralBorrowFreshReadFrame
set_option maxRecDepth 65536
set_option maxHeartbeats 400000

/-- Preserve any older anchor's strong Write activity through the actual
parent Read and shared constructor. Permissions may carry arbitrary mixed
Write/Read strength; no post-state activity or success is assumed. -/
theorem preserves_target (tree : BorrowTree) (newTag : BorTag) (parent : UniIndex) (offset len : UInt64)
    (data : Data tree newTag parent offset len) (protections : ProtectedTags) (isProtected : Bool) (writable : Nat → Bool)
    (owned : OwnedOn (Combined tree protections parent writable) offset (offset+len) tree.locations)
    (target : UniIndex) (lower upper : UInt64)
    (requestLower : lower.toNat ≤ offset.toNat) (requestUpper : (offset+len).toNat ≤ upper.toNat)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree target .Write lower upper) :
    GeneralBorrowFreshActiveWithin.ActiveWithin (child data protections isProtected).tree target .Write lower upper := by
  let accessed := read data protections isProtected
  have owners := GeneralBorrowFreshStageMetadata.registered_owned tree newTag parent offset len data protections isProtected writable owned
  have good := GeneralBorrowFreshMixedRead.access tree (registered protections newTag isProtected) data.parentTag parent data.root
    (Size.ofBytes offset) (Size.ofBytes len) writable .VisitChildrenOfAccessed data.nodeFits data.depth data.children data.parentNode
    data.parentPresent data.roots data.covered data.parentTagPresent data.well offset (offset+len) owners data.bounds
    (Nat.le_refl _) (Nat.le_refl _)
  change accessed.status = .Completed ∧ OwnedOn (Combined accessed.tree (registered protections newTag isProtected) parent writable)
    offset (offset+len) accessed.tree.locations ∧ accessed.tree.locations.WellFormed ∧ accessed.tree.locations.size = tree.locations.size at good
  have readActive : GeneralBorrowFreshActiveWithin.ActiveWithin accessed.tree target .Write lower upper :=
    GeneralBorrowFreshActiveWithinAccess.normal tree data.parentTag (Size.ofBytes offset) (Size.ofBytes len) .Read
      (registered protections newTag isProtected) .VisitChildrenOfAccessed target lower upper data.well data.bounds requestLower requestUpper active
  have framed := GeneralBorrowFreshReadFrame.frame tree (.concrete data.parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read (registered protections newTag isProtected) .VisitChildrenOfAccessed
  change accessed.tree = {tree with locations := accessed.tree.locations} at framed
  have nodeEq := congrArg BorrowTree.nodes framed
  have nodes : accessed.tree.nodes = tree.nodes := nodeEq
  have mappingEq := congrArg BorrowTree.tagMapping framed
  have mapping : accessed.tree.tagMapping = tree.tagMapping := mappingEq
  have rootsEq := congrArg BorrowTree.roots framed
  have roots : accessed.tree.roots = tree.roots := rootsEq
  let depth := depth_on tree accessed.tree nodes data.depth
  have children : GeneralBorrowGraph.ChildNodes accessed.tree := by rw [framed];exact data.children
  have covered : GeneralBorrowGraph.RootsCover accessed.tree := by rw [framed];exact data.covered
  have parentPresent : accessed.tree.nodeAt parent = some data.parentNode := by change accessed.tree.nodes.get parent = _;rw [nodes];exact data.parentPresent
  have tagPresent : accessed.tree.tagMapping.get data.parentTag = some parent := by rw [mapping];exact data.parentTagPresent
  have fresh : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping newTag := by rw [mapping];exact data.tagFresh
  have bounds : offset.toNat+len.toNat ≤ accessed.tree.locations.size.bytes.toNat := by rw [good.2.2.2];exact data.bounds
  cases data.slot with
  | append noFree aligned fits =>
    have noFreeAfter : accessed.tree.tagMapping.deassigned.back? = none := by rw [mapping];exact noFree
    have alignedAfter : accessed.tree.tagMapping.mapping.size = accessed.tree.nodes.data.size := by rw [mapping,nodes];exact aligned
    have fitsAfter : accessed.tree.tagMapping.mapping.size ≤ 4294967295 := by rw [mapping];exact fits
    exact GeneralBorrowFreshSharedTargetWithin.append accessed.tree data.parentTag newTag parent data.parentNode tagPresent parentPresent
      fresh noFreeAfter alignedAfter fitsAfter isProtected offset len data.nonzero good.2.2.1 bounds target lower upper requestLower requestUpper readActive
  | reuse candidate available bounded vacant slack =>
    have availableAfter : accessed.tree.tagMapping.deassigned.back? = some candidate := by rw [mapping];exact available
    have boundedAfter : candidate.toNat < accessed.tree.nodes.data.size := by rw [nodes];exact bounded
    have vacantAfter : accessed.tree.nodes.get candidate = none := by rw [nodes];exact vacant
    exact GeneralBorrowFreshSharedTargetWithin.reuse accessed.tree data.parentTag newTag parent data.parentNode tagPresent parentPresent
      fresh candidate availableAfter boundedAfter vacantAfter isProtected offset len data.nonzero good.2.2.1 bounds target lower upper requestLower requestUpper readActive
end DuplicatePrefix.GeneralBorrowFreshSharedTargetActivity
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshSharedTargetActivity." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved shared target activity dependency {dependency}"
