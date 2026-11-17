import duplicate_prefix.GeneralBorrowFreshSharedWithinStages
import duplicate_prefix.GeneralBorrowFreshSharedPrefix
namespace DuplicatePrefix.GeneralBorrowFreshSharedSequence
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralBorrowFreshReleaseMixed
open DuplicatePrefix.GeneralBorrowFreshMixedChild DuplicatePrefix.GeneralBorrowFreshReborrowStages
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

set_option autoImplicit false in
/-- Caller metadata for one real shared reborrow. The owned slice is supplied
separately, so the second stage consumes the first stage's proved mixed result. -/
structure Data (tree : BorrowTree) (newTag : BorTag) (parent : UniIndex) (offset len : UInt64) where
  parentTag : BorTag
  root : UniIndex
  parentNode : TreeNode
  depth : GeneralBorrowExposure.ParentDepth tree.nodes
  children : GeneralBorrowGraph.ChildNodes tree
  parentPresent : tree.nodeAt parent = some parentNode
  roots : tree.roots = #[root]
  covered : GeneralBorrowGraph.RootsCover tree
  parentTagPresent : tree.indexOfTag parentTag = some parent
  tagFresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag
  protectorFresh : GeneralBorrowProtector.Fresh tree newTag
  nodeFits : tree.nodes.data.size ≤ 4294967296
  slot : Slot tree depth parent
  nonzero : len ≠ 0
  well : tree.locations.WellFormed
  bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat
  clean : Every (fun location : LocationTree => location.perms.get (GeneralBorrowFreshSharedWithinStages.slot_index slot) = none) tree.locations

def index {tree : BorrowTree} {newTag : BorTag} {parent : UniIndex} {offset len : UInt64}
    (data : Data tree newTag parent offset len) : UniIndex := GeneralBorrowFreshSharedWithinStages.slot_index data.slot

def registered (protections : ProtectedTags) (newTag : BorTag) (isProtected : Bool) : ProtectedTags :=
  if isProtected then protections.insert newTag .StrongProtector else protections

def read {tree : BorrowTree} {newTag : BorTag} {parent : UniIndex} {offset len : UInt64}
    (data : Data tree newTag parent offset len) (protections : ProtectedTags) (isProtected : Bool) :=
  tree.performBorrowAccessRange (.concrete data.parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read (registered protections newTag isProtected) .VisitChildrenOfAccessed

def child {tree : BorrowTree} {newTag : BorTag} {parent : UniIndex} {offset len : UInt64}
    (data : Data tree newTag parent offset len) (protections : ProtectedTags) (isProtected : Bool) :=
  (read data protections isProtected).tree.newChild (Size.ofBytes offset) (.concrete data.parentTag) newTag
    (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen isProtected

theorem run (tree : BorrowTree) (newTag : BorTag) (parent : UniIndex) (offset len : UInt64)
    (data : Data tree newTag parent offset len) (protections : ProtectedTags) (isProtected : Bool)
    (writable : Nat → Bool)
    (owned : OwnedOn (Combined tree protections parent writable) offset (offset+len) tree.locations) :
    (read data protections isProtected).status = .Completed ∧ (child data protections isProtected).outcome = .ok () ∧
      OwnedOn (Combined (child data protections isProtected).tree (registered protections newTag isProtected)
        (index data) (extend writable (index data).toNat)) offset (offset+len) (child data protections isProtected).tree.locations ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin (child data protections isProtected).tree (index data) .Read offset (offset+len) := by
  exact GeneralBorrowFreshSharedWithinStages.borrow tree protections isProtected data.parentTag newTag parent data.root data.parentNode
    data.depth data.children data.parentPresent data.roots data.covered data.parentTagPresent data.tagFresh data.protectorFresh
    data.nodeFits data.slot offset len data.nonzero data.well data.bounds writable owned data.clean

/-- Two actual shared constructions retain the initial mutable permissions as
mixed labels. Only the two fresh Frozen slots become read-only; both Reads and
both constructors complete without success premises. The second data record
contains structural/allocator facts only, never ownership of its result. -/
theorem two (tree : BorrowTree) (protections : ProtectedTags) (target : UniIndex)
    (exprTag childTag : BorTag) (offset len : UInt64)
    (first : Data tree exprTag target offset len)
    (second : Data (child first protections false).tree childTag (index first) offset len)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned tree protections target .Write) offset (offset+len) tree.locations) :
    (read first protections false).status = .Completed ∧ (child first protections false).outcome = .ok () ∧
    (read second protections true).status = .Completed ∧ (child second protections true).outcome = .ok () ∧
    OwnedOn (Combined (child second protections true).tree (registered protections childTag true) (index second)
      (GeneralBorrowFreshSharedPrefix.labels (index first) (index second))) offset (offset+len)
      (child second protections true).tree.locations ∧
    GeneralBorrowFreshActiveWithin.ActiveWithin (child second protections true).tree (index second) .Read offset (offset+len) := by
  have initial : OwnedOn (Combined tree protections target (fun _ => true)) offset (offset+len) tree.locations := by
    intro position valid positive lower upper
    exact write_combined tree _ protections target (owned position valid positive lower upper)
  have one := run tree exprTag target offset len first protections false (fun _ => true) initial
  have firstOwned : OwnedOn (Combined (child first protections false).tree protections (index first)
      (extend (fun _ => true) (index first).toNat)) offset (offset+len) (child first protections false).tree.locations := one.2.2.1
  have next := run (child first protections false).tree childTag (index first) offset len second protections true
    (extend (fun _ => true) (index first).toNat) firstOwned
  exact ⟨one.1,one.2.1,next.1,next.2.1,next.2.2.1,next.2.2.2⟩
end DuplicatePrefix.GeneralBorrowFreshSharedSequence
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshSharedSequence." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved shared sequence dependency {dependency}"
