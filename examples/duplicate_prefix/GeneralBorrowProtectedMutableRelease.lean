import duplicate_prefix.GeneralBorrowRootChildWriteOwnership
import duplicate_prefix.GeneralBorrowFreshSharedReleaseWithin
import duplicate_prefix.GeneralBorrowFreshActiveWithinAccess

namespace DuplicatePrefix.GeneralBorrowProtectedMutableRelease
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralRangeMapOrigins
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Actual source registration in both the global table and owning frame. -/
def registration (global : GlobalState) (allocation : AllocId) (tag : BorTag) :=
  global.addProtector {} allocation tag .StrongProtector

/-- The matching real endCall removes the single frame-owned strong protector. -/
theorem end_call_empty (global : GlobalState) (empty : global.protectedTags = {}) (allocation : AllocId) (tag : BorTag) :
    ((registration global allocation tag).1.endCall (registration global allocation tag).2).protectedTags = {} := by
  simp [registration,GlobalState.addProtector,FrameState.addProtector,GlobalState.endCall,empty,
    ProtectedTags.insert,ProtectedTags.remove]

def write (tree : BorrowTree) (tag : BorTag) (offset len : UInt64) (protections : ProtectedTags) :=
  tree.performNormalAccessRange tag (Size.ofBytes offset) (Size.ofBytes len) .Write protections .VisitChildrenOfAccessed

def release (tree : BorrowTree) (tag : BorTag) (offset len : UInt64) (protections : ProtectedTags) :=
  (write tree tag offset len protections).tree.releaseProtector tag protections

/-- A protected child's actual Write and actual protector-end access both
complete before the real frame endCall. Only after that table weakening is root
Write ownership recovered. Premises are graph/permission/activity data, not
successful operations; no active-protector root contract is assumed. -/
theorem write_release_restore (tree : BorrowTree) (global : GlobalState) (empty : global.protectedTags = {})
    (allocation : AllocId) (tag : BorTag) (child root : UniIndex) (childNode rootNode : TreeNode)
    (childPresent : tree.nodeAt child = some childNode) (rootPresent : tree.nodeAt root = some rootNode)
    (parent : childNode.parent = some root) (rootless : rootNode.parent = none) (unexposed : childNode.isExposed = false)
    (lookup : tree.indexOfTag tag = some child) (depth : ParentDepth tree.nodes)
    (children : GeneralBorrowGraph.ChildNodes tree) (covered : GeneralBorrowGraph.RootsCover tree)
    (roots : tree.roots = #[root]) (fits : tree.nodes.data.size ≤ 4294967296)
    (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree child .Write offset (offset+len))
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned tree (registration global allocation tag).1.protectedTags child .Write)
      offset (offset+len) tree.locations) :
    let protections := (registration global allocation tag).1.protectedTags
    (write tree tag offset len protections).status = .Completed ∧
    (release tree tag offset len protections).status = .Released ∧
    ((registration global allocation tag).1.endCall (registration global allocation tag).2).protectedTags = {} ∧
    OwnedOn (GeneralBorrowRange.LocationOwned (release tree tag offset len protections).tree {} root .Write)
      offset (offset+len) (release tree tag offset len protections).tree.locations ∧
    (release tree tag offset len protections).tree.locations.WellFormed ∧
    (release tree tag offset len protections).tree.locations.size = tree.locations.size := by
  dsimp only
  let protections := (registration global allocation tag).1.protectedTags
  let accessed := write tree tag offset len protections
  have wrote := GeneralBorrowRangeLocal.access tree protections tag child root (Size.ofBytes offset) (Size.ofBytes len)
    .Write .Write .VisitChildrenOfAccessed (by intro impossible;cases impossible) fits depth children childNode childPresent roots covered lookup
    well offset (offset+len) owned bounds (Nat.le_refl _) (Nat.le_refl _)
  have activeAfter := GeneralBorrowFreshActiveWithinAccess.normal tree tag (Size.ofBytes offset) (Size.ofBytes len)
    .Write protections .VisitChildrenOfAccessed child offset (offset+len) well bounds (Nat.le_refl _) (Nat.le_refl _) active
  have frame := GeneralBorrowFreshReadFrame.frame tree (.concrete tag) (Size.ofBytes offset) (Size.ofBytes len) .Write protections .VisitChildrenOfAccessed
  have nodes : accessed.tree.nodes = tree.nodes := by
    simpa only [accessed,write,BorrowTree.performNormalAccessRange] using congrArg BorrowTree.nodes frame
  have mapping : accessed.tree.tagMapping = tree.tagMapping := by
    simpa only [accessed,write,BorrowTree.performNormalAccessRange] using congrArg BorrowTree.tagMapping frame
  have rootsEq : accessed.tree.roots = tree.roots := by
    simpa only [accessed,write,BorrowTree.performNormalAccessRange] using congrArg BorrowTree.roots frame
  let nextDepth := GeneralBorrowFreshReadFrame.depth_on tree accessed.tree nodes depth
  have nextChildren : GeneralBorrowGraph.ChildNodes accessed.tree := by
    intro index node present next member
    change accessed.tree.nodes.get index = some node at present
    rw [nodes] at present
    change ∃ node, accessed.tree.nodes.get next = some node
    rw [nodes]
    exact children index node present next member
  have nextCovered : GeneralBorrowGraph.RootsCover accessed.tree := by
    rw [show accessed.tree = {tree with locations := accessed.tree.locations} from frame]
    exact covered
  have childAfter : accessed.tree.nodeAt child = some childNode := by change accessed.tree.nodes.get child = some childNode;rw [nodes];exact childPresent
  have rootAfter : accessed.tree.nodeAt root = some rootNode := by change accessed.tree.nodes.get root = some rootNode;rw [nodes];exact rootPresent
  have lookupAfter : accessed.tree.indexOfTag tag = some child := by change accessed.tree.tagMapping.get tag = some child;rw [mapping];exact lookup
  have fitAfter : accessed.tree.nodes.data.size ≤ 4294967296 := by rw [nodes];exact fits
  have sum : (offset+len).toNat = offset.toNat+len.toNat := by
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt (by
      change offset.toNat+len.toNat < 18446744073709551616
      have limit : tree.locations.size.bytes.toNat < 18446744073709551616 := UInt64.toNat_lt_size tree.locations.size.bytes
      omega)]
  have positive : offset.toNat < (offset+len).toNat := by
    have lenPositive : 0 < len.toNat := by
      have nz : len.toNat ≠ 0 := fun h => nonzero (UInt64.toNat_inj.mp (by simpa using h))
      omega
    rw [sum];omega
  have released := GeneralBorrowFreshSharedReleaseWithin.release accessed.tree protections tag child root .Write offset (offset+len)
    positive fitAfter nextDepth nextChildren childNode childAfter unexposed (rootsEq.trans roots) nextCovered lookupAfter activeAfter
    child wrote.2.2.1 activeAfter wrote.2.1
  have weakened := GeneralBorrowFreshProtectorRelease.end_call_owned_on (accessed.tree.releaseProtector tag protections).tree
    (registration global allocation tag).1 (registration global allocation tag).2 child .Write offset (offset+len) released.2.2.1
  rw [end_call_empty global empty allocation tag] at weakened
  have releasedNodes : (accessed.tree.releaseProtector tag protections).tree.nodes = accessed.tree.nodes :=
    by simpa only using congrArg BorrowTree.nodes released.2.1
  have rootFinal : (accessed.tree.releaseProtector tag protections).tree.nodeAt root = some rootNode := by
    change (accessed.tree.releaseProtector tag protections).tree.nodes.get root = some rootNode
    rw [releasedNodes];exact rootAfter
  have childFinal : (accessed.tree.releaseProtector tag protections).tree.nodeAt child = some childNode := by
    change (accessed.tree.releaseProtector tag protections).tree.nodes.get child = some childNode
    rw [releasedNodes];exact childAfter
  refine ⟨wrote.1,released.1,end_call_empty global empty allocation tag,?_,released.2.2.2.2.1,released.2.2.2.2.2.trans wrote.2.2.2⟩
  intro position valid positive lower upper
  have childOwned := weakened position valid positive lower upper
  refine ⟨childOwned.1,?_⟩
  exact GeneralBorrowRootChildWriteOwnership.root_of_child _ _ root child rootNode childNode rootFinal rootless childFinal parent childOwned.2

end DuplicatePrefix.GeneralBorrowProtectedMutableRelease
