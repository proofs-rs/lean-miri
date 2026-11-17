import duplicate_prefix.GeneralBorrowParentTagConstructors
namespace DuplicatePrefix.GeneralBorrowParentTagRootFrames
open Miri Miri.Memory Miri.ABI Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowWildcardParentTagOrder GeneralBorrowExposure
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
/-- Initial physical allocation trees satisfy order: their only node is a
parentless root. No high-water or permission hypothesis is needed. -/
theorem new_root (tag : BorTag) (size : Size) : ParentTagOrder (BorrowTree.new tag size) := by
  intro child node present parent parentNode edge parentPresent
  have only : ∀ query value, (BorrowTree.new tag size).nodes.get query = some value → value.parent = none := by
    intro query value found
    by_cases zero : query.toNat = 0
    · have equal : query = (⟨0⟩ : UniIndex) := by
        cases query with
        | mk index => exact congrArg UniIndex.mk (UInt32.toNat_inj.mp zero)
      subst query
      rw [BorrowTree.new_root_node] at found
      cases found
      rfl
    · have absent : (BorrowTree.new tag size).nodes.get query = none := by
        unfold UniValMap.get
        rw [Array.getElem?_eq_none (by change 1 ≤ query.toNat; omega)]
      rw [absent] at found
      cases found
  rw [only child node present] at edge
  cases edge

/-- Actual zero-length wildcard root creation also preserves order. No
successful allocation/constructor hypothesis is a caller premise. -/
theorem wildcard_zero (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (order : ParentTagOrder tree)
    (room : tree.nodes.size+1 ≤ 4294967295)
    (outside : Permission) (sifa : IdempotentForeignAccess) (inside : LocationState) (held : Bool)
    (initial : outside.isInitial=true) (nonunique : outside.isUnique=false)
    (foreign : outside.strongestIdempotentForeignAccess held=.Access sifa) (offset : UInt64) :
    ParentTagOrder (tree.newChild (Size.ofBytes offset) .wildcard global.nextPointerTag
      (DedupRangeMap.new Size.ZERO inside) outside held).tree := by
  have fresh := GeneralBorrowParentTagInvariant.fresh tree global runtime
  obtain ⟨mapping,index,inserted,_,vacant,_⟩ := GeneralBorrowWildcardConstructorSlot.select tree global runtime global.nextPointerTag fresh room outside sifa
  rw [WildcardHitZeroConstructor.exact tree global.nextPointerTag index mapping inserted outside sifa held initial nonunique foreign inside offset]
  exact GeneralBorrowParentTagConstructors.installed_root tree
    (GeneralBorrowStructuralHistoryShared.depth tree runtime.formed.toState) order mapping index vacant global.nextPointerTag outside sifa

/-- Exposure changes the actual stored flag and cache counters, while graph
order transfers through the checked exact topology frame. -/
theorem expose (tree : BorrowTree) (order : ParentTagOrder tree) (tag : BorTag) (index : UniIndex) (node : TreeNode)
    (tagged : tree.indexOfTag tag = some index) (present : tree.nodeAt index = some node)
    (depth : ParentDepth tree.nodes) (unexposed : node.isExposed = false) (protections : ProtectedTags) :
    ParentTagOrder (tree.exposeTag protections tag).tree :=
  GeneralBorrowFreshParentTagOrder.transfer tree _
    (GeneralBorrowRootExposureFrame.expose tree tag index node tagged present depth unexposed protections).2.1 order
end DuplicatePrefix.GeneralBorrowParentTagRootFrames
