import duplicate_prefix.GeneralBorrowExposeRead
namespace DuplicatePrefix.GeneralBorrowFrozenWriteExposure
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowNodeUpdate
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def dropRead (cache : ExposedCache) (index : UniIndex) : ExposedCache :=
  let old := (cache.nodes.get index).getD {}
  {cache with nodes := cache.nodes.insert index {old with localReads := old.localReads-1}}

/-- Exact real exposure-cache delta when an exposed Frozen leaf becomes
Disabled: its leaf and parent counters lose a Read witness; UInt16 arithmetic
is retained. This is not a claim that Write preserves the cache. -/
theorem two_nodes (cache : ExposedCache) (nodes : UniValMap TreeNode) (leaf root : UniIndex)
    (leafNode rootNode : TreeNode) (leafPresent : nodes.get leaf = some leafNode)
    (rootPresent : nodes.get root = some rootNode) (parent : leafNode.parent = some root)
    (parentless : rootNode.parent = none) :
    cache.updateExposure nodes leaf .Read .None =
      ⟨dropRead (dropRead cache leaf) root,.ok ()⟩ := by
  have nonempty : 0 < nodes.size := by
    have valid := lookup_valid nodes root rootNode rootPresent
    unfold UniValMap.size
    omega
  have notPast : ¬ 1 > nodes.size := by omega
  unfold ExposedCache.updateExposure
  simp only [Id.run,bind,pure,ForIn.forIn]
  name_range_scan
  have first : scan () (cache,some leaf,0,.ok (),true) =
      .yield (dropRead cache leaf,some root,1,.ok (),true) := by
    simp only [scan,show ¬0>nodes.size from by omega,↓reduceIte,leafPresent,parent,Option.isNone_some]
    rfl
  have second : scan () (dropRead cache leaf,some root,1,.ok (),true) =
      .yield (dropRead (dropRead cache leaf) root,none,2,.ok (),false) := by
    simp only [scan,notPast,↓reduceIte,rootPresent,parentless,Option.isNone_none]
    rfl
  have last : scan () (dropRead (dropRead cache leaf) root,none,2,.ok (),false) =
      .done (dropRead (dropRead cache leaf) root,none,2,.ok (),false) := by simp [scan]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [first,bind]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [second,bind]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [last,bind,pure]
  rfl

/-- Source permission transition paired with the cache delta above. The
unprotected Frozen visitor becomes Disabled on a foreign root Write. -/
theorem frozen_foreign_write :
    performAccessTransition .Write .ForeignAccess .Frozen false = .Transition ⟨.Frozen,.Disabled⟩ := rfl

theorem exposure_levels :
    Permission.strongestAllowedLocalAccess .Frozen false = .Read ∧
    Permission.strongestAllowedLocalAccess .Disabled false = .None := ⟨rfl,rfl⟩

end DuplicatePrefix.GeneralBorrowFrozenWriteExposure
