import duplicate_prefix.GeneralBorrowExposureChildAttach
import duplicate_prefix.GeneralBorrowPositiveWildcardConstructor
namespace DuplicatePrefix.GeneralBorrowWildcardRootCache
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality GeneralBorrowExposure
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

def rootDepth (nodes : UniValMap TreeNode) (depth : ParentDepth nodes) (index : UniIndex) (node : TreeNode)
    (vacant : nodes.get index = none) (parentless : node.parent = none)
    (size : nodes.size ≤ (nodes.insert index node).size) : ParentDepth (nodes.insert index node) where
  depth := fun query => if query = index then 0 else depth.depth query
  bounded := by
    intro query next found
    by_cases same : query = index
    · simp only [same,ite_true];omega
    · rw [GeneralBorrowFreshLocation.get_other nodes index query node same] at found
      simp only [same,ite_false]
      exact Nat.le_trans (depth.bounded query next found) size
  parent := by
    intro query next found earlier parent
    by_cases same : query = index
    · subst query
      rw [GeneralBorrowFreshLocation.get_same] at found
      cases found
      rw [parentless] at parent
      cases parent
    · rw [GeneralBorrowFreshLocation.get_other nodes index query node same] at found
      obtain ⟨old,present,rank⟩ := depth.parent query next found earlier parent
      have different : earlier ≠ index := by intro equal;rw [equal,vacant] at present;cases present
      refine ⟨old,?_,?_⟩
      · rw [GeneralBorrowFreshLocation.get_other nodes index earlier node different];exact present
      · simpa only [same,different,ite_false] using rank

/-- A new unexposed parentless root contributes no exposure, and old parent
walks retain all contributions. Slot cleanliness is not needed for counters. -/
theorem insert (tree : BorrowTree) (depth : ParentDepth tree.nodes) (index : UniIndex) (node : TreeNode)
    (vacant : tree.nodes.get index = none) (hidden : node.isExposed = false)
    (size : tree.nodes.size ≤ (tree.nodes.insert index node).size)
    (location : LocationTree) (protections : ProtectedTags) (initial : LocationCoherent tree location protections) :
    LocationCoherent {tree with nodes := tree.nodes.insert index node} location protections := by
  have oldFrame : ∀ query old,tree.nodes.get query = some old → ∃ next,(tree.nodes.insert index node).get query = some next ∧
      next.parent = old.parent ∧ next.isExposed = old.isExposed ∧
      effective location protections query next = effective location protections query old := by
    intro query old present
    have different : query ≠ index := by intro same;rw [same,vacant] at present;cases present
    exact ⟨old,(GeneralBorrowFreshLocation.get_other tree.nodes index query node different).trans present,rfl,rfl,rfl⟩
  have back : ∀ query next,(tree.nodes.insert index node).get query = some next → next.isExposed = true →
      ∃ old,tree.nodes.get query = some old := by
    intro query next present exposed
    by_cases same : query = index
    · subst query
      rw [GeneralBorrowFreshLocation.get_same] at present
      cases present
      rw [hidden] at exposed
      cases exposed
    · rw [GeneralBorrowFreshLocation.get_other tree.nodes index query node same] at present
      exact ⟨next,present⟩
  intro query kind
  rw [initial query kind]
  exact congrArg UInt16.ofNat (GeneralBorrowExposureGraphTransport.extension tree.nodes _ depth _ _ size oldFrame back query kind).symm

/-- Actual positive wildcard constructor cache closure. All graph and range
resources are initial metadata; new root depth and real materialization closure
are derived before any subsequent concrete access. -/
theorem constructor (tree : BorrowTree) (depth : ParentDepth tree.nodes) (mapping : UniKeyMap BorTag)
    (index : UniIndex) (tag : BorTag) (outside : Permission) (sifa : IdempotentForeignAccess)
    (state : LocationState) (offset len : UInt64)
    (vacant : tree.nodes.get index = none)
    (size : tree.nodes.size ≤ (tree.nodes.insert index (WildcardHitZeroConstructor.rootNode tag outside sifa)).size)
    (well : tree.locations.WellFormed) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (protections : ProtectedTags) (initial : GeneralRangeMapState.Every (fun location => LocationCoherent tree location protections) tree.locations) :
    let after := GeneralBorrowPositiveWildcardConstructor.result tree mapping index tag outside sifa state offset len
    GeneralRangeMapState.Every (fun location => LocationCoherent after location protections) after.locations := by
  let node := WildcardHitZeroConstructor.rootNode tag outside sifa
  let base := {tree with nodes := tree.nodes.insert index node}
  have coherentBase : GeneralRangeMapState.Every (fun location => LocationCoherent base location protections) tree.locations := by
    intro position valid
    exact insert tree depth index node vacant rfl size _ protections (initial position valid)
  have nextDepth := rootDepth tree.nodes depth index node vacant rfl size
  have present : base.nodeAt index = some node := GeneralBorrowFreshLocation.get_same tree.nodes index node
  exact GeneralBorrowExposureChildAttach.modify_every (fun location => LocationCoherent base location protections) tree.locations
    (Size.ofBytes offset) (Size.ofBytes len) (fun _ location => {location with perms := location.perms.insert index state}) well bounds coherentBase
    (fun _ location good => GeneralBorrowExposureChildAttach.materialize base nextDepth index node present rfl location protections state good)
end DuplicatePrefix.GeneralBorrowWildcardRootCache
