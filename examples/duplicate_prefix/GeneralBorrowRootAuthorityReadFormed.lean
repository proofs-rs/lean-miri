import duplicate_prefix.GeneralBorrowRootAuthorityReadRange
namespace DuplicatePrefix.GeneralBorrowRootAuthorityReadFormed
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open GeneralBorrowStructuralHistoryRootAuthorityState GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- An arbitrary mapped descendant Read preserves latent root authority and
physical readability on its real ranged result, including sparse GC holes. -/
theorem ranged (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag) (anchor root : UniIndex)
    (offset len : Size) (mode : ChildrenVisitMode)
    (initial : Formed tree root) (roots : tree.roots = #[root])
    (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (tagPresent : tree.indexOfTag tag = some anchor)
    (readable : Every (fun location => GeneralBorrowPhysicalReadable.Profile tree location protections) tree.locations)
    (bounds : offset.bytes.toNat+len.bytes.toNat ≤ tree.locations.size.bytes.toNat) :
    let result := tree.performNormalAccessRange tag offset len .Read protections mode
    result.status = .Completed ∧ Formed result.tree root ∧
      Every (fun location => GeneralBorrowPhysicalReadable.Profile result.tree location protections) result.tree.locations ∧
      result.tree.locations.WellFormed ∧ result.tree.locations.size = tree.locations.size ∧
      result.tree.nodes = tree.nodes ∧ result.tree.roots = tree.roots ∧ result.tree.tagMapping = tree.tagMapping := by
  obtain ⟨rootNode,rootPresent,parentless⟩ := initial.rootNodes root initial.member
  obtain ⟨depth⟩ := initial.depth
  have combined : Every (fun location => GeneralBorrowPhysicalReadable.Profile tree location protections ∧
      GeneralBorrowStructuralHistoryRootAuthorityAt.At tree location root) tree.locations := by
    intro position valid
    exact ⟨readable position valid,initial.policy position valid⟩
  have good := GeneralBorrowRootAuthorityReadRange.ranged tree protections tag anchor root offset len mode initial.fits depth
    initial.children anchorNode rootNode anchorPresent rootPresent roots initial.covered tagPresent initial.well
    (fun location => Classical.choice (initial.forest location protections)) combined bounds
  let result := tree.performNormalAccessRange tag offset len .Read protections mode
  have frame : result.tree = {tree with locations := result.tree.locations} :=
    GeneralBorrowFreshReadFrame.frame tree (.concrete tag) offset len .Read protections mode
  have graph := GeneralBorrowStructuralHistoryState.graph_locations tree result.tree.locations initial.toGraphState
  rw [←frame] at graph
  refine ⟨good.1,⟨⟨graph,good.2.2.1⟩,?_,?_⟩,?_,good.2.2⟩
  · rw [good.2.2.2.2.2.1]
    exact initial.member
  · intro position valid
    exact (good.2.1 position valid).2
  · intro position valid
    exact (good.2.1 position valid).1
end DuplicatePrefix.GeneralBorrowRootAuthorityReadFormed
