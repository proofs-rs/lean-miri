import duplicate_prefix.GeneralBorrowPhysicalReadableConcreteFrame
import duplicate_prefix.GeneralBorrowStructuralHistorySifaState
namespace DuplicatePrefix.GeneralBorrowProtectedGeneratedFramesNodes
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowStructuralHistoryConcreteAllocator
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
attribute [local irreducible] UniValMap.insert

theorem installed_old (tree : BorrowTree) (mapping : UniKeyMap BorTag) (index parent : UniIndex) (parentNode : TreeNode)
    (tag : BorTag) (outside : Permission) (sifa : IdempotentForeignAccess)
    (query : UniIndex) (old : TreeNode) (parentPresent : tree.nodeAt parent = some parentNode)
    (present : tree.nodeAt query = some old) (vacant : tree.nodes.get index = none) :
    ∃ next,(installed tree mapping index parent parentNode tag outside sifa).nodeAt query = some next ∧ next.tag = old.tag := by
  by_cases same : query = parent
  · subst query
    have equal : parentNode = old := Option.some.inj (parentPresent.symm.trans present)
    let updated : TreeNode := {parentNode with children := parentNode.children.push index}
    refine ⟨updated,?_,by dsimp only [updated];rw [←equal]⟩
    have found := GeneralBorrowFreshLocation.get_same (tree.nodes.insert index (node tag parent outside sifa)) parent updated
    simpa only [installed,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,BorrowTree.nodeAt,GeneralBorrowFreshNode.attachedNodes,updated] using found
  · have different : query ≠ index := by intro equal;rw [←equal] at vacant;rw [show tree.nodes.get query = some old from present] at vacant;cases vacant
    let updated : TreeNode := {parentNode with children := parentNode.children.push index}
    have found : ((tree.nodes.insert index (node tag parent outside sifa)).insert parent updated).get query = some old := by
      rw [GeneralBorrowFreshLocation.get_other (tree.nodes.insert index (node tag parent outside sifa)) parent query updated same,
        GeneralBorrowFreshLocation.get_other tree.nodes index query (node tag parent outside sifa) different]
      exact present
    exact ⟨old,by simpa only [installed,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,BorrowTree.nodeAt,GeneralBorrowFreshNode.attachedNodes,updated] using found,rfl⟩

theorem installed_new (tree : BorrowTree) (mapping : UniKeyMap BorTag) (index parent : UniIndex) (parentNode : TreeNode)
    (tag : BorTag) (outside : Permission) (sifa : IdempotentForeignAccess)
    (parentPresent : tree.nodeAt parent = some parentNode) (vacant : tree.nodes.get index = none) :
    (installed tree mapping index parent parentNode tag outside sifa).nodeAt index = some (node tag parent outside sifa) := by
  have different : index ≠ parent := by intro same;rw [same] at vacant;rw [show tree.nodes.get parent=some parentNode from parentPresent] at vacant;cases vacant
  have found : ((tree.nodes.insert index (node tag parent outside sifa)).insert parent {parentNode with children:=parentNode.children.push index}).get index = some (node tag parent outside sifa) := by
    rw [GeneralBorrowFreshLocation.get_other (tree.nodes.insert index (node tag parent outside sifa)) parent index _ different,
      GeneralBorrowFreshLocation.get_same]
  simpa only [installed,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,BorrowTree.nodeAt,GeneralBorrowFreshNode.attachedNodes] using found

/-- Actual mixed concrete construction retains every earlier node's sparse
index/tag and installs the actual counter-issued tag, including source inside
error prefixes and final SIFA. Freshness and slot vacancy come from the allocator. -/
theorem constructor (tree : BorrowTree) (initial : GeneralBorrowStructuralHistoryState.State tree)
    (parentTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (parentPresent : tree.nodeAt parent = some parentNode)
    (tag : BorTag) (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+1 ≤ 4294967295)
    (outside : Permission) (sifa : IdempotentForeignAccess) (held : Bool)
    (initialOutside : outside.isInitial = true) (notUnique : outside.isUnique = false)
    (foreign : outside.strongestIdempotentForeignAccess held = .Access sifa) (base : Size) (inside : DedupRangeMap LocationState) :
    let actual := (tree.newChild base (.concrete parentTag) tag inside outside held).tree
    (∀ query old,tree.nodeAt query = some old → ∃ next,actual.nodeAt query = some next ∧ next.tag = old.tag) ∧
    (∃ index next,actual.nodeAt index = some next ∧ next.tag = tag) ∧ actual.roots = tree.roots := by
  obtain ⟨mapping,index,inserted,parentLookup,graph,growth⟩ := GeneralBorrowStructuralHistoryConcreteAllocator.select tree initial parent parentNode parentPresent tag fresh room outside sifa
  have vacant := GeneralBorrowStructuralHistorySifaState.vacant_of_insert tree initial tag fresh room mapping index inserted
  have frame := GeneralBorrowPhysicalReadableConcreteFrame.frame tree parentTag parent parentNode tag mapping index inserted tagged outside sifa held parentLookup initialOutside notUnique foreign base inside
  refine ⟨?_,?_,frame.roots⟩
  · intro query old present
    obtain ⟨staged,found,tagged⟩ := installed_old tree mapping index parent parentNode tag outside sifa query old parentPresent present vacant
    obtain ⟨next,found,tag,_,_⟩ := GeneralBorrowStructuralHistoryGraphFrame.node_fields
      (installed tree mapping index parent parentNode tag outside sifa) (tree.newChild base (.concrete parentTag) tag inside outside held).tree frame query staged found
    exact ⟨next,found,tag.trans tagged⟩
  · have found := installed_new tree mapping index parent parentNode tag outside sifa parentPresent vacant
    obtain ⟨next,found,tagged,_,_⟩ := GeneralBorrowStructuralHistoryGraphFrame.node_fields
      (installed tree mapping index parent parentNode tag outside sifa) (tree.newChild base (.concrete parentTag) tag inside outside held).tree frame index (node tag parent outside sifa) found
    exact ⟨index,next,found,tagged⟩
end DuplicatePrefix.GeneralBorrowProtectedGeneratedFramesNodes
