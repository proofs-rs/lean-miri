import duplicate_prefix.GeneralBorrowStructuralHistoryMutable
import duplicate_prefix.GeneralBorrowStructuralHistoryWildcardAllocator
namespace DuplicatePrefix.GeneralBorrowStructuralHistoryConcreteAllocator
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowStructuralHistoryState GeneralBorrowExposure GeneralBorrowGraph GeneralBorrowFreshReborrowStages
open GeneralBorrowGcAllocator GeneralBorrowFreshStagePool GeneralBorrowFreshAllocatorInvariant GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 300000
noncomputable section

def node (tag : BorTag) (parent : UniIndex) (outside : Permission) (sifa : IdempotentForeignAccess) : TreeNode :=
  ⟨tag,some parent,#[],outside,sifa,false,none⟩
def installed (tree : BorrowTree) (mapping : UniKeyMap BorTag) (index parent : UniIndex)
    (parentNode : TreeNode) (tag : BorTag) (outside : Permission) (sifa : IdempotentForeignAccess) : BorrowTree :=
  GeneralBorrowFreshMetadataChildAttach.staged tree index parent parentNode (node tag parent outside sifa) mapping tree.locations

private theorem roots (tree : BorrowTree) (initial : GraphState tree) (mapping : UniKeyMap BorTag)
    (index parent : UniIndex) (parentNode : TreeNode) (tag : BorTag) (outside : Permission) (sifa : IdempotentForeignAccess)
    (present : tree.nodeAt parent=some parentNode)
    (parentLookup : (GeneralBorrowFreshGraph.attached tree index parent parentNode (node tag parent outside sifa)).nodeAt parent=
      some (GeneralBorrowFreshGraph.updatedParent parentNode index))
    (otherLookup : ∀query old,tree.nodeAt query=some old→query≠parent→
      (GeneralBorrowFreshGraph.attached tree index parent parentNode (node tag parent outside sifa)).nodeAt query=some old) :
    ∀root∈(installed tree mapping index parent parentNode tag outside sifa).roots.toList,
      ∃next,(installed tree mapping index parent parentNode tag outside sifa).nodes.get root=some next ∧ next.parent=none := by
  intro root member
  change root∈tree.roots.toList at member
  obtain ⟨old,found,parentless⟩ := initial.rootNodes root member
  by_cases same : root=parent
  · subst root
    have equal : old=parentNode := Option.some.inj (found.symm.trans present)
    subst old
    have found' : (installed tree mapping index parent parentNode tag outside sifa).nodes.get parent =
        some (GeneralBorrowFreshGraph.updatedParent parentNode index) := by
      simpa only [installed,GeneralBorrowFreshMetadataChildAttach.staged,BorrowTree.nodeAt] using parentLookup
    exact ⟨GeneralBorrowFreshGraph.updatedParent parentNode index,found',parentless⟩
  · have found' : (installed tree mapping index parent parentNode tag outside sifa).nodes.get root=some old := by
      simpa only [installed,GeneralBorrowFreshMetadataChildAttach.staged,BorrowTree.nodeAt] using otherLookup root old found same
    exact ⟨old,found',parentless⟩

/-- Generic outside defaults/SIFA are irrelevant to structural allocation.
Original State internally selects the real append/back-free allocator branch,
forms reciprocal parent/child edges and derives the new coherent GraphState. -/
theorem select (tree : BorrowTree) (initial : State tree) (parent : UniIndex) (parentNode : TreeNode)
    (present : tree.nodeAt parent=some parentNode) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+1≤4294967295)
    (outside : Permission) (sifa : IdempotentForeignAccess) :
    ∃mapping index,tree.tagMapping.insert tag=.Inserted mapping index ∧
      (tree.nodes.insert index (node tag parent outside sifa)).get parent=some parentNode ∧
      GraphState (installed tree mapping index parent parentNode tag outside sifa) ∧
      (installed tree mapping index parent parentNode tag outside sifa).nodes.size≤tree.nodes.size+1 := by
  let rank := GeneralBorrowStructuralHistoryMutable.depth tree initial
  let selected := GeneralBorrowStructuralHistoryMutable.slot tree initial parent parentNode present room
  let newNode := node tag parent outside sifa
  cases selected with
  | append noFree aligned fits =>
    let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
    let mapping : UniKeyMap BorTag := ⟨tree.tagMapping.mapping.push (tag,index),tree.tagMapping.deassigned⟩
    let after := installed tree mapping index parent parentNode tag outside sifa
    have atEnd : index.toNat=tree.nodes.data.size := by
      change (UInt32.ofNat tree.tagMapping.mapping.size).toNat=_
      rw [UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega)]
      exact aligned
    have notParent := GeneralBorrowFreshNode.parent_not_fresh tree.nodes index parent parentNode atEnd present
    have parentLookup := (GeneralBorrowFreshNode.append_get_other tree.nodes index parent newNode atEnd notParent).trans present
    have cert := GeneralBorrowFreshMetadataChildAttach.append tree rank initial.children initial.covered index parent parentNode newNode
      atEnd present rfl rfl mapping tree.locations after rfl
    have metadata := GeneralBorrowFreshMetadataChildAttach.allocator tree index parent parentNode newNode atEnd present mapping tree.locations after rfl
    have capacity : after.nodes.size=tree.nodes.size+1 := metadata.2.2
    have clear := Array.back?_eq_none_iff.mp noFree
    have pool : Pool after.nodes after.tagMapping.deassigned := by
      change Pool after.nodes tree.tagMapping.deassigned
      rw [clear]
      exact ⟨by simp,by simp,by simp⟩
    have accounting : Accounting after := by
      unfold Accounting
      change (tree.tagMapping.mapping.push (tag,index)).size + tree.tagMapping.deassigned.size = after.nodes.size
      rw [Array.size_push,clear,Array.size_empty,Nat.add_zero,capacity,aligned]
      rfl
    have allocator : Invariant after := ⟨pool,accounting,
      fresh_push_unique tree.tagMapping tag index tree.tagMapping.deassigned initial.allocator.unique fresh,
      GeneralBorrowSharedAllocatorInvariant.staged_tags tree index parent parentNode newNode tag rfl tree.tagMapping.deassigned tree.locations present fresh initial.allocator.nodeTags⟩
    refine ⟨mapping,index,GeneralBorrowTagMap.insert_append tree.tagMapping tag fresh noFree fits,parentLookup,
      ⟨?_,⟨cert.depth⟩,cert.children,cert.covered,?_,allocator,by rw[capacity];omega⟩,Nat.le_of_eq capacity⟩
    · intro location protections
      obtain ⟨forest⟩ := initial.forest location protections
      exact ⟨GeneralBorrowFreshProjection.projected_forest tree index parent parentNode newNode atEnd present rfl rfl location location protections forest⟩
    · exact roots tree initial.toGraphState mapping index parent parentNode tag outside sifa present
        (GeneralBorrowFreshGraph.parent_lookup tree index parent parentNode newNode atEnd present)
        (fun query old found different => (GeneralBorrowFreshGraph.other_lookup tree index parent query parentNode newNode atEnd present different
          (by intro same;have bound:=GeneralBorrowNodeUpdate.lookup_valid tree.nodes query old found;rw[same,atEnd] at bound;omega)).trans found)
  | reuse index available bounded vacant slack =>
    let mapping : UniKeyMap BorTag := ⟨tree.tagMapping.mapping.push (tag,index),tree.tagMapping.deassigned.pop⟩
    let after := installed tree mapping index parent parentNode tag outside sifa
    have notParent := GeneralBorrowFreshReuseNode.parent_not_vacant tree.nodes index parent parentNode vacant present
    have parentLookup := (GeneralBorrowFreshLocation.get_other tree.nodes index parent newNode notParent).trans present
    have cert := GeneralBorrowFreshMetadataChildReuseAttach.reuse tree rank initial.children initial.covered index parent parentNode newNode
      bounded vacant present rfl rfl slack mapping tree.locations after rfl
    have metadata := GeneralBorrowFreshMetadataChildReuseAttach.allocator tree index parent parentNode newNode bounded vacant present mapping tree.locations after rfl
    have capacity : after.nodes.size=tree.nodes.size := metadata.2.2
    have pool : Pool after.nodes after.tagMapping.deassigned := by
      simpa only [after,installed,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached] using
        GeneralBorrowFreshAllocatorInvariant.attached tree.nodes tree.tagMapping.deassigned initial.allocator.pool index parent available parentNode newNode present
    have nonempty : 0<tree.tagMapping.deassigned.size := by
      obtain ⟨rest,eq⟩ := Array.back?_eq_some_iff.mp available
      rw[eq,Array.size_push];omega
    have accounting : Accounting after := by
      unfold Accounting
      change (tree.tagMapping.mapping.push (tag,index)).size+tree.tagMapping.deassigned.pop.size=after.nodes.size
      rw[Array.size_push,Array.size_pop,capacity]
      have old:=initial.allocator.accounting
      unfold Accounting at old
      omega
    have allocator : Invariant after := ⟨pool,accounting,
      fresh_push_unique tree.tagMapping tag index tree.tagMapping.deassigned.pop initial.allocator.unique fresh,
      GeneralBorrowSharedAllocatorInvariant.staged_tags tree index parent parentNode newNode tag rfl tree.tagMapping.deassigned.pop tree.locations present fresh initial.allocator.nodeTags⟩
    refine ⟨mapping,index,GeneralBorrowTagMap.insert_free tree.tagMapping tag fresh index available,parentLookup,
      ⟨?_,⟨cert.depth⟩,cert.children,cert.covered,?_,allocator,by rw[capacity];exact initial.fits⟩,by rw[capacity];omega⟩
    · intro location protections
      obtain ⟨forest⟩ := initial.forest location protections
      exact ⟨GeneralBorrowFreshReuseProjection.projected_forest tree index parent parentNode newNode bounded vacant present rfl rfl location location protections forest⟩
    · exact roots tree initial.toGraphState mapping index parent parentNode tag outside sifa present
        (GeneralBorrowFreshMetadataChildReuseGraph.parent_lookup tree index parent parentNode newNode vacant present)
        (fun query old found different => (GeneralBorrowFreshMetadataChildReuseGraph.other_lookup tree index parent query parentNode newNode vacant present different
          (by intro same;change tree.nodes.get query=some old at found;rw[same,vacant] at found;cases found)).trans found)
end
end DuplicatePrefix.GeneralBorrowStructuralHistoryConcreteAllocator
