import duplicate_prefix.GeneralBorrowExposureChildAttach
import duplicate_prefix.GeneralBorrowExposureSifaTransport
import duplicate_prefix.GeneralBorrowZeroDefaultConstructor
namespace DuplicatePrefix.GeneralBorrowZeroDefaultExposureCache
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposureCardinality DuplicatePrefix.GeneralBorrowFreshNode
open DuplicatePrefix.GeneralBorrowNodeUpdate DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralBorrowFreshDefaultChild (child inside)
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] UniValMap.insert

/-- Actual zero-length Default append preserves the generic cache invariant.
The constructor still attaches a real unexposed reservation and weakens SIFA;
no materialized inside states or bounds on the ignored offset are assumed. -/
theorem append (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.tagMapping.get parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (noFree : tree.tagMapping.deassigned.back? = none)
    (aligned : tree.tagMapping.mapping.size = tree.nodes.data.size) (fits : tree.tagMapping.mapping.size ≤ 4294967295)
    (offset : UInt64) (protections : ProtectedTags)
    (initial : Every (fun location => LocationCoherent tree location protections) tree.locations) :
    let operation := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes 0) inside) (.ReservedFrz false) false
    operation.outcome = .ok () ∧ Every (fun location => LocationCoherent operation.tree location protections) operation.tree.locations := by
  dsimp only
  let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
  let stage := { (GeneralBorrowFreshGraph.attached tree index parent parentNode (child newTag parent)) with
    tagMapping := (⟨tree.tagMapping.mapping.push (newTag,index),tree.tagMapping.deassigned⟩ : UniKeyMap BorTag) }
  have atEnd : index.toNat = tree.nodes.data.size := by
    simp only [index,UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega : tree.tagMapping.mapping.size < 2^32)]
    exact aligned
  have vacant : tree.nodes.get index = none := by simp [UniValMap.get,atEnd]
  have different := parent_not_fresh tree.nodes index parent parentNode atEnd present
  have parentAfter : (tree.nodes.insert index (child newTag parent)).get parent = some parentNode :=
    (GeneralBorrowFreshLocation.get_other _ index parent _ different).trans present
  have size : tree.nodes.size ≤ (attachedNodes tree.nodes index parent parentNode (child newTag parent)).size := by
    unfold attachedNodes
    rw [insert_existing_size _ parent parentNode _ parentAfter,append_size _ index _ atEnd]
    omega
  let certificate := attached_depth tree.nodes depth index parent parentNode (child newTag parent) atEnd present rfl
  have stageGood : Every (fun location => LocationCoherent stage location protections) stage.locations := by
    intro position valid
    exact GeneralBorrowExposureChildAttach.attach tree depth index parent parentNode (child newTag parent)
      vacant present rfl size _ protections (initial position valid)
  have actual := GeneralBorrowZeroDefaultConstructor.append tree depth parentTag newTag parent parentNode tagged present fresh noFree aligned fits offset
  refine ⟨actual.1,?_⟩
  rw [actual.2]
  exact GeneralBorrowExposureSifaTransport.sifa stage protections certificate parent .Read stageGood

/-- Actual zero-length Default reuse preserves generic per-range coherence,
including arbitrary stale permissions at its initially vacant node index. -/
theorem reuse (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (parentTag newTag : BorTag) (parent index : UniIndex) (parentNode : TreeNode)
    (tagged : tree.tagMapping.get parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (available : tree.tagMapping.deassigned.back? = some index)
    (bounded : index.toNat < tree.nodes.data.size) (vacant : tree.nodes.get index = none)
    (slack : depth.depth parent < tree.nodes.size) (offset : UInt64) (protections : ProtectedTags)
    (initial : Every (fun location => LocationCoherent tree location protections) tree.locations) :
    let operation := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes 0) inside) (.ReservedFrz false) false
    operation.outcome = .ok () ∧ Every (fun location => LocationCoherent operation.tree location protections) operation.tree.locations := by
  dsimp only
  let stage := { (GeneralBorrowFreshGraph.attached tree index parent parentNode (child newTag parent)) with
    tagMapping := (⟨tree.tagMapping.mapping.push (newTag,index),tree.tagMapping.deassigned.pop⟩ : UniKeyMap BorTag) }
  have different := GeneralBorrowFreshReuseNode.parent_not_vacant tree.nodes index parent parentNode vacant present
  have parentAfter : (tree.nodes.insert index (child newTag parent)).get parent = some parentNode :=
    (GeneralBorrowFreshLocation.get_other _ index parent _ different).trans present
  have size : tree.nodes.size ≤ (attachedNodes tree.nodes index parent parentNode (child newTag parent)).size := by
    unfold attachedNodes
    rw [insert_existing_size _ parent parentNode _ parentAfter,GeneralBorrowFreshReuseNode.bounded_size _ index _ bounded]
    exact Nat.le_refl _
  let certificate := GeneralBorrowFreshReuseNode.attached_depth tree.nodes depth index parent parentNode
    (child newTag parent) bounded vacant present rfl slack
  have stageGood : Every (fun location => LocationCoherent stage location protections) stage.locations := by
    intro position valid
    exact GeneralBorrowExposureChildAttach.attach tree depth index parent parentNode (child newTag parent)
      vacant present rfl size _ protections (initial position valid)
  have actual := GeneralBorrowZeroDefaultConstructor.reuse tree depth parentTag newTag parent index parentNode tagged present fresh available bounded vacant slack offset
  refine ⟨actual.1,?_⟩
  rw [actual.2]
  exact GeneralBorrowExposureSifaTransport.sifa stage protections certificate parent .Read stageGood

end DuplicatePrefix.GeneralBorrowZeroDefaultExposureCache
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowZeroDefaultExposureCache.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved zero Default cache dependency {dependency}"
