import duplicate_prefix.GeneralBorrowConstructorSifaProfile
import duplicate_prefix.GeneralBorrowZeroSharedConstructor
import duplicate_prefix.GeneralBorrowZeroDefaultConstructor
import duplicate_prefix.GeneralBorrowZeroProtectedDefaultConstructor
namespace DuplicatePrefix.GeneralBorrowZeroConstructorSifaProfile
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowLocationSifaConsistency DuplicatePrefix.GeneralBorrowSifaPermissionConsistency
open DuplicatePrefix.GeneralBorrowFreshNode DuplicatePrefix.GeneralBorrowNodeUpdate DuplicatePrefix.GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] UniValMap.insert

namespace Shared
/-- Actual zero-length shared append preserves the generic permission/SIFA profile.
The constructor still attaches a real unexposed Frozen node and weakens SIFA;
no materialized inside states or bounds on the ignored offset are assumed. -/
theorem append (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.tagMapping.get parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (noFree : tree.tagMapping.deassigned.back? = none)
    (aligned : tree.tagMapping.mapping.size = tree.nodes.data.size) (fits : tree.tagMapping.mapping.size ≤ 4294967295)
    (offset : UInt64) (isProtected : Bool) (protections : ProtectedTags)
    (initial : Every (fun location => Profile tree location protections) tree.locations) :
    let operation := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes 0) GeneralBorrowFreshAnchor.sharedState) .Frozen isProtected
    operation.outcome = .ok () ∧ Every (fun location => Profile operation.tree location protections) operation.tree.locations := by
  dsimp only
  let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
  let stage := { (GeneralBorrowFreshGraph.attached tree index parent parentNode (GeneralBorrowFreshAnchor.sharedNode newTag parent)) with
    tagMapping := (⟨tree.tagMapping.mapping.push (newTag,index),tree.tagMapping.deassigned⟩ : UniKeyMap BorTag) }
  have atEnd : index.toNat = tree.nodes.data.size := by
    simp only [index,UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega : tree.tagMapping.mapping.size < 2^32)]
    exact aligned
  have vacant : tree.nodes.get index = none := by simp [UniValMap.get,atEnd]
  have newDefault : Consistent (GeneralBorrowFreshAnchor.sharedNode newTag parent).defaultLocationState (protections.contains newTag) :=
    GeneralBorrowSifaPermissionConsistency.frozen false _
  have stageGood : Every (fun location => Profile stage location protections) stage.locations := by
    intro position valid
    have formed := GeneralBorrowConstructorSifaProfile.attach tree _ protections index parent parentNode (GeneralBorrowFreshAnchor.sharedNode newTag parent)
      vacant present (initial position valid) newDefault
    exact ⟨formed.present,formed.vacant⟩
  have actual := GeneralBorrowZeroSharedConstructor.append tree depth parentTag newTag parent parentNode tagged present fresh noFree aligned fits offset isProtected
  refine ⟨actual.1,?_⟩
  rw [actual.2]
  exact GeneralBorrowSifaProfileTransport.sifa stage protections parent .Read stageGood

/-- Actual zero-length shared reuse preserves physical profiles and clean vacancies,
including the explicit initial Clean invariant at its vacant node index. -/
theorem reuse (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (parentTag newTag : BorTag) (parent index : UniIndex) (parentNode : TreeNode)
    (tagged : tree.tagMapping.get parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (available : tree.tagMapping.deassigned.back? = some index)
    (bounded : index.toNat < tree.nodes.data.size) (vacant : tree.nodes.get index = none)
    (slack : depth.depth parent < tree.nodes.size) (offset : UInt64) (isProtected : Bool) (protections : ProtectedTags)
    (initial : Every (fun location => Profile tree location protections) tree.locations) :
    let operation := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes 0) GeneralBorrowFreshAnchor.sharedState) .Frozen isProtected
    operation.outcome = .ok () ∧ Every (fun location => Profile operation.tree location protections) operation.tree.locations := by
  dsimp only
  let stage := { (GeneralBorrowFreshGraph.attached tree index parent parentNode (GeneralBorrowFreshAnchor.sharedNode newTag parent)) with
    tagMapping := (⟨tree.tagMapping.mapping.push (newTag,index),tree.tagMapping.deassigned.pop⟩ : UniKeyMap BorTag) }
  have newDefault : Consistent (GeneralBorrowFreshAnchor.sharedNode newTag parent).defaultLocationState (protections.contains newTag) :=
    GeneralBorrowSifaPermissionConsistency.frozen false _
  have stageGood : Every (fun location => Profile stage location protections) stage.locations := by
    intro position valid
    have formed := GeneralBorrowConstructorSifaProfile.attach tree _ protections index parent parentNode (GeneralBorrowFreshAnchor.sharedNode newTag parent)
      vacant present (initial position valid) newDefault
    exact ⟨formed.present,formed.vacant⟩
  have actual := GeneralBorrowZeroSharedConstructor.reuse tree depth parentTag newTag parent index parentNode tagged present fresh available bounded vacant slack offset isProtected
  refine ⟨actual.1,?_⟩
  rw [actual.2]
  exact GeneralBorrowSifaProfileTransport.sifa stage protections parent .Read stageGood

end Shared

namespace Default
/-- Actual zero-length Default append preserves the generic permission/SIFA profile.
The constructor still attaches a real unexposed reservation and weakens SIFA;
no materialized inside states or bounds on the ignored offset are assumed. -/
theorem append (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.tagMapping.get parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (noFree : tree.tagMapping.deassigned.back? = none)
    (aligned : tree.tagMapping.mapping.size = tree.nodes.data.size) (fits : tree.tagMapping.mapping.size ≤ 4294967295)
    (offset : UInt64) (protections : ProtectedTags)
    (alignedProtection : protections.contains newTag = false)
    (initial : Every (fun location => Profile tree location protections) tree.locations) :
    let operation := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes 0) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false
    operation.outcome = .ok () ∧ Every (fun location => Profile operation.tree location protections) operation.tree.locations := by
  dsimp only
  let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
  let stage := { (GeneralBorrowFreshGraph.attached tree index parent parentNode (GeneralBorrowFreshDefaultChild.child newTag parent)) with
    tagMapping := (⟨tree.tagMapping.mapping.push (newTag,index),tree.tagMapping.deassigned⟩ : UniKeyMap BorTag) }
  have atEnd : index.toNat = tree.nodes.data.size := by
    simp only [index,UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega : tree.tagMapping.mapping.size < 2^32)]
    exact aligned
  have vacant : tree.nodes.get index = none := by simp [UniValMap.get,atEnd]
  have newDefault : Consistent (GeneralBorrowFreshDefaultChild.child newTag parent).defaultLocationState (protections.contains newTag) := by
    rw [alignedProtection]
    exact GeneralBorrowSifaPermissionConsistency.unprotected_reservation false
  have stageGood : Every (fun location => Profile stage location protections) stage.locations := by
    intro position valid
    have formed := GeneralBorrowConstructorSifaProfile.attach tree _ protections index parent parentNode (GeneralBorrowFreshDefaultChild.child newTag parent)
      vacant present (initial position valid) newDefault
    exact ⟨formed.present,formed.vacant⟩
  have actual := GeneralBorrowZeroDefaultConstructor.append tree depth parentTag newTag parent parentNode tagged present fresh noFree aligned fits offset
  refine ⟨actual.1,?_⟩
  rw [actual.2]
  exact GeneralBorrowSifaProfileTransport.sifa stage protections parent .Read stageGood

/-- Actual zero-length Default reuse preserves physical profiles and clean vacancies,
including the explicit initial Clean invariant at its vacant node index. -/
theorem reuse (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (parentTag newTag : BorTag) (parent index : UniIndex) (parentNode : TreeNode)
    (tagged : tree.tagMapping.get parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (available : tree.tagMapping.deassigned.back? = some index)
    (bounded : index.toNat < tree.nodes.data.size) (vacant : tree.nodes.get index = none)
    (slack : depth.depth parent < tree.nodes.size) (offset : UInt64) (protections : ProtectedTags)
    (alignedProtection : protections.contains newTag = false)
    (initial : Every (fun location => Profile tree location protections) tree.locations) :
    let operation := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes 0) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false
    operation.outcome = .ok () ∧ Every (fun location => Profile operation.tree location protections) operation.tree.locations := by
  dsimp only
  let stage := { (GeneralBorrowFreshGraph.attached tree index parent parentNode (GeneralBorrowFreshDefaultChild.child newTag parent)) with
    tagMapping := (⟨tree.tagMapping.mapping.push (newTag,index),tree.tagMapping.deassigned.pop⟩ : UniKeyMap BorTag) }
  have newDefault : Consistent (GeneralBorrowFreshDefaultChild.child newTag parent).defaultLocationState (protections.contains newTag) := by
    rw [alignedProtection]
    exact GeneralBorrowSifaPermissionConsistency.unprotected_reservation false
  have stageGood : Every (fun location => Profile stage location protections) stage.locations := by
    intro position valid
    have formed := GeneralBorrowConstructorSifaProfile.attach tree _ protections index parent parentNode (GeneralBorrowFreshDefaultChild.child newTag parent)
      vacant present (initial position valid) newDefault
    exact ⟨formed.present,formed.vacant⟩
  have actual := GeneralBorrowZeroDefaultConstructor.reuse tree depth parentTag newTag parent index parentNode tagged present fresh available bounded vacant slack offset
  refine ⟨actual.1,?_⟩
  rw [actual.2]
  exact GeneralBorrowSifaProfileTransport.sifa stage protections parent .Read stageGood

end Default

namespace Protected
/-- Actual zero-length protected Default append preserves the generic permission/SIFA profile.
The constructor still attaches a real unexposed reservation and weakens SIFA;
no materialized inside states or bounds on the ignored offset are assumed. -/
theorem append (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.tagMapping.get parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (noFree : tree.tagMapping.deassigned.back? = none)
    (aligned : tree.tagMapping.mapping.size = tree.nodes.data.size) (fits : tree.tagMapping.mapping.size ≤ 4294967295)
    (offset : UInt64) (protections : ProtectedTags)
    (alignedProtection : protections.contains newTag = true)
    (initial : Every (fun location => Profile tree location protections) tree.locations) :
    let operation := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes 0) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    operation.outcome = .ok () ∧ Every (fun location => Profile operation.tree location protections) operation.tree.locations := by
  dsimp only
  let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
  let stage := { (GeneralBorrowFreshGraph.attached tree index parent parentNode (GeneralBorrowFreshChild.child newTag parent)) with
    tagMapping := (⟨tree.tagMapping.mapping.push (newTag,index),tree.tagMapping.deassigned⟩ : UniKeyMap BorTag) }
  have atEnd : index.toNat = tree.nodes.data.size := by
    simp only [index,UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega : tree.tagMapping.mapping.size < 2^32)]
    exact aligned
  have vacant : tree.nodes.get index = none := by simp [UniValMap.get,atEnd]
  have newDefault : Consistent (GeneralBorrowFreshChild.child newTag parent).defaultLocationState (protections.contains newTag) := by
    rw [alignedProtection]
    exact GeneralBorrowSifaPermissionConsistency.protected_reservation false
  have stageGood : Every (fun location => Profile stage location protections) stage.locations := by
    intro position valid
    have formed := GeneralBorrowConstructorSifaProfile.attach tree _ protections index parent parentNode (GeneralBorrowFreshChild.child newTag parent)
      vacant present (initial position valid) newDefault
    exact ⟨formed.present,formed.vacant⟩
  have actual := GeneralBorrowZeroProtectedDefaultConstructor.append tree depth parentTag newTag parent parentNode tagged present fresh noFree aligned fits offset
  refine ⟨actual.1,?_⟩
  rw [actual.2]
  exact GeneralBorrowSifaProfileTransport.sifa stage protections parent .None stageGood

/-- Actual zero-length protected Default reuse preserves physical profiles and clean vacancies,
including the explicit initial Clean invariant at its vacant node index. -/
theorem reuse (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (parentTag newTag : BorTag) (parent index : UniIndex) (parentNode : TreeNode)
    (tagged : tree.tagMapping.get parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (available : tree.tagMapping.deassigned.back? = some index)
    (bounded : index.toNat < tree.nodes.data.size) (vacant : tree.nodes.get index = none)
    (slack : depth.depth parent < tree.nodes.size) (offset : UInt64) (protections : ProtectedTags)
    (alignedProtection : protections.contains newTag = true)
    (initial : Every (fun location => Profile tree location protections) tree.locations) :
    let operation := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes 0) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    operation.outcome = .ok () ∧ Every (fun location => Profile operation.tree location protections) operation.tree.locations := by
  dsimp only
  let stage := { (GeneralBorrowFreshGraph.attached tree index parent parentNode (GeneralBorrowFreshChild.child newTag parent)) with
    tagMapping := (⟨tree.tagMapping.mapping.push (newTag,index),tree.tagMapping.deassigned.pop⟩ : UniKeyMap BorTag) }
  have newDefault : Consistent (GeneralBorrowFreshChild.child newTag parent).defaultLocationState (protections.contains newTag) := by
    rw [alignedProtection]
    exact GeneralBorrowSifaPermissionConsistency.protected_reservation false
  have stageGood : Every (fun location => Profile stage location protections) stage.locations := by
    intro position valid
    have formed := GeneralBorrowConstructorSifaProfile.attach tree _ protections index parent parentNode (GeneralBorrowFreshChild.child newTag parent)
      vacant present (initial position valid) newDefault
    exact ⟨formed.present,formed.vacant⟩
  have actual := GeneralBorrowZeroProtectedDefaultConstructor.reuse tree depth parentTag newTag parent index parentNode tagged present fresh available bounded vacant slack offset
  refine ⟨actual.1,?_⟩
  rw [actual.2]
  exact GeneralBorrowSifaProfileTransport.sifa stage protections parent .None stageGood

end Protected

end DuplicatePrefix.GeneralBorrowZeroConstructorSifaProfile
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowZeroConstructorSifaProfile.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved zero constructor physical profile dependency {dependency}"
