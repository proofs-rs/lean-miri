import duplicate_prefix.GeneralBorrowFreshMutableWithin
import duplicate_prefix.GeneralBorrowFreshActiveOnRange
import duplicate_prefix.GeneralBorrowFreshReborrowStages
namespace DuplicatePrefix.GeneralBorrowFreshMutableStages
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralBorrowFreshReborrowStages DuplicatePrefix.GeneralBorrowFreshReadFrame
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

def slot_index {tree : BorrowTree} {depth : GeneralBorrowExposure.ParentDepth tree.nodes} {parent : UniIndex} : Slot tree depth parent → UniIndex
  | .append .. => ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
  | .reuse index .. => index

theorem slot_vacant (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (parent : UniIndex)
    (slot : Slot tree depth parent) : tree.nodes.get (slot_index slot) = none := by
  cases slot with
  | append noFree aligned fits =>
    have indexAtEnd : (⟨UInt32.ofNat tree.tagMapping.mapping.size⟩ : UniIndex).toNat = tree.nodes.data.size := by
      simp only [UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega : tree.tagMapping.mapping.size < 2^32)]
      exact aligned
    unfold UniValMap.get
    simp only [slot_index,indexAtEnd,Array.getElem?_eq_none (by omega : tree.nodes.data.size ≤ tree.nodes.data.size)]
  | reuse index available bounded vacant slack => exact vacant

set_option autoImplicit false in
/-- A complete protected mutable reborrow: fresh protector insertion, actual
parent Read and actual append/reuse ReservedFrz constructor. The input clean
slot is preserved through the Read before installation, so the returned child's
active states remain confined to this slice. All operation successes are derived. -/
theorem borrow (tree : BorrowTree) (protections : ProtectedTags)
    (parentTag newTag : BorTag) (parent root : UniIndex) (parentNode : TreeNode)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (parentPresent : tree.nodeAt parent = some parentNode) (roots : tree.roots = #[root])
    (covered : GeneralBorrowGraph.RootsCover tree) (parentTagPresent : tree.indexOfTag parentTag = some parent)
    (tagFresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (protectorFresh : GeneralBorrowProtector.Fresh tree newTag)
    (nodeFits : tree.nodes.data.size ≤ 4294967296) (slot : Slot tree depth parent)
    (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned tree protections parent .Write) offset (offset+len) tree.locations)
    (clean : Every (fun location : LocationTree => location.perms.get (slot_index slot) = none) tree.locations) :
    let registered := protections.insert newTag .StrongProtector
    let read := tree.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len)
      .Read registered .VisitChildrenOfAccessed
    let child := read.tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    read.status = .Completed ∧ child.outcome = .ok () ∧
      OwnedOn (GeneralBorrowRange.LocationOwned child.tree registered (slot_index slot) .Write)
        offset (offset+len) child.tree.locations ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin child.tree (slot_index slot) .Write offset (offset+len) := by
  let registered := protections.insert newTag .StrongProtector
  let index := slot_index slot
  let read := tree.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read registered .VisitChildrenOfAccessed
  have registeredOwners := protector_owned_on tree protections newTag .StrongProtector protectorFresh parent .Write
    offset (offset+len) owned
  have good := GeneralBorrowRangeLocal.access tree registered parentTag parent root (Size.ofBytes offset) (Size.ofBytes len)
    .Read .Write .VisitChildrenOfAccessed (fun _ => rfl) nodeFits depth children parentNode parentPresent roots covered parentTagPresent well
    offset (offset+len) registeredOwners bounds (Nat.le_refl _) (Nat.le_refl _)
  change read.status = .Completed ∧ OwnedOn (GeneralBorrowRange.LocationOwned read.tree registered parent .Write) offset (offset+len) read.tree.locations ∧
    read.tree.locations.WellFormed ∧ read.tree.locations.size = tree.locations.size at good
  have cleanResult := GeneralBorrowFreshActiveOnRange.ranged tree registered parentTag parent root index (Size.ofBytes offset) (Size.ofBytes len)
    .Read .Write .VisitChildrenOfAccessed (fun _ => rfl) depth children parentNode parentPresent roots covered parentTagPresent
    (slot_vacant tree depth parent slot) clean well offset (offset+len) registeredOwners bounds (Nat.le_refl _) (Nat.le_refl _)
  have cleanAfter : Every (fun location : LocationTree => location.perms.get index = none) read.tree.locations := cleanResult.2
  have framed := GeneralBorrowFreshReadFrame.frame tree (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read registered .VisitChildrenOfAccessed
  have nodeEq := congrArg BorrowTree.nodes framed
  have nodes : read.tree.nodes = tree.nodes := nodeEq
  have tagEq := congrArg BorrowTree.tagMapping framed
  have tags : read.tree.tagMapping = tree.tagMapping := tagEq
  let readDepth := depth_on tree read.tree nodes depth
  have parentAfter : read.tree.nodeAt parent = some parentNode := by
    change read.tree.nodes.get parent = some parentNode
    rw [nodes]
    exact parentPresent
  have parentTagAfter : read.tree.tagMapping.get parentTag = some parent := by rw [tags];exact parentTagPresent
  have freshAfter : GeneralBorrowTagMap.Fresh read.tree.tagMapping newTag := by rw [tags];exact tagFresh
  have boundsAfter : offset.toNat+len.toNat ≤ read.tree.locations.size.bytes.toNat := by rw [good.2.2.2];exact bounds
  have fitsAfter : read.tree.nodes.data.size ≤ 4294967296 := by rw [nodes];exact nodeFits
  dsimp only
  refine ⟨good.1,?_⟩
  cases slot with
  | append noFree aligned fits =>
    have noFreeAfter : read.tree.tagMapping.deassigned.back? = none := by rw [tags];exact noFree
    have alignedAfter : read.tree.tagMapping.mapping.size = read.tree.nodes.data.size := by rw [tags,nodes];exact aligned
    have fitsIndex : read.tree.tagMapping.mapping.size ≤ 4294967295 := by rw [tags];exact fits
    have sameIndex : (⟨UInt32.ofNat read.tree.tagMapping.mapping.size⟩ : UniIndex) = index := by
      dsimp only [index,slot_index]
      rw [tags]
    have cleanCtor : Every (fun location : LocationTree => location.perms.get ⟨UInt32.ofNat read.tree.tagMapping.mapping.size⟩ = none) read.tree.locations := by
      rw [sameIndex]
      exact cleanAfter
    have constructed := GeneralBorrowFreshMutableWithin.append read.tree readDepth parentTag newTag parent parentNode parentTagAfter parentAfter
      freshAfter noFreeAfter alignedAfter fitsIndex offset len nonzero good.2.2.1 boundsAfter registered good.2.1 cleanCtor
    simpa only [sameIndex,index] using constructed
  | reuse candidate available bounded vacant slack =>
    have availableAfter : read.tree.tagMapping.deassigned.back? = some candidate := by rw [tags];exact available
    have boundedAfter : candidate.toNat < read.tree.nodes.data.size := by rw [nodes];exact bounded
    have vacantAfter : read.tree.nodes.get candidate = none := by rw [nodes];exact vacant
    have slackAfter : readDepth.depth parent < read.tree.nodes.size := by
      change depth.depth parent < read.tree.nodes.size
      rw [nodes]
      exact slack
    have constructed := GeneralBorrowFreshMutableWithin.reuse read.tree readDepth parentTag newTag parent parentNode parentTagAfter parentAfter
      freshAfter candidate availableAfter boundedAfter vacantAfter slackAfter fitsAfter offset len nonzero good.2.2.1 boundsAfter
      registered good.2.1 cleanAfter
    simpa only [index,slot_index] using constructed
end DuplicatePrefix.GeneralBorrowFreshMutableStages
#print axioms DuplicatePrefix.GeneralBorrowFreshMutableStages.borrow

open Lean Elab Command in
run_cmd do
  for (name, _) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowFreshMutableStages.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "{name} depends on unapproved axiom {dependency}"
