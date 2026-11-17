import duplicate_prefix.GeneralBorrowFreshMixedWithin
import duplicate_prefix.GeneralBorrowFreshMixedRead
import duplicate_prefix.GeneralBorrowFreshActiveOnRange
import duplicate_prefix.GeneralBorrowFreshReborrowStages
namespace DuplicatePrefix.GeneralBorrowFreshSharedWithinStages
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshAnchor DuplicatePrefix.GeneralBorrowFreshMixedChild
open DuplicatePrefix.GeneralBorrowFreshReleaseMixed DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralRangeMapState
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

private theorem combined_insert (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (tag : BorTag) (fresh : GeneralBorrowProtector.Fresh tree tag) (anchor : UniIndex) (writable : Nat → Bool)
    (owned : Combined tree protections anchor writable location) :
    Combined tree (protections.insert tag .StrongProtector) anchor writable location := by
  unfold Combined GeneralBorrowRange.LocationOwned Mixed
  rw [GeneralBorrowProtector.normal_projection tree location protections tag .StrongProtector fresh]
  exact owned

/-- A complete real shared reborrow stage: optional fresh protector insertion,
actual parent Read and actual append/reuse Frozen constructor. The input clean
slot is preserved through the Read before installation, so the returned child's
active states remain confined to this slice. All operation successes are derived. -/
theorem borrow (tree : BorrowTree) (protections : ProtectedTags) (isProtected : Bool)
    (parentTag newTag : BorTag) (parent root : UniIndex) (parentNode : TreeNode)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (parentPresent : tree.nodeAt parent = some parentNode) (roots : tree.roots = #[root])
    (covered : GeneralBorrowGraph.RootsCover tree) (parentTagPresent : tree.indexOfTag parentTag = some parent)
    (tagFresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (protectorFresh : GeneralBorrowProtector.Fresh tree newTag)
    (nodeFits : tree.nodes.data.size ≤ 4294967296) (slot : Slot tree depth parent)
    (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) (writable : Nat → Bool)
    (owned : OwnedOn (Combined tree protections parent writable) offset (offset+len) tree.locations)
    (clean : Every (fun location : LocationTree => location.perms.get (slot_index slot) = none) tree.locations) :
    let registered := if isProtected then protections.insert newTag .StrongProtector else protections
    let read := tree.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len)
      .Read registered .VisitChildrenOfAccessed
    let child := read.tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) sharedState) .Frozen isProtected
    read.status = .Completed ∧ child.outcome = .ok () ∧
      OwnedOn (Combined child.tree registered (slot_index slot) (extend writable (slot_index slot).toNat))
        offset (offset+len) child.tree.locations ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin child.tree (slot_index slot) .Read offset (offset+len) := by
  let registered := if isProtected then protections.insert newTag .StrongProtector else protections
  let index := slot_index slot
  let read := tree.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read registered .VisitChildrenOfAccessed
  have registeredOwners : OwnedOn (Combined tree registered parent writable) offset (offset+len) tree.locations := by
    cases isProtected with
    | false => exact owned
    | true =>
      intro position valid positive start stop
      exact combined_insert tree _ protections newTag protectorFresh parent writable (owned position valid positive start stop)
  have readOwners : OwnedOn (GeneralBorrowRange.LocationOwned tree registered parent .Read) offset (offset+len) tree.locations := by
    intro position valid positive start stop
    exact (registeredOwners position valid positive start stop).1
  have good := GeneralBorrowFreshMixedRead.access tree registered parentTag parent root (Size.ofBytes offset) (Size.ofBytes len)
    writable .VisitChildrenOfAccessed nodeFits depth children parentNode parentPresent roots covered parentTagPresent well
    offset (offset+len) registeredOwners bounds (Nat.le_refl _) (Nat.le_refl _)
  change read.status = .Completed ∧ OwnedOn (Combined read.tree registered parent writable) offset (offset+len) read.tree.locations ∧
    read.tree.locations.WellFormed ∧ read.tree.locations.size = tree.locations.size at good
  have cleanResult := GeneralBorrowFreshActiveOnRange.ranged tree registered parentTag parent root index (Size.ofBytes offset) (Size.ofBytes len)
    .Read .Read .VisitChildrenOfAccessed (fun _ => rfl) depth children parentNode parentPresent roots covered parentTagPresent
    (slot_vacant tree depth parent slot) clean well offset (offset+len) readOwners bounds (Nat.le_refl _) (Nat.le_refl _)
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
    have constructed := GeneralBorrowFreshMixedWithin.append read.tree readDepth parentTag newTag parent parentNode parentTagAfter parentAfter
      freshAfter noFreeAfter alignedAfter fitsIndex isProtected offset len nonzero good.2.2.1 boundsAfter registered writable good.2.1 cleanCtor
    simpa only [sameIndex,index] using constructed
  | reuse candidate available bounded vacant slack =>
    have availableAfter : read.tree.tagMapping.deassigned.back? = some candidate := by rw [tags];exact available
    have boundedAfter : candidate.toNat < read.tree.nodes.data.size := by rw [nodes];exact bounded
    have vacantAfter : read.tree.nodes.get candidate = none := by rw [nodes];exact vacant
    have slackAfter : readDepth.depth parent < read.tree.nodes.size := by
      change depth.depth parent < read.tree.nodes.size
      rw [nodes]
      exact slack
    have constructed := GeneralBorrowFreshMixedWithin.reuse read.tree readDepth parentTag newTag parent parentNode parentTagAfter parentAfter
      freshAfter candidate availableAfter boundedAfter vacantAfter slackAfter fitsAfter isProtected offset len nonzero good.2.2.1 boundsAfter
      registered writable good.2.1 cleanAfter
    simpa only [index,slot_index] using constructed
end DuplicatePrefix.GeneralBorrowFreshSharedWithinStages
#print axioms DuplicatePrefix.GeneralBorrowFreshSharedWithinStages.borrow

open Lean Elab Command in
run_cmd do
  for (name, _) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowFreshSharedWithinStages.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "{name} depends on unapproved axiom {dependency}"
