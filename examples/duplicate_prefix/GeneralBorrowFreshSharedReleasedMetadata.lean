import duplicate_prefix.GeneralBorrowFreshSharedStageLookup
import duplicate_prefix.GeneralBorrowFreshSharedNext
namespace DuplicatePrefix.GeneralBorrowFreshSharedReleasedMetadata
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralBorrowFreshSharedSequence DuplicatePrefix.GeneralBorrowFreshMixedChild
open DuplicatePrefix.GeneralBorrowFreshReleaseMixed
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

set_option autoImplicit false in
/-- Graph, allocator and old-parent facts needed by the following default
mutable expression. These facts contain no operation-success hypothesis. -/
structure Output (before after : BorrowTree) (target : UniIndex) (oldNode : TreeNode) (oldTag : BorTag) where
  certificates : GeneralBorrowFreshMetadataChildAttach.Certificates after
  roots : after.roots = before.roots
  noFree : after.tagMapping.deassigned.back? = none
  aligned : after.tagMapping.mapping.size = after.nodes.data.size
  mappingSize : after.tagMapping.mapping.size = before.tagMapping.mapping.size+2
  nodeSize : after.nodes.data.size = before.nodes.data.size+2
  nodeFits : after.nodes.data.size ≤ 4294967296
  node : ∃ node, after.nodeAt target = some node ∧ node.tag = oldNode.tag ∧ node.isExposed = oldNode.isExposed
  tagPresent : after.indexOfTag oldTag = some target

private theorem mapping_two (before middle after : Nat) (first : middle = before+1) (second : after = middle+1) :
    after = before+2 := by omega
private theorem nodes_two (beforeMap beforeNodes afterMap afterNodes : Nat)
    (oldAligned : beforeMap = beforeNodes) (aligned : afterMap = afterNodes) (size : afterMap = beforeMap+2) :
    afterNodes = beforeNodes+2 := by omega

private theorem one_fits (old final nodes : Nat) (aligned : final = nodes)
    (push : final = old+1) (fits : old ≤ 4294967295) : nodes ≤ 4294967296 := by omega

private theorem finish_second (before middle : BorrowTree) (protections : ProtectedTags) (target expr : UniIndex)
    (oldNode middleNode : TreeNode) (oldTag nextTag : BorTag) (offset len : UInt64)
    (second : Data middle nextTag expr offset len) (noFree : middle.tagMapping.deassigned.back? = none)
    (owned : OwnedOn (Combined middle protections expr (extend (fun _ => true) expr.toNat)) offset (offset+len) middle.locations)
    (rootsMiddle : middle.roots = before.roots)
    (mappingMiddle : middle.tagMapping.mapping.size = before.tagMapping.mapping.size+1)
    (alignedBefore : before.tagMapping.mapping.size = before.nodes.data.size)
    (present : middle.nodeAt target = some middleNode) (tag : middleNode.tag = oldNode.tag)
    (exposure : middleNode.isExposed = oldNode.isExposed) (oldPresent : middle.indexOfTag oldTag = some target)
    (different : nextTag ≠ oldTag) :
    Nonempty (Output before (child second protections true).tree target oldNode oldTag) := by
  have built := GeneralBorrowFreshStageMetadata.build middle nextTag expr offset len second protections true
    (extend (fun _ => true) expr.toNat) owned
  obtain ⟨metadata⟩ : Nonempty (GeneralBorrowFreshStageMetadata.Output middle nextTag expr offset len second protections true) := ⟨built⟩
  have allocator := metadata.allocator noFree
  have fitsBefore : middle.tagMapping.mapping.size ≤ 4294967295 := by
    cases second.slot with
    | append _ _ fits => exact fits
    | reuse candidate available bounded vacant slack => rw [noFree] at available;cases available
  have nodeFits := one_fits _ _ _ allocator.2.1 allocator.2.2 fitsBefore
  have mapSize := mapping_two _ _ _ mappingMiddle allocator.2.2
  have nodeSize := nodes_two _ _ _ _ alignedBefore allocator.2.1 mapSize
  obtain ⟨node,lookup,sameTag,sameExposure⟩ := GeneralBorrowFreshSharedStagePaths.old_node middle nextTag expr offset len second protections true
    (extend (fun _ => true) expr.toNat) owned target middleNode present
  have oldLookup := GeneralBorrowFreshSharedStageLookup.old_lookup middle nextTag expr offset len second protections true
    (extend (fun _ => true) expr.toNat) owned oldTag different
  exact ⟨⟨metadata.certificates,metadata.roots.trans rootsMiddle,allocator.1,allocator.2.1,mapSize,nodeSize,nodeFits,
    ⟨node,lookup,sameTag.trans tag,sameExposure.trans exposure⟩,oldLookup.trans oldPresent⟩⟩

/-- Initial data form both shared stages' complete graph/allocator and old-node
metadata. The second Data is the exact constructor used by the runtime proof. -/
theorem stages (tree : BorrowTree) (protections : ProtectedTags) (target : UniIndex)
    (exprTag nextTag : BorTag) (offset len : UInt64) (first : Data tree exprTag target offset len)
    (noFree : tree.tagMapping.deassigned.back? = none) (room : tree.tagMapping.mapping.size+1 ≤ 4294967295)
    (freshTag : GeneralBorrowTagMap.Fresh tree.tagMapping nextTag)
    (freshProtector : GeneralBorrowProtector.Fresh tree nextTag) (different : exprTag ≠ nextTag)
    (cleanFuture : Every (fun location : LocationTree => location.perms.get (GeneralBorrowFreshSharedNext.future tree) = none) tree.locations)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned tree protections target .Write) offset (offset+len) tree.locations) :
    let choice := GeneralBorrowFreshSharedNext.next tree protections target exprTag nextTag offset len first noFree room
      freshTag freshProtector different cleanFuture owned
    Nonempty (Output tree (child choice.val protections true).tree target first.parentNode first.parentTag) := by
  generalize nextEq : GeneralBorrowFreshSharedNext.next tree protections target exprTag nextTag offset len first noFree room
    freshTag freshProtector different cleanFuture owned = choice
  rcases choice with ⟨second,nextIndex⟩
  dsimp only at ⊢
  have initial : OwnedOn (Combined tree protections target (fun _ => true)) offset (offset+len) tree.locations := by
    intro position valid positive lower upper
    exact write_combined tree _ protections target (owned position valid positive lower upper)
  have one := GeneralBorrowFreshSharedSequence.run tree exprTag target offset len first protections false (fun _ => true) initial
  have firstOwned := one.2.2.1
  have regFalse : registered protections exprTag false = protections := by simp only [registered,Bool.false_eq_true,↓reduceIte]
  rw [regFalse] at firstOwned
  have built := GeneralBorrowFreshStageMetadata.build tree exprTag target offset len first protections false (fun _ => true) initial
  obtain ⟨metadata⟩ : Nonempty (GeneralBorrowFreshStageMetadata.Output tree exprTag target offset len first protections false) := ⟨built⟩
  have allocator := metadata.allocator noFree
  have alignedBefore : tree.tagMapping.mapping.size = tree.nodes.data.size := by
    cases first.slot with
    | append _ aligned _ => exact aligned
    | reuse candidate available bounded vacant slack => rw [noFree] at available;cases available
  obtain ⟨middleNode,present,tag,exposure⟩ := GeneralBorrowFreshSharedStagePaths.old_node tree exprTag target offset len first protections false
    (fun _ => true) initial target first.parentNode first.parentPresent
  have differentFirst := GeneralBorrowFreshSharedStageLookup.fresh_not_present tree exprTag first.parentTag target first.tagFresh first.parentTagPresent
  have differentSecond := GeneralBorrowFreshSharedStageLookup.fresh_not_present tree nextTag first.parentTag target freshTag first.parentTagPresent
  have firstLookup := GeneralBorrowFreshSharedStageLookup.old_lookup tree exprTag target offset len first protections false
    (fun _ => true) initial first.parentTag differentFirst
  exact finish_second tree (child first protections false).tree protections target (index first) first.parentNode middleNode first.parentTag nextTag offset len
    second allocator.1 firstOwned metadata.roots allocator.2.2 alignedBefore present tag exposure (firstLookup.trans first.parentTagPresent) differentSecond

/-- A release-frame equation transports all structural and allocator facts.
The location state is unrestricted here: cleanliness/ownership use their own
actual-release proofs, so this bridge does not assume them. -/
theorem of_frame (initial before after : BorrowTree) (target : UniIndex) (oldNode : TreeNode) (oldTag : BorTag)
    (metadata : Output initial before target oldNode oldTag)
    (frame : after = {before with locations := after.locations}) :
    Nonempty (Output initial after target oldNode oldTag) := by
  have nodeEq := congrArg BorrowTree.nodes frame
  have nodes : after.nodes = before.nodes := nodeEq
  have mapEq := congrArg BorrowTree.tagMapping frame
  have mapping : after.tagMapping = before.tagMapping := mapEq
  have rootsEq := congrArg BorrowTree.roots frame
  have roots : after.roots = before.roots := rootsEq
  let depth := GeneralBorrowFreshReadFrame.depth_on before after nodes metadata.certificates.depth
  have children : GeneralBorrowGraph.ChildNodes after := by rw [frame];exact metadata.certificates.children
  have covered : GeneralBorrowGraph.RootsCover after := by rw [frame];exact metadata.certificates.covered
  obtain ⟨node,present,tag,exposure⟩ := metadata.node
  have presentAfter : after.nodeAt target = some node := by change after.nodes.get target = _;rw [nodes];exact present
  refine ⟨⟨⟨depth,children,covered⟩,roots.trans metadata.roots,?_,?_,?_,?_,?_,⟨node,presentAfter,tag,exposure⟩,?_⟩⟩
  · rw [mapping];exact metadata.noFree
  · rw [mapping,nodes];exact metadata.aligned
  · rw [mapping];exact metadata.mappingSize
  · rw [nodes];exact metadata.nodeSize
  · rw [nodes];exact metadata.nodeFits
  · change after.tagMapping.get oldTag = some target
    rw [mapping]
    exact metadata.tagPresent

/-- Consume only the actual runtime's release-frame boundary to form all
metadata required by the next mutable expression, from original caller data. -/
theorem build (tree : BorrowTree) (protections : ProtectedTags) (target : UniIndex)
    (exprTag nextTag : BorTag) (offset len : UInt64) (first : Data tree exprTag target offset len)
    (noFree : tree.tagMapping.deassigned.back? = none) (room : tree.tagMapping.mapping.size+1 ≤ 4294967295)
    (freshTag : GeneralBorrowTagMap.Fresh tree.tagMapping nextTag)
    (freshProtector : GeneralBorrowProtector.Fresh tree nextTag) (different : exprTag ≠ nextTag)
    (cleanFuture : Every (fun location : LocationTree => location.perms.get (GeneralBorrowFreshSharedNext.future tree) = none) tree.locations)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned tree protections target .Write) offset (offset+len) tree.locations)
    (released : BorrowTree)
    (frame :
      let choice := GeneralBorrowFreshSharedNext.next tree protections target exprTag nextTag offset len first noFree room
        freshTag freshProtector different cleanFuture owned
      released = {(child choice.val protections true).tree with locations := released.locations}) :
    Nonempty (Output tree released target first.parentNode first.parentTag) := by
  obtain ⟨metadata⟩ := stages tree protections target exprTag nextTag offset len first noFree room freshTag freshProtector different cleanFuture owned
  exact of_frame tree _ released target first.parentNode first.parentTag metadata frame

/-- The next two append slots require initial capacity for all four new tags. -/
theorem room {before after : BorrowTree} {target : UniIndex} {node : TreeNode} {tag : BorTag}
    (metadata : Output before after target node tag) (initialRoom : before.tagMapping.mapping.size+3 ≤ 4294967295) :
    after.tagMapping.mapping.size+1 ≤ 4294967295 := by rw [metadata.mappingSize];omega
/-- Construct the following expression's append Slot from initial four-slot
capacity, without a post-release allocator hypothesis. -/
def next_slot {before after : BorrowTree} {target : UniIndex} {node : TreeNode} {tag : BorTag}
    (metadata : Output before after target node tag) (initialRoom : before.tagMapping.mapping.size+3 ≤ 4294967295) :
    GeneralBorrowFreshReborrowStages.Slot after metadata.certificates.depth target :=
  .append metadata.noFree metadata.aligned (by have bound := room metadata initialRoom;omega)
end DuplicatePrefix.GeneralBorrowFreshSharedReleasedMetadata
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshSharedReleasedMetadata." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved released shared metadata dependency {dependency}"
