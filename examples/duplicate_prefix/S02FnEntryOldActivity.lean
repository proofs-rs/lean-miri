import duplicate_prefix.S02HiddenLeafActivityRange
import duplicate_prefix.GeneralBorrowProtectedSiblingActivityConstructor
import duplicate_prefix.GeneralBorrowRawFnEntryArgument

namespace DuplicatePrefix.S02FnEntryOldActivity
open Miri Miri.Interpreter Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshActiveWithin
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- A real protected constructor preserves every existing node's activity,
regardless of window containment or the actual append/reuse choice. -/
theorem constructor (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (offset len : UInt64) (nonzero : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (query : UniIndex) (node : TreeNode) (found : tree.nodeAt query = some node)
    (lower upper : UInt64) (active : ActiveWithin tree query .Write lower upper) :
    ActiveWithin (tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree query .Write lower upper := by
  let depth := GeneralBorrowStructuralHistoryMutable.depth tree runtime.formed.toState
  let slot := GeneralBorrowStructuralHistoryMutable.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree aligned fits =>
    exact GeneralBorrowProtectedSiblingActivityConstructor.append
      ⟨tree,depth,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        noFree,aligned,fits,offset,len,nonzero,runtime.formed.well,bounds⟩ query node found .Write lower upper active
  | reuse index available bounded vacant slack =>
    exact GeneralBorrowProtectedSiblingActivityConstructor.reuse
      ⟨tree,depth,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        index,available,bounded,vacant,slack,offset,len,nonzero,runtime.formed.well,bounds⟩ query node found .Write lower upper active

/-- The actual registered Read followed by protected FnEntry construction
preserves an arbitrary distinct hidden old leaf's source activity interval.
No intermediate success/activity and no sibling/single-root condition is input. -/
theorem preserved (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (frame : FrameState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowRawFnEntry.Input tree tracker.global)
    (query : UniIndex) (node : TreeNode) (present : tree.nodeAt query = some node)
    (leaf : node.children = #[]) (hidden : node.isExposed = false) (different : query ≠ input.parent)
    (lower upper : UInt64) (active : ActiveWithin tree query .Write lower upper) :
    ActiveWithin (GeneralBorrowRawFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len)
      query .Write lower upper := by
  obtain ⟨allocated,held,frameEq,registeredRuntime,⟨registeredPositive⟩,fresh⟩ :=
    GeneralBorrowFnEntryRegistration.prepare tree tracker.global frame allocation input.tagRoom runtime
      input.parent input.selected input.maximum input.offset input.len input.positive
  let registration := GeneralBorrowFnEntryRegistration.registered tracker.global frame allocation input.tagRoom
  let accessed := tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset)
    (Size.ofBytes input.len) .Read registration.1.protectedTags .VisitChildrenOfAccessed
  have afterActive := S02HiddenLeafActivityRange.concrete tree registration.1 registeredRuntime input.parentTag
    input.parent input.selected query input.maximum input.offset input.len registeredPositive input.tagged node present
    leaf hidden different lower upper active .Read .VisitChildrenOfAccessed
  obtain ⟨contract,afterRuntime,⟨afterPositive⟩⟩ := GeneralBorrowConcreteRowReadRange.access_runtime tree registration.1 registeredRuntime
    input.parentTag input.parent input.selected input.maximum input.tagged (Size.ofBytes input.offset) (Size.ofBytes input.len)
    .VisitChildrenOfAccessed input.offset input.len registeredPositive input.distinct input.order input.short
    (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨parentNode,parentPresent⟩ := afterPositive.sourcePresent input.parent rfl
  have tagged : accessed.tree.indexOfTag input.parentTag = some input.parent := by
    unfold BorrowTree.indexOfTag
    rw [contract.tags]
    exact input.tagged
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping tracker.global.nextPointerTag := by rw [contract.tags];exact fresh
  have room : accessed.tree.nodes.size+1 ≤ 4294967295 := by rw [contract.nodes];exact input.nodeRoom
  have nonzero : input.len ≠ 0 := by intro zero;have p := input.positive.positive;rw [zero] at p;contradiction
  have oldPresent : accessed.tree.nodeAt query = some node := by
    change accessed.tree.nodes.get query = some node
    rw [contract.nodes]
    exact present
  exact constructor accessed.tree registration.1 afterRuntime input.parentTag tracker.global.nextPointerTag input.parent parentNode
    tagged parentPresent freshAfter room input.offset input.len nonzero afterPositive.bounds query node oldPresent lower upper afterActive

end DuplicatePrefix.S02FnEntryOldActivity
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S02FnEntryOldActivity.constructor,``DuplicatePrefix.S02FnEntryOldActivity.preserved] do
    for ax in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "unapproved axiom {ax}"
