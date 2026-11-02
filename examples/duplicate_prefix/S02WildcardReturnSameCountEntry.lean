import duplicate_prefix.S02WildcardReturnSameSourceActivityPacket
import duplicate_prefix.S02WildcardReturnRootNotPrimary
import duplicate_prefix.S03ReturnWildcardMetadata
namespace DuplicatePrefix.S02WildcardReturnSameCountEntry
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
/-- Facts about the actual wildcard protection result, independent of the
source's original provenance and of the count stored in its caller frame. -/
structure Packet (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (budget : Nat) (before : Before) (place : MPlaceTy Provenance)
    (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame) (owned : FrameState)
    (fresh : input.tracker.global.nextPointerTag.value < 18446744073709551615)
    (sourceTag : BorTag) (query selected : UniIndex) (maximum : Option BorTag) (lower width : UInt64) (node : TreeNode) where
  tree : BorrowTree
  updated : Allocation Provenance BorrowTree
  protect : TypedRetag.protectInPlaceFunctionArgument (config options remaining span).retag budget place
    (Storage.withCurrent frames frame before) = .ok () (S04ProtectUninit.finished before place input frames frame owned fresh tree updated)
  physical : S04FinalReturnWildcardInput.Destination (S04ProtectUninit.finished before place input frames frame owned fresh tree updated).machine place
  physicalId : physical.id = input.id
  physicalEntry : physical.entry = {input.entry with allocation := updated}
  physicalOffset : physical.offset = input.offset
  sourcePositive : DuplicatePrefixBorrowAuthorization.Positive updated.extra
    (TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker input.tracker fresh) input.tracker.global.nextPointerTag).protectedTags
    (some query) (some selected) maximum lower width
  sourceActivity : GeneralBorrowFreshActiveWithin.ActiveWithin updated.extra query .Write lower (lower+width)
  sourcePresent : updated.extra.nodeAt query = some node
  sourceTagged : updated.extra.indexOfTag sourceTag = some query
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts updated.extra
    (TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker input.tracker fresh) input.tracker.global.nextPointerTag)
  capacity : updated.extra.locations.size = input.entry.allocation.extra.locations.size
  growth : updated.extra.nodes.size ≤ input.entry.allocation.extra.nodes.size+1
  distinct : updated.extra.roots.toList.Nodup
  order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder updated.extra
  exposed : GeneralBorrowFreshRootSupportCutoff.ExposedBound updated.extra input.tracker.global.nextPointerTag
  child : UniIndex
  returnNode : TreeNode
  returnTagged : updated.extra.indexOfTag input.tracker.global.nextPointerTag = some child
  returnPresent : updated.extra.nodeAt child = some returnNode
  returnSame : returnNode.tag = input.tracker.global.nextPointerTag
  parentless : returnNode.parent = none
  leaf : returnNode.children = #[]
  hidden : returnNode.isExposed = false
  returnPositive : DuplicatePrefixBorrowAuthorization.Positive updated.extra
    (TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker input.tracker fresh) input.tracker.global.nextPointerTag).protectedTags
    (some child) (some child) (some input.tracker.global.nextPointerTag) input.offset 1
  returnActivity : GeneralBorrowFreshActiveWithin.ActiveWithin updated.extra child .Write input.offset (input.offset+1)
  notPrimary : ∀ valid : 0 < updated.extra.roots.size, updated.extra.roots[0] ≠ child
/-- Execute real wildcard protection/uninit from current source capability.
No future operation or activity result is a premise. -/
theorem after_current
    {options : EvalConfigurationCore.Options} {remaining : Nat} {span : PreparedContracts.FixedSpanQuery}
    (budget : Nat) (before : Before) (model : DuplicatePrefixCallModel.Model options remaining span before)
    (place : MPlaceTy Provenance) (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts input.entry.allocation.extra input.tracker.global)
    (distinct : input.entry.allocation.extra.roots.toList.Nodup)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder input.entry.allocation.extra)
    (headroom : input.entry.allocation.extra.nodes.size+1 < 65536)
    (fresh : input.tracker.global.nextPointerTag.value < 18446744073709551615) (wildcard : input.pointer.provenance = .wildcard)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame) (owned : FrameState)
    (frameBorrow : frame.extra.borrowTracker = some owned)
    (sync : Array (Size × MemoryExtras.Entry Unit))
    (extras : before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == input.id) = some (input.id,⟨none,sync⟩))
    (outsideSync : ∀ row ∈ sync,row.1.bytes.toNat < input.offset.toNat ∨ input.offset.toNat+1 ≤ row.1.bytes.toNat)
    (sourceTag : BorTag) (query selected : UniIndex) (maximum : Option BorTag) (lower width : UInt64) (node : TreeNode)
    (tagged : input.entry.allocation.extra.indexOfTag sourceTag = some query)
    (present : input.entry.allocation.extra.nodeAt query = some node) (leaf : node.children = #[]) (hidden : node.isExposed = false)
    (outside : input.offset.toNat+1 ≤ lower.toNat ∨ (lower+width).toNat ≤ input.offset.toNat)
    (positive : DuplicatePrefixBorrowAuthorization.Positive input.entry.allocation.extra input.tracker.global.protectedTags
      (some query) (some selected) maximum lower width)
    (activity : GeneralBorrowFreshActiveWithin.ActiveWithin input.entry.allocation.extra query .Write lower (lower+width)) :
    Nonempty (Packet options remaining span budget before place input frames frame owned fresh sourceTag query selected maximum lower width node) := by
  obtain ⟨tree,updated,protect,extra,bytes,length,mutable,maskWf,maskLen,pointers,capacity,post,short,roots,postOrder,exposed,other,
    child,returnTagged,rootPush,⟨returnPositive⟩,returnActivity,returnNode,returnPresent,returnSame,parentless,returnLeaf,returnHidden⟩ :=
    S03ReturnWildcardProtectionRawOtherTags.invoke_other_tags budget before model place input runtime distinct order headroom fresh wildcard
      frames frame owned frameBorrow sync extras outsideSync
  obtain ⟨otherUpdated,otherProtect,otherExtra,_,_,_,⟨sourcePositive⟩,sourceActivity,sourcePresent,sourceTags,sourceRuntime,sourceCapacity,_⟩ :=
    S02WildcardReturnSameSourceActivityPacket.invoke budget before model place input runtime distinct headroom fresh wildcard frames frame owned frameBorrow sync extras outsideSync
      query selected maximum lower width outside positive node present leaf hidden activity
  let literalTree := ((input.entry.allocation.extra.performBorrowAccessRange .wildcard (Size.ofBytes input.offset) (Size.ofBytes 1) .Read
    (GeneralBorrowFnEntryRegistration.registered input.tracker.global owned input.id fresh).1.protectedTags .VisitChildrenOfAccessed).tree.newChild
    (Size.ofBytes input.offset) .wildcard input.tracker.global.nextPointerTag
    (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes 1) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree
  have sameState := (EStateM.Result.ok.inj (protect.symm.trans otherProtect)).2
  have firstLive : (S04ProtectUninit.finished before place input frames frame owned fresh tree updated).machine.memory.live.find? (fun row => row.1 == input.id) =
      some (input.id,{input.entry with allocation := updated}) := MemoryCopyBridge.live_lookup_replaced _ _ _
  have secondLive : (S04ProtectUninit.finished before place input frames frame owned fresh literalTree otherUpdated).machine.memory.live.find? (fun row => row.1 == input.id) =
      some (input.id,{input.entry with allocation := otherUpdated}) := MemoryCopyBridge.live_lookup_replaced _ _ _
  have updatedEq : updated = otherUpdated := by
    rw [sameState] at firstLive
    exact congrArg (fun row => row.2.allocation) (Option.some.inj (firstLive.symm.trans secondLive))
  rw [←updatedEq] at otherExtra sourcePositive sourceActivity sourcePresent sourceTags sourceRuntime sourceCapacity
  have binding := input.binding
  simp only [DuplicatePrefixReferenceInput.Binding,wildcard] at binding
  have destination := input.borrow
  rw [binding.1] at destination
  obtain ⟨selectedNone,maximumNone⟩ := S05WildcardEntryBridge.wildcard_metadata _ _ input.selectedRoot input.maximum input.offset 1 runtime.formed destination
  rw [selectedNone,maximumNone] at destination
  obtain ⟨output,operation,_tag,_global,_frame,_readDone,_childDone,_post,_capacity,growth,_⟩ :=
    GeneralBorrowRawWildcardFnEntryScopedResources.invoke input.entry.allocation.extra input.tracker.global owned input.id runtime input.offset 1 destination distinct
      (by omega) (by omega) fresh
  have outputEq := operation
  simp only [GeneralBorrowRawWildcardFnEntryRuntime.operation,TypedRetagEmpty.allocate_tag input.tracker.global fresh,Except.bind,Except.pure,bind,pure] at outputEq
  have outputShape := Except.ok.inj outputEq
  subst output
  have writtenFrame := GeneralBorrowFreshReadFrame.frame literalTree (.concrete input.tracker.global.nextPointerTag)
    (Size.ofBytes input.offset) (Size.ofBytes 1) .Write
    (GeneralBorrowFnEntryRegistration.registered input.tracker.global owned input.id fresh).1.protectedTags .VisitChildrenOfAccessed
  have nodeGrowth : updated.extra.nodes.size ≤ input.entry.allocation.extra.nodes.size+1 := by
    rw [otherExtra,congrArg BorrowTree.nodes writtenFrame]
    exact growth
  let physical := S03ReturnWildcardMetadata.of_protection input wildcard frames frame owned fresh tree updated _ extra bytes length mutable maskWf maskLen pointers capacity
  have rootsNonempty := input.borrow.wildcardRoot binding.1
  have notPrimary := S02WildcardReturnRootNotPrimary.after_push input.entry.allocation.extra _ child rootsNonempty rootPush roots
  refine ⟨{tree := tree,updated := updated,protect := protect,physical := physical,physicalId := rfl,physicalEntry := rfl,physicalOffset := rfl,
           sourcePositive := sourcePositive,sourceActivity := sourceActivity,sourcePresent := sourcePresent,sourceTagged := sourceTags sourceTag query tagged,
           runtime := sourceRuntime,capacity := sourceCapacity,growth := nodeGrowth,distinct := ?_,order := ?_,exposed := ?_,child := child,returnNode := returnNode,
           returnTagged := ?_,returnPresent := ?_,returnSame := returnSame,parentless := parentless,leaf := returnLeaf,hidden := returnHidden,
           returnPositive := ?_,returnActivity := ?_,notPrimary := ?_}⟩
  all_goals rw [extra]
  all_goals first | assumption | exact returnPositive.base
end
end DuplicatePrefix.S02WildcardReturnSameCountEntry
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S02WildcardReturnSameCountEntry." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved wildcard return current entry dependency {dependency}"
