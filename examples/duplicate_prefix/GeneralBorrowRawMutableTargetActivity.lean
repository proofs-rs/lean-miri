import duplicate_prefix.GeneralBorrowRawTargetActivity
import duplicate_prefix.GeneralBorrowRawDefaultResources
import duplicate_prefix.GeneralBorrowRawFnEntryHidden
namespace DuplicatePrefix.GeneralBorrowRawMutableTargetActivity
open Miri Miri.Interpreter Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshActiveWithin
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
/-- The exact unprotected Default driver tree preserves an arbitrary old
mutable owner's confinement, using only current raw resources/activity. -/
theorem default_stage (tree : BorrowTree) (tracker : MachineHooks.BorrowState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowRawDefault.Input tree tracker.global) (target : UniIndex)
    (active : ActiveWithin tree target .Write input.offset (input.offset+input.len)) :
    ActiveWithin (GeneralBorrowRawDefaultExpression.child tree tracker.global.protectedTags
      input.parentTag tracker.global.nextPointerTag input.offset input.len .VisitChildrenOfAccessed).tree
      target .Write input.offset (input.offset+input.len) := by
  obtain ⟨allocated,current,⟨positive⟩,fresh,unheld⟩ := GeneralBorrowDefaultTagAllocation.prepare tree tracker.global
    input.tagRoom runtime input.parent input.selected input.maximum input.offset input.len input.positive
  let global := GeneralBorrowFnEntryRegistration.advanced tracker.global input.tagRoom
  let read := tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len)
    .Read global.protectedTags .VisitChildrenOfAccessed
  obtain ⟨contract,afterRuntime,⟨afterPositive⟩⟩ := GeneralBorrowConcreteRowReadRange.access_runtime tree global current
    input.parentTag input.parent input.selected input.maximum input.tagged (Size.ofBytes input.offset) (Size.ofBytes input.len)
    .VisitChildrenOfAccessed input.offset input.len positive input.distinct input.order input.short (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨parentNode,parentPresent⟩ := afterPositive.sourcePresent input.parent rfl
  have readActive : ActiveWithin read.tree target .Write input.offset (input.offset+input.len) :=
    GeneralBorrowFreshActiveWithinAccess.normal tree input.parentTag (Size.ofBytes input.offset) (Size.ofBytes input.len)
      .Read global.protectedTags .VisitChildrenOfAccessed target input.offset (input.offset+input.len)
      runtime.formed.well input.positive.bounds (Nat.le_refl _) (Nat.le_refl _) active
  have tagged : read.tree.indexOfTag input.parentTag = some input.parent := by
    change read.tree.tagMapping.get input.parentTag = some input.parent
    rw [contract.tags]
    exact input.tagged
  have afterFresh : GeneralBorrowTagMap.Fresh read.tree.tagMapping tracker.global.nextPointerTag := by rw [contract.tags];exact fresh
  have room : read.tree.nodes.size+1 ≤ 4294967295 := by rw [contract.nodes];exact input.nodeRoom
  have nonzero : input.len ≠ 0 := by intro zero;have p := input.positive.positive;rw [zero] at p;contradiction
  exact GeneralBorrowRawTargetActivity.default_child read.tree global afterRuntime input.parentTag tracker.global.nextPointerTag
    input.parent parentNode tagged parentPresent afterFresh room input.offset input.len nonzero afterPositive.bounds target
    input.offset (input.offset+input.len) (Nat.le_refl _) (Nat.le_refl _) readActive

/-- Actual protected FnEntry parent Read/constructor and the real helper
release retain arbitrary old-owner confinement. EndCall changes no tree. -/
theorem fnentry_stage (tree : BorrowTree) (tracker : MachineHooks.BorrowState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowRawFnEntry.Input tree tracker.global) (target : UniIndex)
    (active : ActiveWithin tree target .Write input.offset (input.offset+input.len)) :
    let finalTree := GeneralBorrowRawFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len
    let held := TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag
    ActiveWithin finalTree target .Write input.offset (input.offset+input.len) ∧
      ActiveWithin (finalTree.releaseProtector tracker.global.nextPointerTag held.protectedTags).tree
        target .Write input.offset (input.offset+input.len) := by
  obtain ⟨allocated,held,frameEq,current,⟨positive⟩,fresh⟩ := GeneralBorrowFnEntryRegistration.prepare tree tracker.global
    ({} : FrameState) (⟨1,by decide⟩ : AllocId) input.tagRoom runtime input.parent input.selected input.maximum input.offset input.len input.positive
  let global := (GeneralBorrowFnEntryRegistration.registered tracker.global ({} : FrameState) (⟨1,by decide⟩ : AllocId) input.tagRoom).1
  let read := tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len)
    .Read global.protectedTags .VisitChildrenOfAccessed
  obtain ⟨contract,afterRuntime,⟨afterPositive⟩⟩ := GeneralBorrowConcreteRowReadRange.access_runtime tree global current
    input.parentTag input.parent input.selected input.maximum input.tagged (Size.ofBytes input.offset) (Size.ofBytes input.len)
    .VisitChildrenOfAccessed input.offset input.len positive input.distinct input.order input.short (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨parentNode,parentPresent⟩ := afterPositive.sourcePresent input.parent rfl
  have readActive : ActiveWithin read.tree target .Write input.offset (input.offset+input.len) :=
    GeneralBorrowFreshActiveWithinAccess.normal tree input.parentTag (Size.ofBytes input.offset) (Size.ofBytes input.len)
      .Read global.protectedTags .VisitChildrenOfAccessed target input.offset (input.offset+input.len)
      runtime.formed.well input.positive.bounds (Nat.le_refl _) (Nat.le_refl _) active
  have tagged : read.tree.indexOfTag input.parentTag = some input.parent := by
    change read.tree.tagMapping.get input.parentTag = some input.parent
    rw [contract.tags]
    exact input.tagged
  have afterFresh : GeneralBorrowTagMap.Fresh read.tree.tagMapping tracker.global.nextPointerTag := by rw [contract.tags];exact fresh
  have room : read.tree.nodes.size+1 ≤ 4294967295 := by rw [contract.nodes];exact input.nodeRoom
  have nonzero : input.len ≠ 0 := by intro zero;have p := input.positive.positive;rw [zero] at p;contradiction
  have constructed := GeneralBorrowRawTargetActivity.protected_child read.tree global afterRuntime input.parentTag tracker.global.nextPointerTag
    input.parent parentNode tagged parentPresent afterFresh room input.offset input.len nonzero afterPositive.bounds target
    input.offset (input.offset+input.len) (Nat.le_refl _) (Nat.le_refl _) readActive
  change ActiveWithin (GeneralBorrowRawFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len)
    target .Write input.offset (input.offset+input.len) at constructed
  obtain ⟨afterRuntime,capacity,growth,roots,strong,framePush,tagFresh,child,lookup,positive,activity⟩ :=
    GeneralBorrowRawFnEntryResources.resources tree tracker ({} : FrameState) (⟨1,by decide⟩ : AllocId) runtime input
  obtain ⟨hiddenChild,node,hiddenLookup,present,sameTag,hidden⟩ :=
    GeneralBorrowRawFnEntryHidden.hidden tree tracker ({} : FrameState) (⟨1,by decide⟩ : AllocId) runtime input
  have sameChild : child = hiddenChild := Option.some.inj (lookup.symm.trans hiddenLookup)
  subst hiddenChild
  exact ⟨constructed,GeneralBorrowActiveWithinRelease.release _ _ tracker.global.nextPointerTag child target node lookup present hidden
    input.offset (input.offset+input.len) activity constructed⟩
/-- Literal mutable suffix activity: current Default packet internally forms
its actual next FnEntry packet, then both constructors and real release retain
the original mutable owner's confinement. -/
theorem suffix (tree : BorrowTree) (tracker : MachineHooks.BorrowState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowRawDefault.Input tree tracker.global)
    (headroom : tree.nodes.size+2 < 65536)
    (tagRoom : tracker.global.nextPointerTag.value.toNat+1 < 18446744073709551615)
    (target : UniIndex)
    (active : ActiveWithin tree target .Write input.offset (input.offset+input.len)) :
    let defaultTree := (GeneralBorrowRawDefaultExpression.child tree tracker.global.protectedTags input.parentTag
      tracker.global.nextPointerTag input.offset input.len .VisitChildrenOfAccessed).tree
    let advanced := ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom
    let helperTree := GeneralBorrowRawFnEntryArgument.finalTree defaultTree advanced tracker.global.nextPointerTag input.offset input.len
    let held := TypedBorrowSteps.registeredGlobal advanced advanced.global.nextPointerTag
    ActiveWithin defaultTree target .Write input.offset (input.offset+input.len) ∧
      ActiveWithin helperTree target .Write input.offset (input.offset+input.len) ∧
      ActiveWithin (helperTree.releaseProtector advanced.global.nextPointerTag held.protectedTags).tree
        target .Write input.offset (input.offset+input.len) := by
  let defaultTree := (GeneralBorrowRawDefaultExpression.child tree tracker.global.protectedTags input.parentTag
    tracker.global.nextPointerTag input.offset input.len .VisitChildrenOfAccessed).tree
  let advanced := ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom
  have first := default_stage tree tracker runtime input target active
  obtain ⟨nextRuntime,capacity,short,next,nextTag,nextSelected,nextMaximum,nextOffset,nextLen⟩ :=
    GeneralBorrowRawDefaultResources.resources tree tracker runtime input headroom tagRoom
  have nextActive : ActiveWithin defaultTree target .Write next.offset (next.offset+next.len) := by
    rw [nextOffset,nextLen]
    exact first
  have later := fnentry_stage defaultTree advanced nextRuntime next target nextActive
  simpa only [nextTag,nextOffset,nextLen] using And.intro first later
end DuplicatePrefix.GeneralBorrowRawMutableTargetActivity
