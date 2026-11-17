import duplicate_prefix.S05WildcardCompletedRead
import duplicate_prefix.S05WildcardProtectedRootAuthority
import duplicate_prefix.GeneralBorrowRawWildcardFnEntryRuntime
import duplicate_prefix.GeneralBorrowFnEntryRegistrationRuntime
import duplicate_prefix.CandidateCurrentJointRawReplacement
import duplicate_prefix.GeneralBorrowRangeOutsideOwned
import duplicate_prefix.GeneralBorrowParentTagInvariant
import duplicate_prefix.GeneralBorrowWildcardChildCausalOrder

/-! Actual positive-length wildcard FnEntry borrowing from current completed
resources. The SAME exposed chosen origin supplies every root/byte and the new
virtual completion edge; no selected-root skip or maximum cutoff is introduced.
Source and disjoint Bool raw tables are outputs of actual Read/root insertion.
Typed memory/MIR entry and ordinary ownership admission remain separate. -/
namespace DuplicatePrefix.S05WildcardFnEntryRaw
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowExposedNonleafPrimaryPath
open GeneralBorrowWildcardParentTagOrder GeneralRangeMapOrigins GeneralRangeMapState
open S05CompletedAncestryReadMutable (Authority)
open GeneralBorrowFnEntryRegistration
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

private theorem registered_flags (tree : BorrowTree) (global : GlobalState) (frame : FrameState)
    (allocation : AllocId) (room : global.nextPointerTag.value < 18446744073709551615)
    (fresh : GeneralBorrowProtector.Fresh tree global.nextPointerTag) :
    ∀ index node, tree.nodes.get index = some node →
      (registered global frame allocation room).1.protectedTags.contains node.tag = global.protectedTags.contains node.tag := by
  intro index node present
  exact ProtectorInsertion.contains_other global.protectedTags global.nextPointerTag node.tag .StrongProtector
    (fresh (index,node) (Array.mem_toList_iff.mp ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes index node).mpr present)))

/-- Strong registration followed by the real wildcard ranged Read retains the
one chosen-origin authority and reconstructs complete runtime/graph facts. -/
theorem prepare_read (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (completion : Completion) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (complete : Completes tree completion) (order : ParentTagOrder tree)
    (position : Nat) (selected source : UniIndex) (selectedNode sourceNode : TreeNode)
    (slot : tree.roots[position]? = some selected) (selectedPresent : tree.nodes.get selected = some selectedNode)
    (sourcePresent : tree.nodes.get source = some sourceNode) (exposed : sourceNode.isExposed = true)
    (sourcePath : Path tree selected source) (tagRoom : global.nextPointerTag.value < 18446744073709551615)
    (offset len : UInt64) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (owned : OwnedOn (Authority tree completion global.protectedTags source) offset (offset+len) tree.locations)
    (short : tree.nodes.size < 65536) (mode : ChildrenVisitMode) :
    let registration := registered global frame allocation tagRoom
    let accessed := tree.performBorrowAccessRange .wildcard (Size.ofBytes offset) (Size.ofBytes len)
      .Read registration.1.protectedTags mode
    accessed.status = .Completed ∧ DuplicatePrefixBorrowContract.RuntimeFacts accessed.tree registration.1 ∧
      Completes accessed.tree completion ∧
      OwnedOn (Authority accessed.tree completion registration.1.protectedTags source) offset (offset+len) accessed.tree.locations ∧
      accessed.tree.nodes = tree.nodes ∧ accessed.tree.roots = tree.roots ∧ accessed.tree.tagMapping = tree.tagMapping ∧
      accessed.tree.locations.size = tree.locations.size := by
  obtain ⟨_,_,_,registeredRuntime,nodeFresh,_⟩ :=
    GeneralBorrowFnEntryRegistrationRuntime.prepare tree global frame allocation tagRoom runtime
  let registration := registered global frame allocation tagRoom
  let accessed := tree.performBorrowAccessRange .wildcard (Size.ofBytes offset) (Size.ofBytes len)
    .Read registration.1.protectedTags mode
  have flags := registered_flags tree global frame allocation tagRoom nodeFresh
  obtain ⟨depth⟩ := registeredRuntime.formed.depth
  have rowInput : OwnedOn (fun location => GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location ∧
      Authority tree completion registration.1.protectedTags source location) offset (offset+len) tree.locations := by
    intro cursor valid positive start stop
    refine ⟨registeredRuntime.possible cursor valid,?_⟩
    intro index node present
    rw [flags index node present]
    exact owned cursor valid positive start stop index node present
  have range := S05WildcardCompletedRead.range tree completion registration.1.protectedTags complete
    registeredRuntime.formed.toGraphState depth order position selected source selectedNode sourceNode
    slot selectedPresent sourcePresent exposed sourcePath (Size.ofBytes offset) (Size.ofBytes len) offset (offset+len)
    rowInput registeredRuntime.formed.well
    (fun cursor valid => ⟨registeredRuntime.coherent cursor valid,registeredRuntime.formed.profile cursor valid,
      registeredRuntime.possible cursor valid⟩) bounds (Nat.le_refl _) (Nat.le_refl _) short mode
  have nodes : accessed.tree.nodes = tree.nodes := range.nodes
  have same : accessed.tree = {tree with locations := accessed.tree.locations} := range.tree_eq
  have afterRuntime : DuplicatePrefixBorrowContract.RuntimeFacts accessed.tree registration.1 := by
    rw [same]
    refine ⟨⟨⟨GeneralBorrowStructuralHistoryState.graph_locations tree _ registeredRuntime.formed.toGraphState,
      range.well⟩,?_⟩,?_,?_,⟨registeredRuntime.below.mapping,registeredRuntime.below.protectors⟩⟩
    · intro cursor valid
      exact ⟨(range.runtime cursor valid).2.1.present,(range.runtime cursor valid).2.1.vacant⟩
    · intro cursor valid
      exact (range.runtime cursor valid).1
    · intro cursor valid
      exact (range.runtime cursor valid).2.2
  have afterComplete : Completes accessed.tree completion := by
    rw [same]
    exact CandidateCurrentJointRawReplacement.completes tree completion _ complete
  refine ⟨range.completed,afterRuntime,afterComplete,?_,range.nodes,range.roots,range.tags,range.capacity⟩
  intro cursor valid positive start stop index node present
  exact (range.rows cursor valid positive start stop).2 index node (by rw [←nodes];exact present)

/-- Literal allocation→Strong registration→all-root max=none Read→protected
physical root insertion. Its virtual parent is the SAME fixed exposed origin;
the source-child and disjoint old Bool grant share ONE extended completion. -/
theorem invoke_window (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (completion : Completion) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (complete : Completes tree completion) (order : ParentTagOrder tree)
    (position : Nat) (selected source : UniIndex) (selectedNode sourceNode : TreeNode)
    (slot : tree.roots[position]? = some selected) (selectedPresent : tree.nodes.get selected = some selectedNode)
    (sourcePresent : tree.nodes.get source = some sourceNode) (exposed : sourceNode.isExposed = true)
    (sourcePath : Path tree selected source) (tagRoom : global.nextPointerTag.value < 18446744073709551615)
    (nodeRoom : tree.nodes.size+1 ≤ 4294967295) (short : tree.nodes.size < 65536)
    (offset len : UInt64) (nonzero : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (owned : OwnedOn (Authority tree completion global.protectedTags source) offset (offset+len) tree.locations)
    (target : UniIndex) (targetNode : TreeNode) (targetPresent : tree.nodes.get target = some targetNode)
    (boolOffset boolLen : UInt64) (boolBounds : boolOffset.toNat+boolLen.toNat ≤ tree.locations.size.bytes.toNat)
    (disjoint : ∀ point : UInt64, boolOffset.toNat ≤ point.toNat → point.toNat < (boolOffset+boolLen).toNat →
      point.toNat < offset.toNat ∨ (offset+len).toNat ≤ point.toNat)
    (boolOwned : OwnedOn (Authority tree completion global.protectedTags target) boolOffset (boolOffset+boolLen) tree.locations) :
    ∃ output, GeneralBorrowRawWildcardFnEntryRuntime.operation tree global frame allocation offset len = .ok output ∧
      output.tag = global.nextPointerTag ∧ output.global = (registered global frame allocation tagRoom).1 ∧
      output.frame.protectedTags = frame.protectedTags.push (allocation,output.tag) ∧
      output.access.status = .Completed ∧ output.child.outcome = .ok () ∧
      DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree output.global ∧
      output.child.tree.locations.size = tree.locations.size ∧ output.child.tree.nodes.size ≤ tree.nodes.size+1 ∧
      boolOffset.toNat+boolLen.toNat ≤ output.child.tree.locations.size.bytes.toNat ∧
      ParentTagOrder output.child.tree ∧
      output.child.tree.indexOfTag targetNode.tag = some target ∧
      ∃ child, output.child.tree.indexOfTag output.tag = some child ∧ output.child.tree.roots = tree.roots.push child ∧
        Completes output.child.tree (S05ConcreteProtectedChildCompletion.extend completion child source) ∧
        OwnedOn (Authority output.child.tree (S05ConcreteProtectedChildCompletion.extend completion child source)
          output.global.protectedTags child) offset (offset+len) output.child.tree.locations ∧
        OwnedOn (Authority output.child.tree (S05ConcreteProtectedChildCompletion.extend completion child source)
          output.global.protectedTags target) boolOffset (boolOffset+boolLen) output.child.tree.locations := by
  obtain ⟨allocated,held,frameEq,_,nodeFresh,fresh⟩ :=
    GeneralBorrowFnEntryRegistrationRuntime.prepare tree global frame allocation tagRoom runtime
  let registration := registered global frame allocation tagRoom
  let accessed := tree.performBorrowAccessRange .wildcard (Size.ofBytes offset) (Size.ofBytes len)
    .Read registration.1.protectedTags .VisitChildrenOfAccessed
  obtain ⟨readDone,readRuntime,readComplete,readOwned,readNodes,readRoots,readTags,readCapacity⟩ :=
    prepare_read tree global frame allocation completion runtime complete order position selected source selectedNode sourceNode
      slot selectedPresent sourcePresent exposed sourcePath tagRoom offset len bounds owned short .VisitChildrenOfAccessed
  have sourceAfter : accessed.tree.nodes.get source = some sourceNode := by rw [readNodes];exact sourcePresent
  have targetAfter : accessed.tree.nodes.get target = some targetNode := by rw [readNodes];exact targetPresent
  have slotAfter : accessed.tree.roots[position]? = some selected := by rw [readRoots];exact slot
  have pathAfter : Path accessed.tree selected source :=
    GeneralBorrowPrimaryWitnessVisibility.path_nodes (before := accessed.tree) (after := tree) readNodes.symm sourcePath
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping global.nextPointerTag := by rw [readTags];exact fresh
  have room : accessed.tree.nodes.size+1 ≤ 4294967295 := by rw [readNodes];exact nodeRoom
  have tagBound : global.nextPointerTag.value.toNat < registration.1.nextPointerTag.value.toNat := by
    have successor := GenericFunctionEntryNumerics.successor_value global.nextPointerTag tagRoom
    change global.nextPointerTag.value.toNat < (TypedRetagEmpty.successorTag global.nextPointerTag tagRoom).value.toNat
    omega
  have heldTag : registration.1.protectedTags.contains global.nextPointerTag = true := by
    unfold ProtectedTags.contains
    rw [held]
    rfl
  have older := GeneralBorrowParentTagInvariant.parent_below_fresh tree global runtime source sourceNode sourcePresent
  have afterBounds : offset.toNat+len.toNat ≤ accessed.tree.locations.size.bytes.toNat := by rw [readCapacity];exact bounds
  obtain ⟨childDone,afterRuntime,capacity,growth,child,lookup,roots,originFrame,childComplete,sourceOwned⟩ :=
    S05WildcardProtectedRootAuthority.construct accessed.tree registration.1 completion readRuntime readComplete global.nextPointerTag
      freshAfter room tagBound heldTag source sourceNode sourceAfter exposed older position selected slotAfter pathAfter
      offset len nonzero afterBounds readOwned
  have flags := registered_flags tree global frame allocation tagRoom nodeFresh
  have beforeBool : OwnedOn (Authority tree completion registration.1.protectedTags target) boolOffset (boolOffset+boolLen) tree.locations := by
    intro cursor valid positive start stop index node present
    rw [flags index node present]
    exact boolOwned cursor valid positive start stop index node present
  have boolRead := GeneralBorrowRangeOutsideOwned.owned (Authority tree completion registration.1.protectedTags target)
    tree .wildcard (Size.ofBytes offset) (Size.ofBytes len) .Read registration.1.protectedTags .VisitChildrenOfAccessed
    runtime.formed.well bounds boolOffset (boolOffset+boolLen) disjoint beforeBool
  have afterBool : OwnedOn (Authority accessed.tree completion registration.1.protectedTags target)
      boolOffset (boolOffset+boolLen) accessed.tree.locations := by
    intro cursor valid positive start stop index node present
    exact boolRead cursor valid positive start stop index node (by rw [←readNodes];exact present)
  obtain ⟨framedChild,frameLookup,_,boolAfter⟩ := S05WildcardProtectedRootAuthority.disjoint
    accessed.tree registration.1 completion readRuntime readComplete global.nextPointerTag freshAfter room tagBound heldTag
    source sourceNode sourceAfter exposed older position selected slotAfter pathAfter offset len boolOffset (boolOffset+boolLen)
    nonzero afterBounds target ⟨targetNode,targetAfter⟩ disjoint afterBool
  have same : framedChild = child := Option.some.inj (frameLookup.symm.trans lookup)
  subst framedChild
  obtain ⟨current,currentAt,currentTag,_,_⟩ := originFrame.old target targetNode targetAfter
  have targetTag := (childComplete.2.2.2.2.1 target current currentAt).1
  rw [currentTag] at targetTag
  let output : GeneralBorrowForestFnEntry.Output := ⟨registration.1,registration.2,global.nextPointerTag,accessed,
    accessed.tree.newChild (Size.ofBytes offset) .wildcard global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true⟩
  have fullCapacity : output.child.tree.locations.size = tree.locations.size := capacity.trans readCapacity
  have boolAfterBounds : boolOffset.toNat+boolLen.toNat ≤ output.child.tree.locations.size.bytes.toNat := by
    rw [fullCapacity];exact boolBounds
  have afterOrder := GeneralBorrowParentTagInvariant.nodes_frame tree accessed.tree readNodes order
  obtain ⟨depth⟩ := readRuntime.formed.depth
  obtain ⟨mapping,index,inserted,_,vacant,_,_,_⟩ := GeneralBorrowWildcardConstructorSlot.select
    accessed.tree registration.1 readRuntime global.nextPointerTag freshAfter room (.ReservedFrz false) .None
  have childOrder := GeneralBorrowWildcardChildCausalOrder.inserted_order accessed.tree depth afterOrder global.nextPointerTag
    mapping index inserted vacant (Size.ofBytes offset) (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside)
    (.ReservedFrz false) true
  refine ⟨output,?_,rfl,rfl,frameEq,readDone,childDone,afterRuntime,fullCapacity,?_,boolAfterBounds,childOrder,targetTag,
    child,lookup,?_,childComplete,sourceOwned,boolAfter⟩
  · simp only [GeneralBorrowRawWildcardFnEntryRuntime.operation,allocated,Except.bind,Except.pure,bind,pure]
    rfl
  · rw [readNodes] at growth
    exact growth
  · rw [readRoots] at roots
    exact roots


/-- Compatibility specialization for a one-byte target. -/
theorem invoke (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (completion : Completion) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (complete : Completes tree completion) (order : ParentTagOrder tree)
    (position : Nat) (selected source : UniIndex) (selectedNode sourceNode : TreeNode)
    (slot : tree.roots[position]? = some selected) (selectedPresent : tree.nodes.get selected = some selectedNode)
    (sourcePresent : tree.nodes.get source = some sourceNode) (exposed : sourceNode.isExposed = true)
    (sourcePath : Path tree selected source) (tagRoom : global.nextPointerTag.value < 18446744073709551615)
    (nodeRoom : tree.nodes.size+1 ≤ 4294967295) (short : tree.nodes.size < 65536)
    (offset len : UInt64) (nonzero : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (owned : OwnedOn (Authority tree completion global.protectedTags source) offset (offset+len) tree.locations)
    (target : UniIndex) (targetNode : TreeNode) (targetPresent : tree.nodes.get target = some targetNode)
    (boolOffset : UInt64) (boolBounds : boolOffset.toNat+1 ≤ tree.locations.size.bytes.toNat)
    (disjoint : ∀ point : UInt64, boolOffset.toNat ≤ point.toNat → point.toNat < (boolOffset+1).toNat →
      point.toNat < offset.toNat ∨ (offset+len).toNat ≤ point.toNat)
    (boolOwned : OwnedOn (Authority tree completion global.protectedTags target) boolOffset (boolOffset+1) tree.locations) :
    ∃ output, GeneralBorrowRawWildcardFnEntryRuntime.operation tree global frame allocation offset len = .ok output ∧
      output.tag = global.nextPointerTag ∧ output.global = (registered global frame allocation tagRoom).1 ∧
      output.frame.protectedTags = frame.protectedTags.push (allocation,output.tag) ∧
      output.access.status = .Completed ∧ output.child.outcome = .ok () ∧
      DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree output.global ∧
      output.child.tree.locations.size = tree.locations.size ∧ output.child.tree.nodes.size ≤ tree.nodes.size+1 ∧
      boolOffset.toNat+1 ≤ output.child.tree.locations.size.bytes.toNat ∧
      ParentTagOrder output.child.tree ∧
      output.child.tree.indexOfTag targetNode.tag = some target ∧
      ∃ child, output.child.tree.indexOfTag output.tag = some child ∧ output.child.tree.roots = tree.roots.push child ∧
        Completes output.child.tree (S05ConcreteProtectedChildCompletion.extend completion child source) ∧
        OwnedOn (Authority output.child.tree (S05ConcreteProtectedChildCompletion.extend completion child source)
          output.global.protectedTags child) offset (offset+len) output.child.tree.locations ∧
        OwnedOn (Authority output.child.tree (S05ConcreteProtectedChildCompletion.extend completion child source)
          output.global.protectedTags target) boolOffset (boolOffset+1) output.child.tree.locations := by
  exact invoke_window tree global frame allocation completion runtime complete order position selected source selectedNode sourceNode slot selectedPresent sourcePresent exposed sourcePath tagRoom nodeRoom short offset len nonzero bounds owned target targetNode targetPresent boolOffset 1 boolBounds disjoint boolOwned

end DuplicatePrefix.S05WildcardFnEntryRaw

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05WildcardFnEntryRaw." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved wildcard FnEntry raw dependency {dependency}"
