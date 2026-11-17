import duplicate_prefix.CandidateCurrentWindowAuthority
import duplicate_prefix.DuplicatePrefixCallSpecification
import duplicate_prefix.CandidateCurrentLiveRuntime

/-! Immediate positive current-call borrowing consumer. Content admission and
complete typed MIR entry remain separate from this operational bridge. -/
namespace DuplicatePrefix.CandidateCurrentFnEntryRaw
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall GeneralRangeMapOrigins GeneralRangeMapState
open GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowWildcardParentTagOrder GeneralBorrowFnEntryRegistration
open S05CompletedAncestryReadMutable (Authority)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

structure Metadata (before after : BorrowTree) : Prop where
  capacity : after.locations.size = before.locations.size
  growth : after.nodes.size ≤ before.nodes.size+1
  order : ParentTagOrder after
  old : ∀ index node, before.nodes.get index = some node →
    ∃ next, after.nodes.get index = some next ∧ next.tag = node.tag ∧
      next.parent = node.parent ∧ next.isExposed = node.isExposed

/-- Source-only wildcard construction for a separate return allocation. No Bool
window in the source tree is invented to call the same-allocation theorem. -/
theorem wildcard_source (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (completion : Completion) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (complete : Completes tree completion) (order : ParentTagOrder tree)
    (position : Nat) (selected source : UniIndex) (selectedNode sourceNode : TreeNode)
    (slot : tree.roots[position]? = some selected) (selectedPresent : tree.nodes.get selected = some selectedNode)
    (sourcePresent : tree.nodes.get source = some sourceNode) (exposed : sourceNode.isExposed = true)
    (sourcePath : Path tree selected source) (tagRoom : global.nextPointerTag.value < 18446744073709551615)
    (nodeRoom : tree.nodes.size+1 ≤ 4294967295) (short : tree.nodes.size < 65536)
    (offset len : UInt64) (nonzero : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (owned : OwnedOn (Authority tree completion global.protectedTags source) offset (offset+len) tree.locations) :
    ∃ output,  GeneralBorrowRawWildcardFnEntryRuntime.operation tree global frame allocation offset len = .ok output ∧
      output.tag = global.nextPointerTag ∧ output.global = (registered global frame allocation tagRoom).1 ∧
      output.access.status = .Completed ∧ output.child.outcome = .ok () ∧
      DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree output.global ∧
      ∃ child,  output.child.tree.indexOfTag output.tag = some child ∧
        Completes output.child.tree (S05ConcreteProtectedChildCompletion.extend completion child source) ∧
        OwnedOn (Authority output.child.tree (S05ConcreteProtectedChildCompletion.extend completion child source)
          output.global.protectedTags child) offset (offset+len) output.child.tree.locations ∧
        Metadata tree output.child.tree ∧
        (∃ node, output.child.tree.nodes.get child = some node ∧ node.tag = output.tag) := by
  obtain ⟨allocated, held, _, _, _, fresh⟩ :=
    GeneralBorrowFnEntryRegistrationRuntime.prepare tree global frame allocation tagRoom runtime
  let registration := registered global frame allocation tagRoom
  let accessed := tree.performBorrowAccessRange .wildcard (Size.ofBytes offset) (Size.ofBytes len)
    .Read registration.1.protectedTags .VisitChildrenOfAccessed
  obtain ⟨readDone, readRuntime, readComplete, readOwned, readNodes, readRoots, readTags, readCapacity⟩ :=
    S05WildcardFnEntryRaw.prepare_read tree global frame allocation completion runtime complete order position selected source
      selectedNode sourceNode slot selectedPresent sourcePresent exposed sourcePath tagRoom offset len bounds owned short
      .VisitChildrenOfAccessed
  have sourceAfter : accessed.tree.nodes.get source = some sourceNode := by rw [readNodes];exact sourcePresent
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
  obtain ⟨childDone, afterRuntime, capacity, growth, child, lookup, _, rootFrame, childComplete, sourceOwned⟩ :=
    S05WildcardProtectedRootAuthority.construct accessed.tree registration.1 completion readRuntime readComplete global.nextPointerTag
      freshAfter room tagBound heldTag source sourceNode sourceAfter exposed older position selected slotAfter pathAfter
      offset len nonzero afterBounds readOwned
  let output : GeneralBorrowForestFnEntry.Output := ⟨registration.1, registration.2, global.nextPointerTag, accessed,
    accessed.tree.newChild (Size.ofBytes offset) .wildcard global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true⟩
  have readOrder := GeneralBorrowParentTagInvariant.nodes_frame tree accessed.tree readNodes order
  obtain ⟨depth⟩ := readRuntime.formed.depth
  obtain ⟨mapping,index,inserted,_,vacant,_,_,_⟩ := GeneralBorrowWildcardConstructorSlot.select
    accessed.tree registration.1 readRuntime global.nextPointerTag freshAfter room (.ReservedFrz false) .None
  have childOrder := GeneralBorrowWildcardChildCausalOrder.inserted_order accessed.tree depth readOrder global.nextPointerTag
    mapping index inserted vacant (Size.ofBytes offset) (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside)
    (.ReservedFrz false) true
  refine ⟨output, ?_, rfl, rfl, readDone, childDone, afterRuntime, child, lookup, childComplete, sourceOwned,
    ⟨capacity.trans readCapacity,?_,childOrder,?_⟩,?_⟩
  · simp only [GeneralBorrowRawWildcardFnEntryRuntime.operation, allocated, Except.bind, Except.pure, bind, pure]
    rfl
  · rw [readNodes] at growth
    exact growth
  · intro index node present
    exact rootFrame.old index node (by rw [readNodes];exact present)
  · obtain ⟨node,nodeAt,tagEq,_⟩ := rootFrame.childLive
    exact ⟨node,nodeAt,tagEq⟩

/-- Dispatch uses the provenance carried by the actual pointer value. -/
def operation (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (provenance : Provenance) (offset len : UInt64) : Except GlobalStateError GeneralBorrowForestFnEntry.Output :=
  match provenance with
  | .concrete _ tag => GeneralBorrowForestFnEntry.operation tree global frame allocation tag offset len .VisitChildrenOfAccessed
  | .wildcard => GeneralBorrowRawWildcardFnEntryRuntime.operation tree global frame allocation offset len

/-- Same-allocation dispatch retains the disjoint Bool's fixed raw grant. -/
theorem same_allocation (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (completion : Completion) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (complete : Completes tree completion) (order : ParentTagOrder tree)
    (pointer : PointerInstance) (sourceNode : TreeNode)
    (sourcePresent : tree.nodes.get pointer.grant = some sourceNode)
    (provenance : match pointer.value.provenance with
      | .concrete _ tag => tag = sourceNode.tag
      | .wildcard => sourceNode.isExposed = true)
    (tagRoom : global.nextPointerTag.value < 18446744073709551615)
    (nodeRoom : tree.nodes.size+1 ≤ 4294967295) (short : tree.nodes.size < 65536)
    (offset len : UInt64) (nonzero : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (owned : OwnedOn (Authority tree completion global.protectedTags pointer.grant) offset (offset+len) tree.locations)
    (target : UniIndex) (targetNode : TreeNode) (targetPresent : tree.nodes.get target = some targetNode)
    (boolOffset : UInt64) (boolBounds : boolOffset.toNat+1 ≤ tree.locations.size.bytes.toNat)
    (disjoint : ∀ point : UInt64,  boolOffset.toNat ≤ point.toNat → point.toNat < (boolOffset+1).toNat →
      point.toNat < offset.toNat ∨ (offset+len).toNat ≤ point.toNat)
    (boolOwned : OwnedOn (Authority tree completion global.protectedTags target) boolOffset (boolOffset+1) tree.locations) :
    ∃ output,  operation tree global frame allocation pointer.value.provenance offset len = .ok output ∧
      output.tag = global.nextPointerTag ∧ output.global = (registered global frame allocation tagRoom).1 ∧
      output.access.status = .Completed ∧ output.child.outcome = .ok () ∧
      DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree output.global ∧
      output.child.tree.indexOfTag targetNode.tag = some target ∧
      ∃ child,  output.child.tree.indexOfTag output.tag = some child ∧
        Completes output.child.tree (S05ConcreteProtectedChildCompletion.extend completion child pointer.grant) ∧
        OwnedOn (Authority output.child.tree (S05ConcreteProtectedChildCompletion.extend completion child pointer.grant)
          output.global.protectedTags child) offset (offset+len) output.child.tree.locations ∧
        OwnedOn (Authority output.child.tree (S05ConcreteProtectedChildCompletion.extend completion child pointer.grant)
          output.global.protectedTags target) boolOffset (boolOffset+1) output.child.tree.locations := by
  obtain ⟨position, root, rootNode, slot, rootAt, path⟩ :=
    CandidateCurrentWindowAuthority.root_path tree runtime.formed.toGraphState pointer.grant sourceNode sourcePresent
  cases actual : pointer.value.provenance with
  | concrete id tag =>
    have sameTag : tag = sourceNode.tag := by simpa [actual] using provenance
    obtain ⟨output, ok, tagEq, globalEq, _, readDone, childDone, afterRuntime, _, _, _, _, boolLookup,
      child, childLookup, _, afterComplete, sourceOwned, boolAfter⟩ :=
      S05ConcreteFnEntryDisjoint.invoke tree global frame allocation completion runtime complete order position root pointer.grant
        rootNode sourceNode slot rootAt sourcePresent path tagRoom nodeRoom short offset len nonzero bounds owned
        target targetNode targetPresent boolOffset boolBounds disjoint boolOwned
    exact ⟨output, by simpa [operation, actual, sameTag] using ok, tagEq, globalEq, readDone, childDone, afterRuntime,
      boolLookup, child, childLookup, afterComplete, sourceOwned, boolAfter⟩
  | wildcard =>
    have exposed : sourceNode.isExposed = true := by simpa [actual] using provenance
    obtain ⟨output, ok, tagEq, globalEq, _, readDone, childDone, afterRuntime, _, _, _, _, boolLookup,
      child, childLookup, _, afterComplete, sourceOwned, boolAfter⟩ :=
      S05WildcardFnEntryRaw.invoke tree global frame allocation completion runtime complete order position root pointer.grant
        rootNode sourceNode slot rootAt sourcePresent exposed path tagRoom nodeRoom short offset len nonzero bounds owned
        target targetNode targetPresent boolOffset boolBounds disjoint boolOwned
    exact ⟨output, by simpa [operation, actual] using ok, tagEq, globalEq, readDone, childDone, afterRuntime,
      boolLookup, child, childLookup, afterComplete, sourceOwned, boolAfter⟩

/-- The source lane for a physically distinct return allocation. -/
theorem source_only (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (completion : Completion) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (complete : Completes tree completion) (order : ParentTagOrder tree)
    (pointer : PointerInstance) (sourceNode : TreeNode)
    (sourcePresent : tree.nodes.get pointer.grant = some sourceNode)
    (provenance : match pointer.value.provenance with
      | .concrete _ tag => tag = sourceNode.tag
      | .wildcard => sourceNode.isExposed = true)
    (tagRoom : global.nextPointerTag.value < 18446744073709551615)
    (nodeRoom : tree.nodes.size+1 ≤ 4294967295) (short : tree.nodes.size < 65536)
    (offset len : UInt64) (nonzero : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (owned : OwnedOn (Authority tree completion global.protectedTags pointer.grant) offset (offset+len) tree.locations) :
    ∃ output,  operation tree global frame allocation pointer.value.provenance offset len = .ok output ∧
      output.tag = global.nextPointerTag ∧ output.global = (registered global frame allocation tagRoom).1 ∧
      output.access.status = .Completed ∧ output.child.outcome = .ok () ∧
      DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree output.global ∧
      ∃ child,  output.child.tree.indexOfTag output.tag = some child ∧
        Completes output.child.tree (S05ConcreteProtectedChildCompletion.extend completion child pointer.grant) ∧
        OwnedOn (Authority output.child.tree (S05ConcreteProtectedChildCompletion.extend completion child pointer.grant)
          output.global.protectedTags child) offset (offset+len) output.child.tree.locations ∧
        Metadata tree output.child.tree ∧
        (∃ node, output.child.tree.nodes.get child = some node ∧ node.tag = output.tag) := by
  obtain ⟨position, root, rootNode, slot, rootAt, path⟩ :=
    CandidateCurrentWindowAuthority.root_path tree runtime.formed.toGraphState pointer.grant sourceNode sourcePresent
  cases actual : pointer.value.provenance with
  | concrete id tag =>
    have sameTag : tag = sourceNode.tag := by simpa [actual] using provenance
    obtain ⟨output, ok, tagEq, globalEq, _, readDone, childDone, afterRuntime, capacity, growth,
      child, childLookup, _, afterComplete, sourceOwned, _, _, _, childOrder, oldNodes,childNode⟩ :=
      S05ConcreteFnEntryRaw.invoke tree global frame allocation completion runtime complete order position root pointer.grant
        rootNode sourceNode slot rootAt sourcePresent path tagRoom nodeRoom short offset len nonzero bounds owned
    exact ⟨output, by simpa [operation, actual, sameTag] using ok, tagEq, globalEq, readDone, childDone, afterRuntime,
      child, childLookup, afterComplete, sourceOwned,⟨capacity,growth,childOrder,oldNodes⟩,childNode⟩
  | wildcard =>
    have exposed : sourceNode.isExposed = true := by simpa [actual] using provenance
    obtain ⟨output, ok, tagEq, globalEq, readDone, childDone, afterRuntime, child, childLookup, afterComplete, sourceOwned,metadata,childNode⟩ :=
      wildcard_source tree global frame allocation completion runtime complete order position root pointer.grant
        rootNode sourceNode slot rootAt sourcePresent exposed path tagRoom nodeRoom short offset len nonzero bounds owned
    exact ⟨output, by simpa [operation, actual] using ok, tagEq, globalEq, readDone, childDone, afterRuntime,
      child, childLookup, afterComplete, sourceOwned,metadata,childNode⟩

private theorem bound_node (before : Before) (held : ProtectedTags)
    (data : Identities) (call : CallLoans) (argument : DuplicatePrefixSliceArgument.Argument)
    (len : UInt64) (place : Miri.Interpreter.MPlaceTy Provenance)
    (joint : CandidateCurrentGrantResources.Joint (ActualWorld before) held data.interpretation)
    (actual : ActualBindings before argument len place held call data)
    (loan : Loan) (pointer : PointerInstance) (id : AllocId)
    (pointerAt : data.interpretation.pointers[loan.pointer]? = some pointer)
    (pointerId : pointer.allocation = id) (allocation : Allocation Provenance BorrowTree)
    (present : Present (ActualWorld before) id allocation) : PointerBinds allocation pointer := by
  obtain ⟨other, otherPresent, binds⟩ := actual.2.2.2.1 pointer
    (Array.mem_toList_iff.mpr (Array.mem_of_getElem? pointerAt))
  rw [pointerId] at otherPresent
  have same := CandidateCurrentUniformOwnerWindow.same_id (ActualWorld before).toList joint.shape.1
    id other allocation otherPresent present
  subst other
  exact binds

/-- Data retained by the immediate call: one fixed instance and completion for
source and return,  and the literal operation selected from source provenance. -/
structure Result (before : Before) (tracker : Miri.Interpreter.MachineHooks.BorrowState)
    (frame : FrameState) (argument : DuplicatePrefixSliceArgument.Argument) (len : UInt64)
    (place : Miri.Interpreter.MPlaceTy Provenance) (call : CallLoans) (data : Identities) where
  sourcePointer : PointerInstance
  returnPointer : PointerInstance
  sourceAllocation : Allocation Provenance BorrowTree
  returnAllocation : Allocation Provenance BorrowTree
  sourcePrecise : PreciseAllocation
  returnPrecise : PreciseAllocation
  sourceLoan : Loan
  returnLoan : Loan
  output : GeneralBorrowForestFnEntry.Output
  child : UniIndex
  argument_eq : argument = .pointer sourcePointer.value
  place_eq : place.mplace.ptr = returnPointer.value.withOptionalProvenance
  sourceLoanAt : data.interpretation.loans[call.sourceOwner]? = some sourceLoan
  returnLoanAt : data.interpretation.loans[call.returnOwner]? = some returnLoan
  sourcePointerAt : data.interpretation.pointers[sourceLoan.pointer]? = some sourcePointer
  returnPointerAt : data.interpretation.pointers[returnLoan.pointer]? = some returnPointer
  sourceId : sourcePointer.allocation = call.sourceId
  returnId : returnPointer.allocation = call.returnId
  sourcePresent : Present (ActualWorld before) call.sourceId sourceAllocation
  returnPresent : Present (ActualWorld before) call.returnId returnAllocation
  sourcePreciseAt : (call.sourceId, sourcePrecise) ∈ data.interpretation.precise.toList
  returnPreciseAt : (call.returnId, returnPrecise) ∈ data.interpretation.precise.toList
  actual : operation sourceAllocation.extra tracker.global frame call.sourceId sourcePointer.value.provenance
    (UInt64.ofNat call.sourceOffset) len = .ok output
  tag : output.tag = tracker.global.nextPointerTag
  readCompleted : output.access.status = .Completed
  childCompleted : output.child.outcome = .ok ()
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree output.global
  tagRoom : tracker.global.nextPointerTag.value < 18446744073709551615
  outputGlobal : output.global = (registered tracker.global frame call.sourceId tagRoom).1
  outputCapacity : output.child.tree.locations.size = sourceAllocation.extra.locations.size
  outputGrowth : output.child.tree.nodes.size ≤ sourceAllocation.extra.nodes.size+1
  outputOrder : ParentTagOrder output.child.tree
  oldNodes : ∀ index node, sourceAllocation.extra.nodes.get index = some node →
    ∃ next, output.child.tree.nodes.get index = some next ∧ next.tag = node.tag ∧
      next.parent = node.parent ∧ next.isExposed = node.isExposed
  childLookup : output.child.tree.indexOfTag output.tag = some child
  childNode : ∃ node, output.child.tree.nodes.get child = some node ∧ node.tag = output.tag
  completes : Completes output.child.tree
    (S05ConcreteProtectedChildCompletion.extend sourcePrecise.completion child sourcePointer.grant)
  sourceOwned : OwnedOn (Authority output.child.tree
    (S05ConcreteProtectedChildCompletion.extend sourcePrecise.completion child sourcePointer.grant)
    output.global.protectedTags child) (UInt64.ofNat call.sourceOffset)
    (UInt64.ofNat call.sourceOffset+len) output.child.tree.locations
  boolOwned :
    let tree := if call.sourceId = call.returnId then output.child.tree else returnAllocation.extra
    let completion := if call.sourceId = call.returnId then
      S05ConcreteProtectedChildCompletion.extend sourcePrecise.completion child sourcePointer.grant
      else returnPrecise.completion
    OwnedOn (Authority tree completion output.global.protectedTags returnPointer.grant)
      (UInt64.ofNat call.returnOffset) (UInt64.ofNat call.returnOffset+1) tree.locations
/-- Consume one current Joint and its actual argument bindings immediately.
The uniform source/Bool witnesses are selected internally by fixed lookups. -/
theorem invoke_from_live (before : Before) (tracker : Miri.Interpreter.MachineHooks.BorrowState)
    (frame : FrameState) (argument : DuplicatePrefixSliceArgument.Argument) (len : UInt64)
    (place : Miri.Interpreter.MPlaceTy Provenance) (call : CallLoans) (data : Identities)
    (joint : CandidateCurrentGrantResources.Joint (ActualWorld before) tracker.global.protectedTags data.interpretation)
    (actual : ActualBindings before argument len place tracker.global.protectedTags call data)
    (normalized : NormalizedWindows before argument len place call data)
    (claims : Claims data.interpretation call) (positive : 0 < len.toNat)
    (tagRoom : tracker.global.nextPointerTag.value < 18446744073709551615)
    (live : ∀ id allocation,  Present (ActualWorld before) id allocation →
      DuplicatePrefixBorrowContract.RuntimeFacts allocation.extra tracker.global ∧
      ParentTagOrder allocation.extra ∧ allocation.extra.nodes.size+1 ≤ 4294967295 ∧
      allocation.extra.nodes.size < 65536 ∧ allocation.len < 2^64 ∧
      allocation.extra.locations.size.bytes.toNat = allocation.len) :
    Nonempty (Result before tracker frame argument len place call data) := by
  obtain ⟨sourcePointer, returnPointer, argumentEq, placeEq, sourceWindow, returnWindow, sourceUniform, returnUniform⟩ :=
    CandidateCurrentUniformOwnerWindow.positive_call_uniform before tracker.global.protectedTags data call argument len
      place joint actual normalized claims positive
  obtain ⟨sourceLoan, sourceAllocation, sourcePrecise, sourceLoanAt, sourcePointerAt, sourceId, sourcePresent, sourcePreciseAt, sourceRights⟩ := sourceUniform
  obtain ⟨returnLoan, returnAllocation, returnPrecise, returnLoanAt, returnPointerAt, returnId, returnPresent, returnPreciseAt, returnRights⟩ := returnUniform
  obtain ⟨sourceRuntime, sourceOrder, nodeRoom, short, sourceRoom, sourceCapacity⟩ := live _ _ sourcePresent
  obtain ⟨returnRuntime, _, _, _, returnRoom, returnCapacity⟩ := live _ _ returnPresent
  -- The physical allocation in the precise shape is unique in this world.
  obtain ⟨shapeAllocation, shapePresent, shapeComplete, _⟩ := joint.shape.2.2 _ _ sourcePreciseAt
  have shapeEq := CandidateCurrentUniformOwnerWindow.same_id (ActualWorld before).toList joint.shape.1
    call.sourceId shapeAllocation sourceAllocation shapePresent sourcePresent
  subst shapeAllocation
  obtain ⟨sourceNode, sourceNodeAt, _, sourceBinds⟩ := bound_node before tracker.global.protectedTags data call argument len place
    joint actual sourceLoan sourcePointer call.sourceId sourcePointerAt sourceId sourceAllocation sourcePresent
  obtain ⟨returnNode, returnNodeAt, _, _⟩ := bound_node before tracker.global.protectedTags data call argument len place
    joint actual returnLoan returnPointer call.returnId returnPointerAt returnId returnAllocation returnPresent
  have sourceProvenance : match sourcePointer.value.provenance with
      | .concrete _ tag => tag = sourceNode.tag
      | .wildcard => sourceNode.isExposed = true := by
    cases h : sourcePointer.value.provenance with
    | concrete id tag =>
      simp only [h] at sourceBinds
      exact sourceBinds.2
    | wildcard => simpa [h] using sourceBinds
  have lengthEq := actual.2.1
  have lengthPositive : 0 < call.length := by omega
  obtain ⟨sourceBounds, offsetEq, lengthNat, sumEq, sourceOwned⟩ :=
    CandidateCurrentWindowAuthority.nat_window sourceAllocation tracker.global.protectedTags sourcePrecise sourcePointer
      call.sourceId call.sourceOffset call.length .mut lengthPositive (by decide) sourceRuntime.formed.well sourceRoom sourceRights
  have lengthUInt : UInt64.ofNat call.length = len := by apply UInt64.toNat_inj.mp;omega
  rw [lengthUInt] at sourceOwned sumEq
  have bounds : (UInt64.ofNat call.sourceOffset).toNat+len.toNat ≤ sourceAllocation.extra.locations.size.bytes.toNat := by omega
  obtain ⟨returnBounds, returnOffsetEq, _, returnSumEq, returnOwned⟩ :=
    CandidateCurrentWindowAuthority.nat_window returnAllocation tracker.global.protectedTags returnPrecise returnPointer
      call.returnId call.returnOffset 1 .ret (by omega) (by decide) returnRuntime.formed.well returnRoom returnRights
  have one : UInt64.ofNat 1 = (1 : UInt64) := rfl
  rw [one] at returnSumEq returnOwned
  have boolBounds : (UInt64.ofNat call.returnOffset).toNat+1 ≤ returnAllocation.extra.locations.size.bytes.toNat := by omega
  have nonzero : len ≠ 0 := by intro h; simp [h] at positive
  obtain ⟨metadataOutput,metadataActual,_,_,_,_,_,metadataChild,metadataLookup,_,_,metadata,metadataNode⟩ :=
    source_only sourceAllocation.extra tracker.global frame call.sourceId sourcePrecise.completion sourceRuntime shapeComplete
      sourceOrder sourcePointer sourceNode sourceNodeAt sourceProvenance tagRoom nodeRoom short (UInt64.ofNat call.sourceOffset)
      len nonzero bounds sourceOwned
  by_cases same : call.sourceId = call.returnId
  · have allocationEq := CandidateCurrentUniformOwnerWindow.same_id (ActualWorld before).toList joint.shape.1
      call.sourceId sourceAllocation returnAllocation sourcePresent (by rw [same];exact returnPresent)
    have preciseEq := CandidateCurrentUniformOwnerWindow.same_id data.interpretation.precise.toList joint.shape.2.1
      call.sourceId sourcePrecise returnPrecise sourcePreciseAt (by rw [same];exact returnPreciseAt)
    subst returnAllocation
    subst returnPrecise
    have disjoint : ∀ point : UInt64,  (UInt64.ofNat call.returnOffset).toNat ≤ point.toNat →
        point.toNat < (UInt64.ofNat call.returnOffset+1).toNat →
        point.toNat < (UInt64.ofNat call.sourceOffset).toNat ∨
          (UInt64.ofNat call.sourceOffset+len).toNat ≤ point.toNat := by
      intro point lower upper
      apply Classical.byContradiction
      intro bad
      have overlap : call.sourceOffset ≤ point.toNat ∧ point.toNat < call.sourceOffset+call.length := by omega
      exact source_return_disjoint data.interpretation call joint.contents claims (call.sourceId, point.toNat)
        ⟨rfl, overlap⟩ ⟨same, by omega, by omega⟩
    obtain ⟨output, ok, tagEq, globalEq, readDone, childDone, afterRuntime, _, child, childLookup, afterComplete, childOwned, boolAfter⟩ :=
      same_allocation sourceAllocation.extra tracker.global frame call.sourceId sourcePrecise.completion sourceRuntime shapeComplete
        sourceOrder sourcePointer sourceNode sourceNodeAt sourceProvenance tagRoom nodeRoom short (UInt64.ofNat call.sourceOffset)
        len nonzero bounds sourceOwned returnPointer.grant returnNode returnNodeAt (UInt64.ofNat call.returnOffset)
        boolBounds disjoint returnOwned
    have metadataEq : metadataOutput = output := Except.ok.inj (metadataActual.symm.trans ok)
    subst metadataOutput
    have metadataChildEq : metadataChild = child := Option.some.inj (metadataLookup.symm.trans childLookup)
    subst metadataChild
    exact ⟨{
      sourcePointer := sourcePointer
      returnPointer := returnPointer
      sourceAllocation := sourceAllocation
      returnAllocation := sourceAllocation
      sourcePrecise := sourcePrecise
      returnPrecise := sourcePrecise
      sourceLoan := sourceLoan
      returnLoan := returnLoan
      output := output
      child := child
      argument_eq := argumentEq
      place_eq := placeEq
      sourceLoanAt := sourceLoanAt
      returnLoanAt := returnLoanAt
      sourcePointerAt := sourcePointerAt
      returnPointerAt := returnPointerAt
      sourceId := sourceId
      returnId := returnId
      sourcePresent := sourcePresent
      returnPresent := returnPresent
      sourcePreciseAt := sourcePreciseAt
      returnPreciseAt := returnPreciseAt
      actual := ok
      tag := tagEq
      readCompleted := readDone
      childCompleted := childDone
      runtime := afterRuntime
      tagRoom := tagRoom
      outputGlobal := globalEq
      outputCapacity := metadata.capacity
      outputGrowth := metadata.growth
      outputOrder := metadata.order
      oldNodes := metadata.old
      childLookup := childLookup
      childNode := metadataNode
      completes := afterComplete
      sourceOwned := childOwned
      boolOwned := by simpa only [same, ite_true] using boolAfter
    }⟩
  · obtain ⟨output, ok, tagEq, globalEq, readDone, childDone, afterRuntime, child, childLookup, afterComplete, childOwned,_⟩ :=
      source_only sourceAllocation.extra tracker.global frame call.sourceId sourcePrecise.completion sourceRuntime shapeComplete
        sourceOrder sourcePointer sourceNode sourceNodeAt sourceProvenance tagRoom nodeRoom short (UInt64.ofNat call.sourceOffset)
        len nonzero bounds sourceOwned
    have metadataEq : metadataOutput = output := Except.ok.inj (metadataActual.symm.trans ok)
    subst metadataOutput
    have metadataChildEq : metadataChild = child := Option.some.inj (metadataLookup.symm.trans childLookup)
    subst metadataChild
    have flags : ∀ index node,  returnAllocation.extra.nodes.get index = some node →
        output.global.protectedTags.contains node.tag = tracker.global.protectedTags.contains node.tag := by
      intro index node present
      have older := GeneralBorrowParentTagInvariant.parent_below_fresh returnAllocation.extra tracker.global returnRuntime index node present
      have different : node.tag ≠ tracker.global.nextPointerTag := by intro h;rw [h] at older;exact (UInt64.lt_irrefl _ older)
      rw [globalEq]
      exact ProtectorInsertion.contains_other tracker.global.protectedTags tracker.global.nextPointerTag node.tag .StrongProtector different
    have boolAfter : OwnedOn (Authority returnAllocation.extra returnPrecise.completion output.global.protectedTags returnPointer.grant)
        (UInt64.ofNat call.returnOffset) (UInt64.ofNat call.returnOffset+1) returnAllocation.extra.locations := by
      intro position valid nonempty start stop index node present
      rw [flags index node present]
      exact returnOwned position valid nonempty start stop index node present
    exact ⟨{
      sourcePointer := sourcePointer
      returnPointer := returnPointer
      sourceAllocation := sourceAllocation
      returnAllocation := returnAllocation
      sourcePrecise := sourcePrecise
      returnPrecise := returnPrecise
      sourceLoan := sourceLoan
      returnLoan := returnLoan
      output := output
      child := child
      argument_eq := argumentEq
      place_eq := placeEq
      sourceLoanAt := sourceLoanAt
      returnLoanAt := returnLoanAt
      sourcePointerAt := sourcePointerAt
      returnPointerAt := returnPointerAt
      sourceId := sourceId
      returnId := returnId
      sourcePresent := sourcePresent
      returnPresent := returnPresent
      sourcePreciseAt := sourcePreciseAt
      returnPreciseAt := returnPreciseAt
      actual := ok
      tag := tagEq
      readCompleted := readDone
      childCompleted := childDone
      runtime := afterRuntime
      tagRoom := tagRoom
      outputGlobal := globalEq
      outputCapacity := metadata.capacity
      outputGrowth := metadata.growth
      outputOrder := metadata.order
      oldNodes := metadata.old
      childLookup := childLookup
      childNode := metadataNode
      completes := afterComplete
      sourceOwned := childOwned
      boolOwned := by simpa only [same, ite_false] using boolAfter
    }⟩

/-- Positive FnEntry borrowing from the current resource candidate and existing
physical runtime/resources. Both pointer origins and allocation relationships
are chosen from this one actual call, including disjoint same-allocation Bool. -/
theorem invoke (options : Miri.Input.EvalConfigurationCore.Options)
    (limits : Miri.Interpreter.ExecutionMachine.Limits) (remaining : Nat)
    (before : Before) (tracker : Miri.Interpreter.MachineHooks.BorrowState)
    (frame : FrameState) (argument : DuplicatePrefixSliceArgument.Argument) (len : UInt64)
    (place : Miri.Interpreter.MPlaceTy Provenance) (call : CallLoans) (data : Identities)
    (joint : CandidateCurrentGrantResources.Joint (ActualWorld before) tracker.global.protectedTags data.interpretation)
    (actual : ActualBindings before argument len place tracker.global.protectedTags call data)
    (normalized : NormalizedWindows before argument len place call data)
    (claims : Claims data.interpretation call) (positive : 0 < len.toNat)
    (state : DuplicatePrefixRuntimeInput.OrderedState before tracker)
    (resources : DuplicatePrefixCallSpecification.Resources options limits remaining before tracker len) :
    Nonempty (Result before tracker frame argument len place call data) :=
  invoke_from_live before tracker frame argument len place call data joint actual normalized claims positive
    (CandidateCurrentLiveRuntime.tag_room options limits remaining before tracker len resources)
    (CandidateCurrentLiveRuntime.live options limits remaining before tracker len state resources)

end DuplicatePrefix.CandidateCurrentFnEntryRaw

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CandidateCurrentFnEntryRaw." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved current FnEntry raw dependency {dependency}"
