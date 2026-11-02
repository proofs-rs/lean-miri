import duplicate_prefix.CurrentCallResourceDefaultBoolFrame
import duplicate_prefix.CurrentCallResourceAsMutBoolFrame
import duplicate_prefix.CurrentCallResourceLenBoolCurrent
import duplicate_prefix.CurrentCallResourceSameHeap
namespace DuplicatePrefix.CurrentCallResourceAsMutBoolCurrent
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization CurrentCallResourceEntryBody
open GeneralRangeMapOrigins CurrentCallResourceAsMutInvoke
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section
private def at_id {before tracker data owner oldId offset length mode}
    (B : UniformWindow before tracker data owner oldId offset length mode) (newId : AllocId) (same : oldId=newId) :
    UniformWindow before tracker data owner newId offset length mode where
  loan:=B.loan;pointer:=B.pointer;allocation:=B.allocation;precise:=B.precise
  loanAt:=B.loanAt;pointerAt:=B.pointerAt;pointerId:=B.pointerId.trans same
  present:=by rw [←same];exact B.present
  preciseAt:=by rw [←same];exact B.preciseAt
  binding:=B.binding;issued:=by rw [←same];exact B.issued
  parents:=B.parents;window:=by intro byte inside;apply B.window;simpa only [same] using inside

private theorem spatial_at_id {before tracker oldId newId allocation C grant}
    (same : oldId=newId) (old : SpatialDelegation before tracker oldId allocation C grant) :
    SpatialDelegation before tracker newId allocation C grant := by cases same;exact old

private theorem spatial_data {before tracker id first second C D grant}
    (allocation : first=second) (completion : C=D)
    (old : SpatialDelegation before tracker id first C grant) : SpatialDelegation before tracker id second D grant := by
  cases allocation;cases completion;exact old

variable {options remaining span root before tracker data owner id offset len W place limits count}
    {C : Conditions options remaining span #[] root before tracker data owner id offset len W place}
    {out : Output limits C count} {ready : CurrentCallResourceBodyReadiness.Ready C} {nextData nextOwner}
    {Q : UniformWindow (CurrentCallResourceSharedStage.machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ nextData nextOwner id offset len.toNat .mut}
    {stage : CurrentCallResourceSharedResources.Stage Q out.sourceOutput.tag (UInt64.ofNat offset) len (CurrentCallResourceBodyReadiness.current_room out ready)}
    (result : CurrentCallResourceLenReturn.Result out ready Q stage)
    (done : DefaultResult result)

abbrev allocation := if out.physical.id=id then done.current.allocation else CurrentCallResourceLenBoolCurrent.allocation out ready
abbrev completion := if out.physical.id=id then done.current.precise.completion else CurrentCallResourceLenBoolCurrent.completion out ready result

structure DefaultPacket where
  identities : Identities
  holder : Nat
  B : UniformWindow done.machine done.nextTracker identities holder out.physical.id out.physical.offset.toNat 1 .ret
  pointer : B.pointer=CurrentCallResourceBoolCurrent.pointer out
  allocation : B.allocation=allocation result done
  completion : B.precise.completion=completion result done
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra done.nextTracker.global
  distinct : B.allocation.extra.roots.toList.Nodup
  short : B.allocation.extra.nodes.size<65536
  node : TreeNode
  nodeAt : B.allocation.extra.nodes.get B.pointer.grant=some node
  nodeTag : node.tag=out.boolOutput.tag
  nodeParent : node.parent=out.boolNode.parent
  leaf : node.children=#[]
  hidden : node.isExposed=false
  activity : GeneralBorrowFreshActiveWithin.ActiveWithin B.allocation.extra B.pointer.grant .Write out.physical.offset (out.physical.offset+1)
  parentIssued : SpatialDelegation done.machine done.nextTracker out.physical.id B.allocation B.precise.completion C.V.pointer.grant
  parentBinding : PointerBinds B.allocation C.V.pointer
  edge : B.precise.completion.parents[B.pointer.grant.toNat]?=some (some C.V.pointer.grant)

private theorem before_current : ∃bData bOwner,∃B : UniformWindow (beforeDefault result) (CurrentCallResourceLenReturn.postTracker out ready)
    bData bOwner out.physical.id out.physical.offset.toNat 1 .ret,
    B.pointer=CurrentCallResourceBoolCurrent.pointer out ∧B.allocation=CurrentCallResourceLenBoolCurrent.allocation out ready ∧
    B.precise.completion=CurrentCallResourceLenBoolCurrent.completion out ready result := by
  obtain ⟨bData,bOwner,B,pointer,allocation,completion⟩:=CurrentCallResourceLenBoolCurrent.current out ready result
  exact ⟨bData,bOwner,CurrentCallResourceSameHeap.window (before:=result.machine) (after:=beforeDefault result) rfl B,pointer,allocation,completion⟩

private theorem q_bounds : (UInt64.ofNat offset).toNat=offset ∧
    (UInt64.ofNat offset).toNat+len.toNat≤done.qWindow.allocation.extra.locations.size.bytes.toNat := by
  have start:=(CurrentCallResourceSharedStage.source_bounds out).1
  have last:=(done.qWindow.window (id,(UInt64.ofNat offset).toNat+len.toNat-1) ⟨rfl,by have p:=C.positive;omega,by have p:=C.positive;omega⟩).1
  have cap:=done.qWindow.issued.capability
  rw [cap.treeExtent,←cap.extent]
  exact ⟨start,by omega⟩

private theorem before_parent : SpatialDelegation (beforeDefault result) (CurrentCallResourceLenReturn.postTracker out ready)
    out.physical.id (CurrentCallResourceLenBoolCurrent.allocation out ready) (CurrentCallResourceLenBoolCurrent.completion out ready result) C.V.pointer.grant :=
  CurrentCallResourceSameHeap.issued (before:=result.machine) (after:=beforeDefault result) rfl (CurrentCallResourceLenBoolCurrent.parent_issued out ready result)

private theorem tags (node : TreeNode) (tag : node.tag=out.boolNode.tag) : result.sourceNode.tag≠node.tag := by
  have older:=GeneralBorrowParentTagInvariant.parent_below_fresh out.sourceOutput.child.tree out.sourceOutput.global out.sourceWitness.runtime
    out.sourceChild out.sourceWitness.node out.sourceWitness.nodeAt
  rw [out.sourceWitness.tag] at older
  intro same
  rw [result.sourceTag,tag,(CurrentCallResourceBoolFacets.current out).2.2.1] at same
  rw [same] at older
  exact UInt64.lt_irrefl _ older
private theorem default_same (same : out.physical.id=id) : Nonempty (DefaultPacket result done) := by
  obtain ⟨bData,bOwner,B,bPointer,bAllocation,bCompletion⟩:=before_current result
  obtain ⟨_,_,⟨oldNode,oldAt,oldTag,oldParent,oldLeaf,oldHidden⟩,oldActivity⟩:=CurrentCallResourceLenBoolFrame.result out ready result
  let V:=at_id B id same
  have oldAllocation : CurrentCallResourceLenBoolCurrent.allocation out ready=done.qWindow.allocation :=
    (CurrentCallResourceLenBoolCurrent.allocation_same out ready same).trans done.qAllocation.symm
  have oldCompletion : CurrentCallResourceLenBoolCurrent.completion out ready result=done.qWindow.precise.completion :=
    (CurrentCallResourceLenBoolCurrent.completion_same out ready result same).trans done.qCompletion.symm
  have allocationEq : V.allocation=done.qWindow.allocation:=bAllocation.trans oldAllocation
  have completionEq : V.precise.completion=done.qWindow.precise.completion:=bCompletion.trans oldCompletion
  have atBool : done.qWindow.allocation.extra.nodes.get V.pointer.grant=some oldNode := by
    rw [←allocationEq]
    change B.allocation.extra.nodes.get B.pointer.grant=some oldNode
    rw [bAllocation,bPointer];exact oldAt
  have activity : GeneralBorrowFreshActiveWithin.ActiveWithin done.qWindow.allocation.extra V.pointer.grant .Write out.physical.offset (out.physical.offset+1) := by
    rw [←allocationEq]
    change GeneralBorrowFreshActiveWithin.ActiveWithin B.allocation.extra B.pointer.grant .Write out.physical.offset (out.physical.offset+1)
    rw [bAllocation,bPointer];exact oldActivity
  have qAt : done.qWindow.allocation.extra.nodes.get done.qWindow.pointer.grant=some result.sourceNode := by
    rw [done.qPointer,done.qAllocation];exact result.sourceAt
  have different : V.pointer.grant≠done.qWindow.pointer.grant := by
    intro equal
    have found:=atBool
    rw [equal] at found
    have nodeEq:result.sourceNode=oldNode:=Option.some.inj (qAt.symm.trans found)
    exact tags result oldNode oldTag (congrArg TreeNode.tag nodeEq)
  have separate : ∀byte,Window id (UInt64.ofNat offset).toNat len.toNat byte→Window id out.physical.offset.toNat 1 byte→False := by
    intro byte source bool
    have originalSame:=out.physicalId.symm.trans same
    exact C.separate originalSame byte
      ⟨source.1,by rw [←(q_bounds result done).1];exact source.2.1,by rw [←(q_bounds result done).1];exact source.2.2⟩
      ⟨bool.1.trans originalSame.symm,by rw [←out.physicalOffset];exact bool.2.1,by rw [←out.physicalOffset];exact bool.2.2⟩
  have concrete : done.qWindow.pointer.value.provenance=.concrete id out.sourceOutput.tag := by rw [done.qPointer,done.address];rfl
  have nonzero : len≠0 := by intro zero;have positive:=C.positive;rw [zero] at positive;cases positive
  obtain ⟨newData,newB,newPointer,newLoan,newAllocation,newCompletion⟩:=CurrentCallResourceDefaultBoolFrame.current done.qWindow done.qRuntime out.sourceOutput.tag concrete done.room
    done.qDistinct (by have h:=done.qMargin;omega) (by have h:=done.qMargin;omega) (UInt64.ofNat offset) len rfl rfl nonzero (q_bounds result done).2
    done.stage out.physical.offset V allocationEq completionEq separate oldNode atBool oldLeaf oldHidden different activity
    (sourceEntry (out:=out) (ready:=ready)) done.qAllocation
  obtain ⟨_,⟨node,nodeAt,nodeTag,nodeParent,nodeLeaf,nodeHidden⟩,nodeActivity⟩:=CurrentCallResourceDefaultBoolFrame.same done.qWindow done.qRuntime out.sourceOutput.tag concrete done.room
    done.qDistinct (by have h:=done.qMargin;omega) (by have h:=done.qMargin;omega) (UInt64.ofNat offset) len rfl rfl nonzero (q_bounds result done).2
    done.stage out.physical.offset V allocationEq completionEq separate oldNode atBool oldLeaf oldHidden different activity
  let current:=CurrentCallResourceSameHeap.window
    (before:=defaultMachine (beforeDefault result) (CurrentCallResourceLenReturn.postTracker out ready) done.room id (sourceEntry (out:=out) (ready:=ready))
      (defaultTree done.qWindow out.sourceOutput.tag (UInt64.ofNat offset) len)) (after:=done.machine)
    (congrArg (fun machine : Before=>machine.memory) done.machineEq) (at_id newB out.physical.id same.symm)
  have currentPointer : current.pointer=CurrentCallResourceBoolCurrent.pointer out := newPointer.trans bPointer
  have aEq : current.allocation=done.current.allocation:=newAllocation.trans done.allocation.symm
  have cEq : current.precise.completion=done.current.precise.completion:=newCompletion.trans done.completion.symm
  have initialIssued:=spatial_at_id same (spatial_data oldAllocation oldCompletion (before_parent result))
  have installedIssued:=CurrentCallResourceDefaultBoolFrame.license done.qWindow out.sourceOutput.tag done.room (UInt64.ofNat offset) len done.stage
    (sourceEntry (out:=out) (ready:=ready)) done.qAllocation initialIssued
  have parentIssued := spatial_at_id same.symm (CurrentCallResourceSameHeap.issued
    (before:=defaultMachine (beforeDefault result) (CurrentCallResourceLenReturn.postTracker out ready) done.room id (sourceEntry (out:=out) (ready:=ready))
      (defaultTree done.qWindow out.sourceOutput.tag (UInt64.ofNat offset) len)) (after:=done.machine)
    (congrArg (fun machine : Before=>machine.memory) done.machineEq) installedIssued)
  have oldBinding : PointerBinds done.qWindow.allocation C.V.pointer := by rw [←oldAllocation];exact CurrentCallResourceLenBoolCurrent.parent_binding out ready result
  have installedBinding:=CurrentCallResourceDefaultBoolFrame.old_binding done.qWindow out.sourceOutput.tag done.room (UInt64.ofNat offset) len done.stage C.V.pointer oldBinding
  have initialEdge:=CurrentCallResourceLenBoolCurrent.edge out ready result
  rw [oldCompletion] at initialEdge
  have installedEdge:=CurrentCallResourceDefaultBoolFrame.old_edge done.qWindow out.sourceOutput.tag done.room (UInt64.ofNat offset) len done.stage out.boolChild C.V.pointer.grant initialEdge
  refine ⟨{
    identities:=newData,holder:=bOwner,B:=current,pointer:=currentPointer
    allocation:=by simpa only [allocation,ite_eq_left same] using aEq
    completion:=by simpa only [completion,ite_eq_left same] using cEq
    runtime:=?_,distinct:=?_,short:=?_,node:=node,nodeAt:=?_,nodeTag:=nodeTag.trans (oldTag.trans out.boolNodeTag)
    nodeParent:=nodeParent.trans oldParent,leaf:=nodeLeaf.trans oldLeaf,hidden:=nodeHidden.trans oldHidden
    activity:=?_,parentIssued:=?_,parentBinding:=?_,edge:=?_}⟩
  · change DuplicatePrefixBorrowContract.RuntimeFacts newB.allocation.extra done.nextTracker.global
    rw [newAllocation]
    exact done.stage.runtime
  · change newB.allocation.extra.roots.toList.Nodup
    rw [newAllocation]
    change (defaultTree done.qWindow out.sourceOutput.tag (UInt64.ofNat offset) len).roots.toList.Nodup
    rw [done.stage.roots];exact done.qDistinct
  · change newB.allocation.extra.nodes.size<65536
    rw [newAllocation]
    change (defaultTree done.qWindow out.sourceOutput.tag (UInt64.ofNat offset) len).nodes.size<65536
    have growth:=done.stage.growth
    change (defaultTree done.qWindow out.sourceOutput.tag (UInt64.ofNat offset) len).nodes.size≤done.qWindow.allocation.extra.nodes.size+1 at growth
    have room:=done.qMargin;omega
  · change newB.allocation.extra.nodes.get newB.pointer.grant=some node
    rw [newAllocation,newPointer];exact nodeAt
  · change GeneralBorrowFreshActiveWithin.ActiveWithin newB.allocation.extra newB.pointer.grant .Write out.physical.offset (out.physical.offset+1)
    rw [newAllocation,newPointer];exact nodeActivity
  · exact spatial_data newAllocation.symm newCompletion.symm parentIssued
  · change PointerBinds newB.allocation C.V.pointer
    rw [newAllocation];exact installedBinding
  · change newB.precise.completion.parents[newB.pointer.grant.toNat]?=some (some C.V.pointer.grant)
    rw [newCompletion,newPointer]
    change _[B.pointer.grant.toNat]?=_
    rw [bPointer]
    exact installedEdge
private theorem default_different (different : out.physical.id≠id) : Nonempty (DefaultPacket result done) := by
  obtain ⟨bData,bOwner,B,bPointer,bAllocation,bCompletion⟩:=before_current result
  obtain ⟨_,_,⟨node,nodeAt,nodeTag,nodeParent,nodeLeaf,nodeHidden⟩,nodeActivity⟩:=CurrentCallResourceLenBoolFrame.result out ready result
  obtain ⟨next,ptr,loan,alloc,comp⟩:=CurrentCallResourceDefaultBoolFrame.different done.qWindow out.sourceOutput.tag done.room (UInt64.ofNat offset) len
    (sourceEntry (out:=out) (ready:=ready)) B different
  let current:=CurrentCallResourceSameHeap.window
    (before:=defaultMachine (beforeDefault result) (CurrentCallResourceLenReturn.postTracker out ready) done.room id (sourceEntry (out:=out) (ready:=ready))
      (defaultTree done.qWindow out.sourceOutput.tag (UInt64.ofNat offset) len)) (after:=done.machine)
    (congrArg (fun machine : Before=>machine.memory) done.machineEq) next
  have currentAllocation : current.allocation=CurrentCallResourceLenBoolCurrent.allocation out ready := by
    change next.allocation=_
    exact alloc.trans bAllocation
  have currentCompletion : current.precise.completion=CurrentCallResourceLenBoolCurrent.completion out ready result :=
    (congrArg PreciseAllocation.completion comp).trans bCompletion
  have initialIssued:=before_parent result
  have installedIssued:=CurrentCallResourceDefaultBoolFrame.different_license done.qWindow out.sourceOutput.tag done.room (UInt64.ofNat offset) len
    (sourceEntry (out:=out) (ready:=ready)) different initialIssued
  have parentIssued:=CurrentCallResourceSameHeap.issued
    (before:=defaultMachine (beforeDefault result) (CurrentCallResourceLenReturn.postTracker out ready) done.room id (sourceEntry (out:=out) (ready:=ready))
      (defaultTree done.qWindow out.sourceOutput.tag (UInt64.ofNat offset) len)) (after:=done.machine)
    (congrArg (fun machine : Before=>machine.memory) done.machineEq) installedIssued
  refine ⟨{
    identities:=bData,holder:=bOwner,B:=current,pointer:=ptr.trans bPointer
    allocation:=by simpa only [allocation,ite_eq_right different] using currentAllocation
    completion:=by simpa only [completion,ite_eq_right different] using currentCompletion
    runtime:=?_,distinct:=?_,short:=?_,node:=node,nodeAt:=?_,nodeTag:=nodeTag.trans out.boolNodeTag
    nodeParent:=nodeParent,leaf:=nodeLeaf,hidden:=nodeHidden,activity:=?_,parentIssued:=?_,parentBinding:=?_,edge:=?_}⟩
  · change DuplicatePrefixBorrowContract.RuntimeFacts next.allocation.extra done.nextTracker.global
    rw [alloc,bAllocation]
    exact CurrentCallResourceDefaultBoolFrame.advance_runtime done.room _ (CurrentCallResourceLenBoolCurrent.runtime out ready result)
  · change next.allocation.extra.roots.toList.Nodup
    rw [alloc,bAllocation];exact CurrentCallResourceLenBoolCurrent.roots out ready result
  · change next.allocation.extra.nodes.size<65536
    rw [alloc,bAllocation];exact CurrentCallResourceLenBoolCurrent.short out ready result
  · change next.allocation.extra.nodes.get next.pointer.grant=some node
    rw [alloc,bAllocation,ptr,bPointer];exact nodeAt
  · change GeneralBorrowFreshActiveWithin.ActiveWithin next.allocation.extra next.pointer.grant .Write out.physical.offset (out.physical.offset+1)
    rw [alloc,bAllocation,ptr,bPointer];exact nodeActivity
  · exact spatial_data currentAllocation.symm currentCompletion.symm parentIssued
  · change PointerBinds next.allocation C.V.pointer
    rw [alloc,bAllocation];exact CurrentCallResourceLenBoolCurrent.parent_binding out ready result
  · change next.precise.completion.parents[next.pointer.grant.toNat]?=some (some C.V.pointer.grant)
    rw [comp,bCompletion,ptr,bPointer]
    exact CurrentCallResourceLenBoolCurrent.edge out ready result

/-- Current Bool resources at the SAME actual accepted Default statement
output. All before/after resources are derived from the Len/Default producers. -/
theorem of_default : Nonempty (DefaultPacket result done) := by
  by_cases same : out.physical.id=id
  · exact default_same result done same
  · exact default_different result done same

variable (fresh : done.nextTracker.global.nextPointerTag.value<18446744073709551615)
    (valid15 : (15 : Miri.MIR.LocalId)<done.frame.locals.size)
    (seed : CurrentCallResourceAsMutCall.Seed options limits remaining span done.current done.entry done.frame done.base
      (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15)
    (returned : CurrentCallResourceAsMutReturn.Returned done.current done.entry done.frame done.base
      (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed)

abbrev finalTracker := CurrentCallResourceAsMutReturn.postTracker done.current done.entry done.frame done.base
  (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed
abbrev finalTree := CurrentCallResourceAsMutReturn.releasedTree done.current done.entry done.frame done.base
  (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed
abbrev finalCompletion := CurrentCallResourceAsMutReturn.completion done.current done.entry done.frame done.base
  (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed

abbrev finalAllocation := if out.physical.id=id then done.current.allocation.setExtra (finalTree result done fresh valid15 seed) else CurrentCallResourceLenBoolCurrent.allocation out ready
abbrev finalC := if out.physical.id=id then finalCompletion result done fresh valid15 seed else CurrentCallResourceLenBoolCurrent.completion out ready result

structure Packet where
  identities : Identities
  holder : Nat
  B : UniformWindow returned.machine (finalTracker result done fresh valid15 seed) identities holder out.physical.id out.physical.offset.toNat 1 .ret
  pointer : B.pointer=CurrentCallResourceBoolCurrent.pointer out
  allocation : B.allocation=finalAllocation result done fresh valid15 seed
  completion : B.precise.completion=finalC result done fresh valid15 seed
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra (finalTracker result done fresh valid15 seed).global
  distinct : B.allocation.extra.roots.toList.Nodup
  short : B.allocation.extra.nodes.size<65536
  node : TreeNode
  nodeAt : B.allocation.extra.nodes.get B.pointer.grant=some node
  nodeTag : node.tag=out.boolOutput.tag
  older : node.tag.value<seed.output.tag.value
  nodeParent : node.parent=out.boolNode.parent
  leaf : node.children=#[]
  hidden : node.isExposed=false
  activity : GeneralBorrowFreshActiveWithin.ActiveWithin B.allocation.extra B.pointer.grant .Write out.physical.offset (out.physical.offset+1)
  parentIssued : SpatialDelegation returned.machine (finalTracker result done fresh valid15 seed) out.physical.id B.allocation B.precise.completion C.V.pointer.grant
  parentBinding : PointerBinds B.allocation C.V.pointer
  edge : B.precise.completion.parents[B.pointer.grant.toNat]?=some (some C.V.pointer.grant)

private theorem bool_older (P : DefaultPacket result done) : out.boolOutput.tag.value<seed.output.tag.value := by
  rw [seed.tag,←P.nodeTag]
  exact GeneralBorrowParentTagInvariant.parent_below_fresh _ _ P.runtime _ _ P.nodeAt

private theorem final_different (P : DefaultPacket result done) (different : out.physical.id≠id) :
    Nonempty (Packet result done fresh valid15 seed returned) := by
  obtain ⟨B,ptr,loan,alloc,comp⟩:=CurrentCallResourceAsMutBoolFrame.different done.current done.entry done.frame done.base
    (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed returned P.B different
  have issued:=CurrentCallResourceAsMutBoolFrame.different_license done.current done.entry done.frame done.base
    (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed returned different P.parentIssued
  refine ⟨{
    identities:=P.identities,holder:=P.holder,B:=B,pointer:=ptr.trans P.pointer,
    allocation:=by simpa only [finalAllocation,ite_eq_right different,allocation,ite_eq_right different] using alloc.trans P.allocation
    completion:=by simpa only [finalC,ite_eq_right different,completion,ite_eq_right different] using (congrArg PreciseAllocation.completion comp).trans P.completion
    runtime:=?_,distinct:=?_,short:=?_,node:=P.node,nodeAt:=?_,nodeTag:=P.nodeTag,older:=by rw [P.nodeTag];exact bool_older result done fresh valid15 seed P
    nodeParent:=P.nodeParent,
    leaf:=P.leaf,hidden:=P.hidden,activity:=?_,parentIssued:=?_,parentBinding:=?_,edge:=?_}⟩
  · rw [alloc];exact CurrentCallResourceAsMutBoolFrame.different_runtime done.current done.entry done.frame done.base
      (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed _ P.runtime
  · rw [alloc];exact P.distinct
  · rw [alloc];exact P.short
  · rw [alloc,ptr];exact P.nodeAt
  · rw [alloc,ptr];exact P.activity
  · exact spatial_data alloc.symm (congrArg PreciseAllocation.completion comp).symm issued
  · rw [alloc];exact P.parentBinding
  · rw [comp,ptr];exact P.edge

private theorem final_same (P : DefaultPacket result done) (same : out.physical.id=id) :
    Nonempty (Packet result done fresh valid15 seed returned) := by
  let V:=at_id P.B id same
  have aEq : V.allocation=done.current.allocation := by
    change P.B.allocation=done.current.allocation
    simpa only [allocation,ite_eq_left same] using P.allocation
  have cEq : V.precise.completion=done.current.precise.completion := by
    change P.B.precise.completion=done.current.precise.completion
    simpa only [completion,ite_eq_left same] using P.completion
  have nodeAt : done.current.allocation.extra.nodes.get V.pointer.grant=some P.node := by rw [←aEq];exact P.nodeAt
  have active : GeneralBorrowFreshActiveWithin.ActiveWithin done.current.allocation.extra V.pointer.grant .Write out.physical.offset (out.physical.offset+1) := by rw [←aEq];exact P.activity
  have different : V.pointer.grant≠done.current.pointer.grant := by
    have oldAllocation : CurrentCallResourceLenBoolCurrent.allocation out ready=done.qWindow.allocation :=
      (CurrentCallResourceLenBoolCurrent.allocation_same out ready same).trans done.qAllocation.symm
    obtain ⟨_,_,⟨oldNode,oldAt,oldTag,_,_,_⟩,_⟩:=CurrentCallResourceLenBoolFrame.result out ready result
    have oldAtQ : done.qWindow.allocation.extra.nodes.get out.boolChild=some oldNode := by rw [←oldAllocation];exact oldAt
    have below:=GeneralBorrowParentTagInvariant.parent_below_fresh _ _ done.qRuntime _ _ oldAtQ
    have oldTagEq : oldNode.tag=out.boolOutput.tag := oldTag.trans out.boolNodeTag
    rw [oldTagEq] at below
    intro equal
    have found:=nodeAt
    rw [equal,done.pointer] at found
    have pAt : done.current.allocation.extra.nodes.get done.stage.childIndex=some done.stage.node := by rw [done.allocation];exact done.stage.nodeAt
    have nodes : P.node=done.stage.node:=Option.some.inj (found.symm.trans pAt)
    have tagsEq:=congrArg TreeNode.tag nodes
    rw [P.nodeTag,done.stage.nodeTag] at tagsEq
    rw [tagsEq] at below
    exact UInt64.lt_irrefl _ below
  have separate : ∀byte,Window id (UInt64.ofNat offset).toNat len.toNat byte→Window id out.physical.offset.toNat 1 byte→False := by
    intro byte source bool
    have originalSame:=out.physicalId.symm.trans same
    exact C.separate originalSame byte
      ⟨source.1,by rw [←(q_bounds result done).1];exact source.2.1,by rw [←(q_bounds result done).1];exact source.2.2⟩
      ⟨bool.1.trans originalSame.symm,by rw [←out.physicalOffset];exact bool.2.1,by rw [←out.physicalOffset];exact bool.2.2⟩
  have short : done.current.allocation.extra.nodes.size<65536 := by have h:=done.margin;omega
  have room : done.current.allocation.extra.nodes.size+1≤4294967295 := by omega
  obtain ⟨newData,B,ptr,loan,alloc,comp⟩:=CurrentCallResourceAsMutBoolFrame.current done.current done.entry done.frame done.base
    (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed returned
    out.physical.offset V aEq cEq separate short room P.node nodeAt P.leaf P.hidden different active
  obtain ⟨_,⟨node,atNode,tag,parent,leaf,hidden⟩,activity⟩:=CurrentCallResourceAsMutBoolFrame.same done.current done.entry done.frame done.base
    (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed
    out.physical.offset V aEq cEq separate short room P.node nodeAt P.leaf P.hidden different active
  let current:=at_id B out.physical.id same.symm
  have oldIssued:=spatial_at_id same (spatial_data aEq cEq P.parentIssued)
  have installed:=CurrentCallResourceAsMutBoolFrame.license done.current done.entry done.frame done.base
    (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed returned oldIssued
  have binding:=CurrentCallResourceAsMutBoolFrame.old_binding done.current done.entry done.frame done.base
    (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed C.V.pointer
    (by rw [←aEq];exact P.parentBinding)
  have oldEdge : done.current.precise.completion.parents[V.pointer.grant.toNat]?=some (some C.V.pointer.grant) := by rw [←cEq];exact P.edge
  have edge:=CurrentCallResourceAsMutBoolFrame.old_edge done.current done.entry done.frame done.base
    (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed V.pointer.grant C.V.pointer.grant oldEdge
  refine ⟨{
    identities:=newData,holder:=P.holder,B:=current,pointer:=ptr.trans P.pointer,
    allocation:=by change B.allocation=finalAllocation result done fresh valid15 seed;simpa only [finalAllocation,finalTree,ite_eq_left same] using alloc
    completion:=by change B.precise.completion=finalC result done fresh valid15 seed;simpa only [finalC,finalCompletion,ite_eq_left same] using comp
    runtime:=?_,distinct:=?_,short:=?_,node:=node,nodeAt:=?_,nodeTag:=tag.trans P.nodeTag,older:=by rw [tag,P.nodeTag];exact bool_older result done fresh valid15 seed P
    nodeParent:=parent.trans P.nodeParent,
    leaf:=leaf.trans P.leaf,hidden:=hidden.trans P.hidden,activity:=?_,parentIssued:=?_,parentBinding:=?_,edge:=?_}⟩
  · change DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra _
    rw [alloc];exact CurrentCallResourceAsMutReturn.runtime_end_call done.current done.entry done.frame done.base
      (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed
  · change B.allocation.extra.roots.toList.Nodup
    rw [alloc];exact CurrentCallResourceAsMutBoolFrame.roots done.current done.entry done.frame done.base
      (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed
  · change B.allocation.extra.nodes.size<65536
    rw [alloc];exact CurrentCallResourceAsMutBoolFrame.short done.current done.entry done.frame done.base
      (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed
  · change B.allocation.extra.nodes.get B.pointer.grant=some node
    rw [alloc,ptr];exact atNode
  · change GeneralBorrowFreshActiveWithin.ActiveWithin B.allocation.extra B.pointer.grant .Write out.physical.offset (out.physical.offset+1)
    rw [alloc,ptr];exact activity
  · exact spatial_data alloc.symm comp.symm (spatial_at_id same.symm installed)
  · change PointerBinds B.allocation C.V.pointer
    rw [alloc];exact binding
  · change B.precise.completion.parents[B.pointer.grant.toNat]?=some (some C.V.pointer.grant)
    rw [comp,ptr];exact edge

/-- Bool resources after the actual Default statement, Strong helper, release,
and helper pop. The producer derives both allocation cases internally. -/
theorem invoke : Nonempty (Packet result done fresh valid15 seed returned) := by
  obtain ⟨P⟩:=of_default result done
  by_cases same : out.physical.id=id
  · exact final_same result done fresh valid15 seed returned P same
  · exact final_different result done fresh valid15 seed returned P same
end
end DuplicatePrefix.CurrentCallResourceAsMutBoolCurrent

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceAsMutBoolCurrent" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual Bool packet dependency {dependency}"
