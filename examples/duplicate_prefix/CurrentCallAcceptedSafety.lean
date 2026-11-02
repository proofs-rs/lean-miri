import duplicate_prefix.CurrentCallAcceptedCopyPrefix
import duplicate_prefix.CurrentCallCopyBoolWindow
import duplicate_prefix.RootSuccessToReturn
import duplicate_prefix.CurrentCallLenRootData
import duplicate_prefix.CurrentCallEntryRootRelease
import duplicate_prefix.CurrentCallRootReturn
import duplicate_prefix.SuccessfulTraceTerminal
import duplicate_prefix.S04FinalReturnRuleAccounting
namespace DuplicatePrefix.CurrentCallAcceptedSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext CurrentCallLen
open CandidateStableCallOwnership GeneralBorrowProjection S05ConcreteProtectedChildCompletion GeneralRangeMapOrigins
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
private theorem tick_model (options remaining span machine)
    (model : DuplicatePrefixCallModel.Model options remaining span machine) :
    DuplicatePrefixCallModel.Model options remaining span (RootZeroCompleteState.tick options remaining span machine) := by
  have flags := RootZeroCompleteState.tick_flags options remaining span machine
  have unchecked := model.unchecked
  have noGc := model.noGc
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators] at unchecked noGc
  unfold RootZeroCompleteState.tick SourceControl.accounted at flags ⊢
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators] at flags ⊢
  exact {model with unchecked := by rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]; exact flags.1.trans unchecked, noGc := by rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]; exact flags.2.trans noGc}

private theorem release_current {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    {count : UInt64} (s : SharedStage input count) (positive : 0 < len.toNat)
    (post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (held : MachineHooks.BorrowState)
    (qEntry bEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (qCompletion bCompletion : Completion)
    (qLive : post.memory.live.find? (fun row => row.1 == call.sourceId)=some (call.sourceId,qEntry))
    (bLive : post.memory.live.find? (fun row => row.1 == call.returnId)=some (call.returnId,bEntry))
    (qRuntime : DuplicatePrefixBorrowContract.RuntimeFacts qEntry.allocation.extra held.global)
    (bRuntime : DuplicatePrefixBorrowContract.RuntimeFacts bEntry.allocation.extra held.global)
    (qComplete : Completes qEntry.allocation.extra qCompletion) (bComplete : Completes bEntry.allocation.extra bCompletion)
    (qOrder : GeneralBorrowWildcardParentTagOrder.ParentTagOrder qEntry.allocation.extra)
    (bOrder : GeneralBorrowWildcardParentTagOrder.ParentTagOrder bEntry.allocation.extra)
    (sameCompletion : call.sourceId=call.returnId → bCompletion=qCompletion)
    (qNode bNode oldNode : TreeNode)
    (qAt : qEntry.allocation.extra.nodeAt s.out.source.base.raw.child=some qNode)
    (bAt : bEntry.allocation.extra.nodeAt s.out.borrowed.child=some bNode)
    (oldAt : bEntry.allocation.extra.nodeAt s.out.source.base.raw.returnPointer.grant=some oldNode)
    (original : match s.out.source.base.raw.returnPointer.value.provenance with
      | .concrete _ tag => tag=oldNode.tag | .wildcard => oldNode.isExposed=true)
    (qTag : qNode.tag=s.out.source.base.raw.output.tag) (bTag : bNode.tag=s.out.borrowed.output.tag)
    (qHidden : qNode.isExposed=false) (bHidden : bNode.isExposed=false) (bLeaf : bNode.children=#[])
    (qActive : GeneralBorrowFreshActiveWithin.ActiveWithin qEntry.allocation.extra s.out.source.base.raw.child .Write
      (UInt64.ofNat call.sourceOffset) (UInt64.ofNat call.sourceOffset+len))
    (bActive : GeneralBorrowFreshActiveWithin.ActiveWithin bEntry.allocation.extra s.out.borrowed.child .Write
      (UInt64.ofNat call.returnOffset) (UInt64.ofNat call.returnOffset+1))
    (qOwned : OwnedOn (S05CompletedAncestryReadMutable.Authority qEntry.allocation.extra qCompletion held.global.protectedTags s.out.source.base.raw.child)
      (UInt64.ofNat call.sourceOffset) (UInt64.ofNat call.sourceOffset+len) qEntry.allocation.extra.locations)
    (bOwned : OwnedOn (S05CompletedAncestryReadMutable.Authority bEntry.allocation.extra bCompletion held.global.protectedTags s.out.borrowed.child)
      (UInt64.ofNat call.returnOffset) (UInt64.ofNat call.returnOffset+1) bEntry.allocation.extra.locations)
    (edge : bCompletion.parents[s.out.borrowed.child.toNat]?=some (some s.out.source.base.raw.returnPointer.grant))
    (qShort : qEntry.allocation.extra.nodes.size<65536) (bShort : bEntry.allocation.extra.nodes.size<65536)
    (absent : call.sourceId≠call.returnId → bEntry.allocation.extra.indexOfTag s.out.source.base.raw.output.tag=none)
    (bounds : (UInt64.ofNat call.returnOffset).toNat+1 ≤ bEntry.allocation.extra.locations.size.bytes.toNat)
    (initial : CurrentCallBoolScalarWrite.Window post place)
    (initialId : initial.id=call.returnId) (initialPtr : initial.pointer=s.out.source.base.raw.returnPointer.value)
    (initialOffset : initial.offset=UInt64.ofNat call.returnOffset)
    (initialBinding : CandidateCallBindings.WindowBinding post initial.pointer initial.id initial.offset.toNat 1) :
    Nonempty (CurrentCallEntryRootRelease.Released post held (CurrentCallEntryRootRelease.Entry.borrowFrame s.out)
      place s.out.source.base.raw.returnPointer.grant call.returnId (UInt64.ofNat call.returnOffset) s.out.source.base.raw.returnPointer.value) := by
  let raw := s.out.source.base.raw
  let frame := CurrentCallEntryRootRelease.Entry.borrowFrame s.out
  have frameTags : frame.protectedTags=#[(call.sourceId,qNode.tag),(call.returnId,bNode.tag)] := by
    simpa only [qTag,bTag] using CurrentCallEntryRootRelease.Entry.frame_tags s.out
  have endpoints := CurrentCallBoolProtection.endpoints (CurrentCallPush.prepared_input input #[]) {} raw positive
  have qPositive : (UInt64.ofNat call.sourceOffset).toNat < (UInt64.ofNat call.sourceOffset+len).toNat := by
    rw [endpoints.1,endpoints.2.2.1];omega
  have bPositive : (UInt64.ofNat call.returnOffset).toNat < (UInt64.ofNat call.returnOffset+1).toNat := by
    rw [endpoints.2.1,endpoints.2.2.2.1];omega
  have output : ∃ memory finalTree,
      StackPopRelease.Plan held.global.protectedTags frame.protectedTags.toList post.memory memory ∧
      memory.live.find? (fun row => row.1 == call.returnId)=some (call.returnId,{bEntry with allocation:=bEntry.allocation.setExtra finalTree}) ∧
      DuplicatePrefixBorrowContract.RuntimeFacts finalTree (held.global.endCall frame) ∧ Completes finalTree bCompletion ∧
      finalTree={bEntry.allocation.extra with locations:=finalTree.locations} ∧
      finalTree.locations.size=bEntry.allocation.extra.locations.size ∧
      OwnedOn (S05CompletedAncestryReadMutable.Authority finalTree bCompletion (held.global.endCall frame).protectedTags raw.returnPointer.grant)
        (UInt64.ofNat call.returnOffset) (UInt64.ofNat call.returnOffset+1) finalTree.locations := by
    by_cases same : call.sourceId=call.returnId
    · have entryEq : qEntry=bEntry := by
        rw [same,bLive] at qLive
        exact (Prod.mk.inj (Option.some.inj qLive)).2.symm
      subst qEntry
      have compEq := sameCompletion same
      rw [←compEq] at qOwned
      have different : s.out.borrowed.child≠raw.child := by
        intro equal
        have atSame : bEntry.allocation.extra.nodes.get raw.child = some bNode := by simpa only [equal,BorrowTree.nodeAt] using bAt
        have nodeEq : bNode=qNode := Option.some.inj (atSame.symm.trans qAt)
        exact CurrentCallEntryProtectionData.source_bool_tags_ne raw s.out.borrowed (qTag.symm.trans (nodeEq ▸ bTag))
      have disjoint : (UInt64.ofNat call.sourceOffset+len).toNat ≤ (UInt64.ofNat call.returnOffset).toNat ∨
          (UInt64.ofNat call.returnOffset+1).toNat ≤ (UInt64.ofNat call.sourceOffset).toNat := by
        by_cases left : (UInt64.ofNat call.sourceOffset+len).toNat ≤ (UInt64.ofNat call.returnOffset).toNat
        · exact .inl left
        by_cases after : (UInt64.ofNat call.sourceOffset).toNat ≤ (UInt64.ofNat call.returnOffset).toNat
        · have impossible := endpoints.2.2.2.2.2 same (UInt64.ofNat call.returnOffset) after (by omega)
          omega
        · have earlier := endpoints.2.2.2.2.2 same (UInt64.ofNat call.sourceOffset) (Nat.le_refl _) qPositive
          exact .inr (by omega)
      let first := bEntry.allocation.extra.releaseProtector qNode.tag held.global.protectedTags
      let second := first.tree.releaseProtector bNode.tag held.global.protectedTags
      let middleEntry := {bEntry with allocation:=bEntry.allocation.setExtra first.tree}
      obtain ⟨plan,runtime,complete,shape,capacity,rights⟩ := CurrentCallRootRelease.same_tree_plan bEntry.allocation.extra held.global bCompletion
        bRuntime bComplete bOrder call.returnId frame raw.child s.out.borrowed.child raw.returnPointer.grant qNode bNode
        qAt bAt qHidden bHidden bLeaf different (by simpa only [same] using frameTags) edge
        (UInt64.ofNat call.sourceOffset) len (UInt64.ofNat call.returnOffset) qPositive bPositive disjoint qActive bActive qOwned bOwned bShort
        post.memory bEntry bLive rfl
      let middle := StackPopRelease.commitTree post.memory call.returnId bEntry first.tree
      let memory := StackPopRelease.commitTree middle call.returnId middleEntry second.tree
      refine ⟨memory,second.tree,plan,?_,runtime,complete,shape,capacity,rights⟩
      simpa only [memory,middleEntry,Allocation.setExtra,Allocation.mapExtra] using StackPopRelease.lookup_commit_same middle call.returnId middleEntry second.tree
    · have hiddenFrame : S04ReturnReleaseParent.HiddenFrame bEntry.allocation.extra frame := by
        intro row member index node present tagged
        rw [frameTags] at member
        change row ∈ [(call.sourceId,qNode.tag),(call.returnId,bNode.tag)] at member
        simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with source | dest
        · subst row
          have mapping := bRuntime.formed.allocator.nodeTags index node present
          rw [tagged,qTag] at mapping
          have impossible := absent same
          change bEntry.allocation.extra.indexOfTag raw.output.tag = some index at mapping
          rw [mapping] at impossible
          cases impossible
        · subst row
          have mapping := bRuntime.formed.allocator.nodeTags index node present
          have actual := bRuntime.formed.allocator.nodeTags s.out.borrowed.child bNode bAt
          rw [tagged,actual] at mapping
          have equal := Option.some.inj mapping
          subst index
          have nodeEq := Option.some.inj (present.symm.trans bAt)
          subst node;exact bHidden
      let first := qEntry.allocation.extra.releaseProtector qNode.tag held.global.protectedTags
      let second := bEntry.allocation.extra.releaseProtector bNode.tag held.global.protectedTags
      let middle := StackPopRelease.commitTree post.memory call.sourceId qEntry first.tree
      let memory := StackPopRelease.commitTree middle call.returnId bEntry second.tree
      obtain ⟨plan,runtime,complete,shape,capacity,rights⟩ := CurrentCallRootRelease.different_trees_plan qEntry.allocation.extra bEntry.allocation.extra held.global
        qCompletion bCompletion qRuntime bRuntime qComplete bComplete qOrder bOrder call.sourceId call.returnId (Ne.symm same) frame
        raw.child s.out.borrowed.child raw.returnPointer.grant qNode bNode qAt bAt qHidden bHidden frameTags hiddenFrame edge
        (UInt64.ofNat call.sourceOffset) len (UInt64.ofNat call.returnOffset) qPositive bPositive qActive bActive qOwned bOwned qShort bShort
        post.memory qEntry bEntry qLive bLive rfl rfl
      exact ⟨memory,second.tree,plan,StackPopRelease.lookup_commit_same middle call.returnId bEntry second.tree,runtime,complete,shape,capacity,rights⟩
  obtain ⟨memory,finalTree,plan,finalLive,runtime,complete,shape,capacity,rights⟩ := output
  let final := ActualPopPlan.released post memory held frame
  obtain ⟨window,ptrSame,idSame,offsetSame,binding⟩ := CurrentCallRootPhysicalWindow.plan held.global.protectedTags frame.protectedTags.toList
    post.memory memory plan post final rfl rfl rfl place initial initialBinding
  have idEq := idSame.trans initialId
  have ptrEq := ptrSame.trans initialPtr
  have offsetEq := offsetSame.trans initialOffset
  have entryEq : window.entry={bEntry with allocation:=bEntry.allocation.setExtra finalTree} := by
    have live := window.live
    rw [idEq] at live
    exact (Prod.mk.inj (Option.some.inj (live.symm.trans finalLive))).2
  have treeEq : window.entry.allocation.extra=finalTree := by rw [entryEq];rfl
  have nodes : finalTree.nodes=bEntry.allocation.extra.nodes := by rw [shape]
  refine ⟨{
    memory := memory
    plan := plan
    window := window
    binding := binding
    roleId := idEq
    roleOffset := offsetEq
    rolePointer := ptrEq
    completion := bCompletion
    runtime := ?_
    completes := ?_
    order := ?_
    short := ?_
    node := oldNode
    present := ?_
    provenance := ?_
    bounds := ?_
    owned := ?_ }⟩
  · rw [treeEq];exact runtime
  · rw [treeEq];exact complete
  · rw [treeEq];exact GeneralBorrowParentTagInvariant.nodes_frame _ _ nodes bOrder
  · rw [treeEq,nodes];exact bShort
  · change window.entry.allocation.extra.nodes.get raw.returnPointer.grant=some oldNode
    rw [treeEq,nodes];exact oldAt
  · rw [ptrEq];exact original
  · rw [treeEq,offsetEq,capacity];exact bounds
  · rw [treeEq,offsetEq];exact rights

private theorem finish {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    {count : UInt64} (s : SharedStage input count) (positive : 0 < len.toNat)
    (result : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (current : MachineHooks.BorrowState) (borrowFrame : FrameState)
    (released : CurrentCallEntryRootRelease.Released machine current borrowFrame place
      s.out.source.base.raw.returnPointer.grant call.returnId (UInt64.ofNat call.returnOffset) s.out.source.base.raw.returnPointer.value)
    (traceBefore : SuccessfulTrace.Trace (config options (remaining+1) span) limits
      (Storage.withCurrent #[] (s.out.frame count) (s.out.machine count)) (Storage.withCurrent #[] result machine))
    (model : DuplicatePrefixCallModel.Model options remaining span machine)
    (memoryReady : CurrentCallBoolProtection.ProfileMemoryReadiness machine call)
    (thread : Miri.Concurrency.ThreadRecord) (activeThread : machine.threads.activeThread?=some thread)
    (tracked : machine.borrowTracker=some current) (frameTracked : result.extra.borrowTracker=some borrowFrame)
    (body : result.body=RootBody.reflected.body.body) (size : result.locals.size=25)
    (located : result.location=.mir ⟨10,0⟩)
    (slot0 : result.locals[0]?=some ⟨.live (.immediate (.scalar (.fromBool true))),some RootCompilerFacts.boolLayout⟩)
    (returnPlace : result.returnPlace=(s.out.frame count).returnPlace)
    (noClocks : result.extra.dataRace=none) (returnStop : result.returnContinuation=.stop true)
    (noVarargs : result.vaList=#[]) (immediate : CopyHelperCleanup.AllImmediate result) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before argument len count place := by
  let cfg := config options (remaining+1) span
  let accounted := S04FinalReturnRuleAccounting.machine options remaining span result machine
  have active : accounted.threads.activeThread? = some thread := activeThread
  let post : RootState := ⟨⟨#[]⟩,GenericPopFrame.afterRelevanceAt #[] result
    (ActualPopPlan.released accounted released.memory current borrowFrame) (thread.topUserRelevantFrame.getD 0)⟩
  have postUser : post.machine.user = accounted.user := by
    unfold post GenericPopFrame.afterRelevanceAt
    split <;> rfl
  have addresses : accounted.user.addresses = machine.user.addresses := by
    unfold accounted S04FinalReturnRuleAccounting.machine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have extras : accounted.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras := by
    unfold accounted S04FinalReturnRuleAccounting.machine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have ghost : accounted.user.payload.ghost = false := by
    unfold accounted S04FinalReturnRuleAccounting.machine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact model.ghostOff
  have shallow : accounted.user.payload.validation = .Shallow := by
    unfold accounted S04FinalReturnRuleAccounting.machine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact model.shallow
  have backend : accounted.user.payload.payload.user.backend = .none := by
    unfold accounted S04FinalReturnRuleAccounting.machine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact model.noBackend
  have postMemory : post.machine.memory.live = (ActualPopPlan.released machine released.memory current borrowFrame).memory.live := by
    unfold post GenericPopFrame.afterRelevanceAt
    split <;> rfl
  obtain ⟨window,pointerEq,idEq,offsetEq,entryEq,binding⟩ := CurrentCallRootPhysicalWindow.view released.window released.binding
    (final := post.machine) (by rw [postUser];exact addresses) postMemory
  have enabled : post.machine.borrowTracker = some {current with global := current.global.endCall borrowFrame} := by
    unfold post GenericPopFrame.afterRelevanceAt
    split <;> rfl
  have race : post.machine.dataRace = none := by
    unfold post GenericPopFrame.afterRelevanceAt
    split <;> exact model.noDataRace
  have ready : CurrentCallBoolProtection.WindowReady post.machine window.id window.offset.toNat 1 := by
    have original := memoryReady.bool
    have transported := original.transport (show post.machine.user.payload.payload.user.runtime.extras =
      machine.user.payload.payload.user.runtime.extras from by rw [postUser];exact extras)
    rw [idEq,released.roleId,offsetEq,released.roleOffset]
    have normalized := (CurrentCallBoolProtection.endpoints (CurrentCallPush.prepared_input input #[]) {} s.out.source.base.raw positive).2.1
    rw [normalized]
    exact transported
  have completed : (window.entry.allocation.extra.performBorrowAccessRange
      (S04ReturnBorrowBridge.extra window.pointer.provenance) (Size.ofBytes window.offset) (Size.ofBytes 1)
      .Write (current.global.endCall borrowFrame).protectedTags .VisitChildrenOfAccessed).status = .Completed := by
    rw [entryEq,pointerEq,offsetEq]
    exact CurrentCallRootRelease.write_original released.window.entry.allocation.extra (current.global.endCall borrowFrame)
      released.completion released.runtime released.completes released.order s.out.source.base.raw.returnPointer.grant released.node
      released.present released.window.pointer.provenance released.provenance released.window.offset released.bounds released.owned released.short
  have resolved := CurrentCallRootPhysicalWindow.resolve options remaining span post place window binding
  let fuel := options.limits.validation-1
  have fuelEq : options.limits.validation = fuel+1 := by
    have configured := input.machine.resources.configuredFuel.2.2.2
    have lower : 64 ≤ DuplicatePrefixCallSpecification.work before len := by unfold DuplicatePrefixCallSpecification.work;omega
    dsimp only [fuel];omega
  have enabledBefore : accounted.borrowTracker = some current := tracked
  have valid0 : (0 : Miri.MIR.LocalId) < result.locals.size := by rw [size];decide
  have cell0 : result.locals[0] = ⟨.live (.immediate (.scalar (.fromBool true))),some RootCompilerFacts.boolLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem valid0).symm.trans slot0)
  have destination : result.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩ := by
    rw [returnPlace,s.facts.destination];rfl
  have unchecked := model.unchecked
  have noGc := model.noGc
  have fixed := model.fixedScheduler
  obtain ⟨updated,returned,_,_,_⟩ := CurrentCallRootReturn.step_of_release_copy options limits remaining span result accounted current borrowFrame
    enabledBefore frameTracked released.memory released.plan thread active post rfl body located valid0 noClocks ghost returnStop
    immediate noVarargs place window binding {current with global := current.global.endCall borrowFrame} enabled race
    (by rw [postUser];exact backend) (by rw [postUser];exact ghost) (by rw [postUser];exact shallow)
    ready completed resolved true fuel model.debugOff fuelEq (by rw [cell0]) (by rw [cell0]) destination
    machine rfl unchecked noGc fixed
  let installed := Storage.withCurrent #[] (s.out.frame count) (s.out.machine count)
  let finalState := CanonicalCopy.replaceAllocation post window.id window.entry.kind updated
  have trace : SuccessfulTrace.Trace cfg limits installed finalState := SuccessfulTrace.append traceBefore (.next returned (.refl _))
  have terminal : ExecutionMachine.step cfg limits () finalState = (finalState,.ok false) := rfl
  have empty : finalState.stack.frames = #[] := rfl
  let context : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit := ⟨cfg,limits,fun _ _ => True⟩
  have entry : CallSafety.IsCallEntry 1 installed := ⟨by decide,rfl⟩
  have past : CallSafety.pastCallBoundary 1 finalState := by
    change finalState.stack.frames.size < 1
    rw [empty];decide
  exact ⟨installed,finalState,s.facts.actual,trace,terminal,empty,
    SuccessfulTrace.no_errors context 1 installed finalState entry trace past,
    SuccessfulTrace.no_ub context 1 installed finalState entry trace past,
    SuccessfulTraceTerminal.prefix_step_success trace terminal⟩


private theorem accept_from_released {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    {count : UInt64} (s : SharedStage input count) (positive : 0 < len.toNat)
    (root : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (held : MachineHooks.BorrowState) (completion : Completion)
    (facts : CurrentCallAcceptedCopyPrefix.ReturnFacts s root machine entry held completion)
    (tracked : machine.borrowTracker=some held) (located : root.location=.mir ⟨9,0⟩)
    (destination : root.returnPlace=(s.out.frame count).returnPlace)
    (trace : SuccessfulTrace.Trace (config options (remaining+1) span) limits
      (Storage.withCurrent #[] (s.out.frame count) (s.out.machine count)) (Storage.withCurrent #[] root machine))
    (released : CurrentCallEntryRootRelease.Released machine held (CurrentCallEntryRootRelease.Entry.borrowFrame s.out)
      place s.out.source.base.raw.returnPointer.grant call.returnId (UInt64.ofNat call.returnOffset) s.out.source.base.raw.returnPointer.value) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before argument len count place := by
  have fuelEq : options.limits.validation = options.limits.validation-1+1 := by
    have configured := input.machine.resources.configuredFuel.2.2.2
    have lower : 64 ≤ DuplicatePrefixCallSpecification.work before len := by unfold DuplicatePrefixCallSpecification.work;omega
    omega
  have valid (i : Fin 25) : i.val < root.locals.size := by rw [facts.size];exact i.isLt
  have cell (i : Fin 25) (row : LocalState Provenance LocalLayout) (h : root.locals[i.val]?=some row) :
      root.locals[i.val]'(valid i)=row := Option.some.inj ((Array.getElem?_eq_getElem (valid i)).symm.trans h)
  have val (i : Fin 25) (value : Immediate Provenance)
      (h : root.locals[i.val]?.map (·.value)=some (.live (.immediate value))) :
      (root.locals[i.val]'(valid i)).value=.live (.immediate value) := by
    rw [Array.getElem?_eq_getElem (valid i)] at h
    exact Option.some.inj h
  obtain ⟨t15,t18,t19,t21,t24,v15,v18,v19,v21,v24⟩ := facts.temporaries
  obtain ⟨current,currentAt,mode⟩ := facts.model.defaultTracker
  have eq : current=held := Option.some.inj (currentAt.symm.trans tracked)
  subst current
  obtain ⟨done,bodyTrace,shape⟩ := RootSuccessToReturn.reaches_return options limits remaining span
    (DuplicatePrefixCallModel.sourceComparator options remaining span machine facts.model) facts.model.debugOff
    (options.limits.validation-1) fuelEq #[] root machine facts.size t15 t18 t19 t21 t24
    (congrArg (·.value) (cell 0 _ facts.zero)) (congrArg (·.layout) (cell 0 _ facts.zero)) (val 15 _ v15)
    (congrArg (·.value) (cell 17 _ facts.seventeen)) (congrArg (·.layout) (cell 17 _ facts.seventeen))
    (val 18 _ v18) (val 19 _ v19) (val 21 _ v21) (val 24 _ v24)
    facts.body facts.identity facts.callee located facts.clocks held tracked mode facts.model.ghostOff facts.model.shallow
    facts.model.unchecked facts.model.noGc facts.model.fixedScheduler
  let result := {done with location:=.mir ⟨10,0⟩}
  let beforeReturn := RootZeroCompleteState.tick options remaining span machine
  let frame := CurrentCallEntryRootRelease.Entry.borrowFrame s.out
  have viewAddresses : beforeReturn.user.addresses=machine.user.addresses := by
    unfold beforeReturn RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have viewExtras : beforeReturn.user.payload.payload.user.runtime.extras=machine.user.payload.payload.user.runtime.extras := by
    unfold beforeReturn RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  obtain ⟨window,pointerEq,idEq,offsetEq,entryEq,binding⟩ := CurrentCallRootPhysicalWindow.view released.window released.binding
    (final:=ActualPopPlan.released beforeReturn released.memory held frame) viewAddresses rfl
  let current : CurrentCallEntryRootRelease.Released beforeReturn held frame place
      s.out.source.base.raw.returnPointer.grant call.returnId (UInt64.ofNat call.returnOffset) s.out.source.base.raw.returnPointer.value := {
    memory := released.memory, plan := released.plan, window := window, binding := binding
    roleId := idEq.trans released.roleId, roleOffset := offsetEq.trans released.roleOffset, rolePointer := pointerEq.trans released.rolePointer
    completion := released.completion
    runtime := by rw [entryEq];exact released.runtime
    completes := by rw [entryEq];exact released.completes
    order := by rw [entryEq];exact released.order
    short := by rw [entryEq];exact released.short
    node := released.node
    present := by rw [entryEq];exact released.present
    provenance := by rw [pointerEq];exact released.provenance
    bounds := by rw [entryEq,offsetEq];exact released.bounds
    owned := by rw [entryEq,offsetEq];exact released.owned }
  have control := CurrentCallEntryRootRelease.Entry.frame_control s.out count s.facts
  obtain ⟨thread,active⟩ := facts.active
  apply finish s positive result beforeReturn held frame current (SuccessfulTrace.append trace bodyTrace)
    (tick_model _ _ _ _ facts.model) (facts.ready.transport viewExtras) thread active tracked
  · change done.extra.borrowTracker=some frame
    rw [shape.extra,facts.extra];exact CurrentCallEntryRootRelease.Entry.frame_tracked s.out count s.facts
  · exact shape.body.trans facts.body
  · exact shape.size
  · rfl
  · exact shape.output
  · exact shape.destination.trans destination
  · change done.extra.dataRace=none
    rw [shape.extra];exact facts.clocks
  · exact shape.continuation.trans (facts.continuation.trans control.2.1)
  · exact shape.varargs.trans (facts.varargs.trans control.2.2)
  · exact shape.immediate facts.immediate

/-- Original accepted positive-source invocation, including physical copy,
root cleanup, protector release, original Bool store and terminal safety. -/
theorem invoke {options limits remaining span before tracker argument len place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (stackReady : CurrentCallPush.StackReadiness before #[])
    (memoryReady : CurrentCallBoolProtection.ProfileMemoryReadiness before call)
    (positive : 0 < len.toNat) (count : UInt64) (nonzero : count ≠ 0) (within : count ≤ len/2) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before argument len count place := by
  obtain ⟨s,root,post,entry,held,completion,trace,located,destination,live,tracked,runtime,complete,order,capacity,short,owned,activity,
    ⟨node,present,tag,hidden⟩,facts⟩ := CurrentCallAcceptedCopyPrefix.copied_and_returned
      input stackReady memoryReady positive count nonzero within
  obtain ⟨boolData⟩ := facts.boolData
  obtain ⟨initial,idEq,pointerEq,offsetEq,binding⟩ := CurrentCallRootPhysicalWindow.of_entry s.out count s.facts
  have replacement : {s.entry with allocation:=entry.allocation}=entry := by
    change {kind:=s.entry.kind,allocation:=entry.allocation}=entry
    rw [←facts.sourceKind]
  obtain ⟨window,pointerNext,idNext,offsetNext,bindingNext⟩ := CurrentCallCopyBoolWindow.replace initial binding
    call.sourceId s.entry entry.allocation s.live facts.sourceSize facts.sourceLen
    facts.physical.mutable facts.physical.maskValid facts.physical.maskLength facts.physical.pointerBounds facts.addresses
    (by rw [replacement];exact facts.memory)
  have qTag : node.tag=s.out.source.base.raw.output.tag := tag.trans s.out.source.base.raw.tag.symm
  obtain ⟨released⟩ := release_current s positive post held entry boolData.entry completion boolData.completion
    live boolData.live runtime boolData.runtime complete boolData.completes order boolData.order boolData.sameCompletion
    node boolData.node boolData.originalNode present boolData.present boolData.originalPresent boolData.originalProvenance
    qTag boolData.tag hidden boolData.hidden boolData.leaf activity boolData.active owned boolData.owned boolData.edge
    short boolData.short boolData.sourceAbsent boolData.bounds window (idNext.trans idEq) (pointerNext.trans pointerEq)
    (offsetNext.trans offsetEq) bindingNext
  exact accept_from_released s positive root post entry held completion facts tracked located destination trace released

end
end DuplicatePrefix.CurrentCallAcceptedSafety

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallAcceptedSafety" then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved accepted safety dependency {dependency}"
