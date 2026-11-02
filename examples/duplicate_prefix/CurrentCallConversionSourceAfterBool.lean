import duplicate_prefix.CurrentCallSelectedSourceAfterBool
import duplicate_prefix.CurrentCallConversionEntryFrame
import duplicate_prefix.CurrentCallSourceStorageAfterClear

namespace DuplicatePrefix.CurrentCallConversionSourceAfterBool
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization CurrentCallSpatialCover CurrentCallPostEntryCheckpoint
open GeneralBorrowFnEntryRegistration CanonicalConfigFacts ActualReferenceContext
open CurrentCallSelectedSourceAfterBool
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

private theorem set_extra_extra (allocation : Allocation Provenance BorrowTree) (tree : BorrowTree) :
    (allocation.setExtra tree).extra=tree := by cases allocation; rfl
private theorem set_extra_twice (allocation : Allocation Provenance BorrowTree) (first second : BorrowTree) :
    (allocation.setExtra first).setExtra second=allocation.setExtra second := by cases allocation; rfl

private theorem present_of_live (post : Before) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (live : post.memory.live.find? (fun row=>row.1==id)=some (id,entry)) :
    Present (ActualWorld post) id entry.allocation := by
  simp only [Present,ActualWorld,Array.toList_map]
  exact List.mem_map.mpr ⟨(id,entry),Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live),rfl⟩

theorem after_protect_live (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : ActualRetagContext.Context options remaining span)
    (before : Before) (tracker : MachineHooks.BorrowState) (offset : Nat) (len : UInt64)
    (source : Source before tracker offset len) (copyReady : CopyReady source)
    (sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (sourceLive : before.memory.live.find? (fun row=>row.1==source.role.backing.id)=some (source.role.backing.id,sourceEntry))
    (sourceAllocation : sourceEntry.allocation=source.role.backing.allocation)
    (sourceLeaf : source.node.children=#[]) (sourceRoom : source.role.backing.allocation.extra.nodes.size+7<65536)
    (data : Identities) (owner : Nat)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState)
    (enabled : before.borrowTracker=some tracker) (frameBorrow : frame.extra.borrowTracker=some borrowFrame)
    (place : MPlaceTy Provenance) (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow before place)
    (W : UniformWindow before tracker data owner physical.id physical.offset.toNat 1 .ret)
    (pointer : physical.pointer=W.pointer.value) (allocation : physical.entry.allocation=W.allocation)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (binding : CandidateCallBindings.WindowBinding before physical.pointer physical.id physical.offset.toNat 1)
    (distinct : W.allocation.extra.roots.toList.Nodup) (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (short : W.allocation.extra.nodes.size+1<65536)
    (differentGrant : source.role.backing.id=physical.id →source.grant≠W.pointer.grant)
    (separate : ∀byte,Window source.role.backing.id offset len.toNat byte→Window physical.id physical.offset.toNat 1 byte→False)
    (ghost : before.user.payload.ghost=false) (race : before.dataRace=none)
    (backend : before.user.payload.payload.user.backend=.none)
    (ready : CurrentCallBoolProtection.WindowReady before physical.id physical.offset.toNat 1) :
    ∃(output : GeneralBorrowForestFnEntry.Output)(post : RootState),
    ∃(R : Return post.machine ⟨output.global,tracker.retagMode⟩ place)
      (current : Source post.machine ⟨output.global,tracker.retagMode⟩ offset len),
      (ExecutionMachine.callHooks (ActualReferenceContext.config options remaining span) options.limits).protectArgument () place
        (Storage.withCurrent frames frame before)=.ok () post ∧CopyReady current ∧
      current.role.family=source.role.family ∧current.role.backing.id=source.role.backing.id ∧
      current.tag=source.tag ∧current.grant=source.grant ∧
      R.id=physical.id ∧R.offset=physical.offset.toNat ∧R.original=W.pointer ∧
      post.machine.borrowTracker=some ⟨output.global,tracker.retagMode⟩ ∧
      output.global=(registered tracker.global borrowFrame physical.id fresh).1 ∧
      post.stack=(Storage.withCurrent frames (TypedBorrowSteps.registeredFrame frame borrowFrame physical.id tracker.global.nextPointerTag) before).stack ∧
      R.node.tag=tracker.global.nextPointerTag ∧
      R.window.allocation.extra.nodes.size≤W.allocation.extra.nodes.size+1 ∧
      CandidateCurrentFnEntryRaw.operation W.allocation.extra tracker.global borrowFrame physical.id
        W.pointer.value.provenance physical.offset 1 = .ok output ∧
      R.window.allocation.extra.tagMapping = output.child.tree.tagMapping ∧
      R.window.allocation.extra = (output.child.tree.performBorrowAccessRange (.concrete output.tag)
        (Size.ofBytes physical.offset) (Size.ofBytes 1) .Write output.global.protectedTags .VisitChildrenOfAccessed).tree ∧
      Allocation.writeUninit (allocRange (Size.ofBytes physical.offset) (Size.ofBytes 1)) (Size.ofBytes 8)
        ((physical.entry.allocation.setExtra output.child.tree).setExtra
          (output.child.tree.performBorrowAccessRange (.concrete output.tag) (Size.ofBytes physical.offset) (Size.ofBytes 1)
            .Write output.global.protectedTags .VisitChildrenOfAccessed).tree) = .ok () R.window.allocation ∧
      post.machine = {(ReturnProtection.borrowedState frames frame borrowFrame before tracker fresh physical.id physical.entry output.child.tree).machine with
        memory := {(ReturnProtection.borrowedState frames frame borrowFrame before tracker fresh physical.id physical.entry output.child.tree).machine.memory with
          live := (((ReturnProtection.borrowedState frames frame borrowFrame before tracker fresh physical.id physical.entry output.child.tree).machine.memory.live.filter
            (fun row => row.1 != physical.id)).push (physical.id, {physical.entry with allocation := R.window.allocation}))}} := by
  obtain ⟨output,post,R,protect,idEq,offsetEq,original,nodeTag,growth,tracked,globalEq,stackEq,actual,tagsEq,extra,mutation,postEq⟩ :=
    CurrentCallConversionBool.protect_live options remaining span ctx before tracker data owner frames frame borrowFrame enabled frameBorrow
      place physical W pointer allocation runtime binding distinct fresh short ghost race backend ready
  let written := output.child.tree.performBorrowAccessRange (.concrete output.tag) (Size.ofBytes physical.offset) (Size.ofBytes 1)
    .Write output.global.protectedTags .VisitChildrenOfAccessed
  have mutation' : Allocation.writeUninit (allocRange (Size.ofBytes physical.offset) (Size.ofBytes 1)) (Size.ofBytes 8)
      (physical.entry.allocation.setExtra written.tree)=.ok () R.window.allocation := by
    simpa only [set_extra_twice] using mutation
  obtain ⟨lengthEq,sizeEq,mutable,_,_,_,_⟩:=CurrentCallBoolWindow.mutation_metadata physical written.tree R.window.allocation mutation'
  have postLookup:=CurrentCallConversionEntryFrame.live frames frame borrowFrame fresh physical.id physical.entry output.child.tree
    R.window.allocation post.machine postEq source.role.backing.id
  have cached : ∀base,before.user.addresses.baseAddr.find? (fun row=>row.allocId==source.role.backing.id)=some ⟨source.role.backing.id,base⟩ →
      post.machine.user.addresses.baseAddr.find? (fun row=>row.allocId==source.role.backing.id)=some ⟨source.role.backing.id,base⟩ := by
    intro base hit
    rw [postEq]
    exact hit
  have postProfile : CurrentCallBoolProtection.WindowReady post.machine source.role.backing.id offset len.toNat :=
    CurrentCallConversionEntryFrame.profile copyReady.profile (by rw [postEq];rfl)
  have bounds : physical.offset.toNat+1≤W.allocation.extra.locations.size.bytes.toNat := by
    have hit:=(W.window (physical.id,physical.offset.toNat) ⟨rfl,Nat.le_refl _,by omega⟩).1
    rw [W.issued.capability.treeExtent,←W.issued.capability.extent]
    omega
  have nodeRoom : W.allocation.extra.nodes.size+1≤4294967295 := by omega
  obtain ⟨otherOutput,child,otherActual,tag,_,_,_,_,lookup,⟨witness⟩⟩ :=
    CurrentCallResourceFnEntry.correlated_borrow_selected W runtime borrowFrame fresh rfl distinct (by omega) nodeRoom
      physical.offset 1 rfl rfl (by decide) bounds
  have outputEq : otherOutput=output:=Except.ok.inj (otherActual.symm.trans actual)
  subst otherOutput
  let ctor := ReturnProtection.borrowedState frames frame borrowFrame before tracker fresh physical.id physical.entry output.child.tree
  have ctorPresent : Present (ActualWorld ctor.machine) physical.id (W.allocation.setExtra output.child.tree) := by
    simp only [Present,ActualWorld,Array.toList_map]
    refine List.mem_map.mpr ⟨(physical.id,{physical.entry with allocation:=physical.entry.allocation.setExtra output.child.tree}),?_,?_⟩
    · exact Array.mem_toList_iff.mpr (Array.mem_push.mpr (.inr rfl))
    · rw [allocation]
  have rootTag : output.global.rootTag? physical.id=tracker.global.rootTag? physical.id := by rw [globalEq];rfl
  have writeFacts:=CurrentCallSelectedBoolCurrent.operation_runtime W runtime borrowFrame fresh distinct short physical.offset rfl
    output child actual witness tag ctor.machine ctorPresent rootTag .VisitChildrenOfAccessed
  have currentExists : ∃current : Source post.machine ⟨output.global,tracker.retagMode⟩ offset len,
      CopyReady current ∧current.role.family=source.role.family ∧current.role.backing.id=source.role.backing.id ∧
      current.tag=source.tag ∧current.grant=source.grant := by
    by_cases same : source.role.backing.id=physical.id
    · have entries : sourceEntry=physical.entry := by
        have first:=sourceLive
        rw [same,physical.live] at first
        exact (Prod.mk.inj (Option.some.inj first.symm)).2
      have sameAllocation : source.role.backing.allocation=W.allocation := by rw [←sourceAllocation,entries,allocation]
      have live : post.machine.memory.live.find? (fun row=>row.1==source.role.backing.id)=
          some (source.role.backing.id,{physical.entry with allocation:=R.window.allocation}) := by
        simpa only [same,ite_true] using postLookup
      have present : Present (ActualWorld post.machine) source.role.backing.id R.window.allocation := present_of_live post.machine _ _ live
      have currentBinding:=CurrentCallConversionEntryFrame.binding source.binding source.tag source.concrete sourceEntry
        {physical.entry with allocation:=R.window.allocation} sourceLive live
        (by rw [entries];exact sizeEq) (by rw [entries];exact lengthEq) cached
      have sourceFits : offset<2^64 := by
        have request : Window source.role.backing.id offset len.toNat (source.role.backing.id,offset):=⟨rfl,Nat.le_refl _,by have := source.positive;omega⟩
        obtain ⟨i,cell⟩:=source.role.covered (source.role.backing.id,offset) request
        have overlap : CurrentCallSpatialSourceCover.Active source.role i:=⟨_,request,cell⟩
        have bound:=((source.role.roles i overlap).available _ request cell).1
        have storage:=copyReady.storage.storage
        have extent:=source.role.backing.allocation.byteSize.bytes.toNat_lt
        omega
      have offEq : (UInt64.ofNat offset).toNat=offset := by rw [UInt64.toNat_ofNat',Nat.mod_eq_of_lt sourceFits]
      have apart : (UInt64.ofNat offset).toNat+len.toNat≤physical.offset.toNat ∨physical.offset.toNat+1≤(UInt64.ofNat offset).toNat := by
        rw [offEq]
        by_cases early : offset+len.toNat≤physical.offset.toNat
        · exact Or.inl early
        · apply Or.inr
          apply Nat.le_of_not_gt
          intro late
          have low : offset≤physical.offset.toNat := by omega
          exact separate (physical.id,physical.offset.toNat) ⟨same.symm,low,by omega⟩ ⟨rfl,Nat.le_refl _,by omega⟩
      have sourceData : CurrentCallResourceEntrySourceStorage.Data physical.entry.allocation (UInt64.ofNat offset) len := by
        rw [←entries,sourceAllocation]
        exact copyReady.storage
      have storage:=CurrentCallSourceStorageAfterClear.after_clear physical written.tree R.window.allocation
        (UInt64.ofNat offset) len sourceData apart mutation'
      have initialAt : W.allocation.extra.nodes.get source.grant=some source.node := by rw [←sameAllocation];exact source.nodeAt
      have freshQ : source.tag.value.toNat<tracker.global.nextPointerTag.value.toNat := by
        exact GeneralBorrowForestTagHighWater.mapped _ _ _ source.tag source.runtime.below source.grant
          (by rw [←source.nodeTag];exact source.runtime.formed.allocator.nodeTags _ _ source.nodeAt)
      have differentNew : source.grant≠child := by
        intro equal
        have old:=witness.oldNodes source.grant source.node initialAt
        obtain ⟨next,atNext,nextTag,_,_,_⟩:=old
        rw [equal,witness.nodeAt] at atNext
        have nodeEqual:=Option.some.inj atNext
        have tagEqual : source.node.tag=output.tag := nextTag.symm.trans ((congrArg TreeNode.tag nodeEqual).symm.trans witness.tag)
        have savedEq : source.tag=tracker.global.nextPointerTag := source.nodeTag.symm.trans (tagEqual.trans tag)
        rw [savedEq] at freshQ
        exact Nat.lt_irrefl _ freshQ
      obtain ⟨next,nextAt,nextTag,nextLeaf,nextHidden,nextActive⟩:=source_activity W runtime borrowFrame fresh distinct short physical.offset rfl
        output child actual witness tag ctor.machine ctorPresent rootTag source.grant source.node initialAt sourceLeaf source.hidden
        (differentGrant same) differentNew (UInt64.ofNat offset) (UInt64.ofNat offset+len)
        (by rw [←sameAllocation];exact source.activity)
      have atWritten : R.window.allocation.extra.nodes.get source.grant=some next := by rw [extra];exact nextAt
      have activeWritten : GeneralBorrowFreshActiveWithin.ActiveWithin R.window.allocation.extra source.grant .Write
          (UInt64.ofNat offset) (UInt64.ofNat offset+len) := by rw [extra];exact nextActive
      let ret:=CurrentCallSpatialCover.ofUniform W
      have outEq : CurrentCallSpatialEntryRead.output ret borrowFrame fresh physical.offset 1=output := by
        exact Except.ok.inj ((CurrentCallSpatialEntryRead.literal_operation ret borrowFrame fresh physical.offset 1).symm.trans actual)
      let updatesRaw:=same_updates source.role ret same sameAllocation separate runtime distinct (by change W.allocation.extra.nodes.size<65536;omega) nodeRoom borrowFrame fresh physical.offset rfl
        bounds physical.entry allocation child (by rw [outEq,←tag];exact lookup) (by rw [outEq];exact witness.runtime)
        (by rw [outEq];exact witness.capacity) (by simpa only [CurrentCallSelectedSourceAfterBool.written,outEq] using writeFacts.2.2.2.2.2.2.2)
        post.machine R.window.allocation (by change Present (ActualWorld post.machine) physical.id R.window.allocation;simpa only [same] using present) (by simpa only [CurrentCallSelectedSourceAfterBool.written,outEq] using extra)
        (by change R.window.allocation.len=W.allocation.len;rw [←allocation];exact lengthEq) (by change R.window.allocation.byteSize=W.allocation.byteSize;rw [←allocation];exact sizeEq)
        (by rw [outEq];exact R.runtime) source.grant (source_grants source)
      have updates : ∀i overlap,CurrentCallSpatialSourceCover.Update source.role post.machine ⟨output.global,tracker.retagMode⟩
          R.window.allocation source.role.family source.grant i overlap := by
        have typed : ∀i overlap,CurrentCallSpatialSourceCover.Update source.role post.machine
            ⟨(CurrentCallSpatialEntryRead.output ret borrowFrame fresh physical.offset 1).global,tracker.retagMode⟩
            R.window.allocation source.role.family source.grant i overlap := updatesRaw
        rw [outEq] at typed
        exact typed
      obtain ⟨current,ready,family,alloc,id,tagEq,grantEq⟩:=assemble source post.machine _ R.window.allocation present updates
        R.runtime R.distinct next atWritten (nextTag.trans source.nodeTag) nextHidden activeWritten currentBinding
        (by rw [←sameAllocation] at growth;omega) storage postProfile
      exact ⟨current,ready,family,id,tagEq,grantEq⟩
    · have live : post.machine.memory.live.find? (fun row=>row.1==source.role.backing.id)=some (source.role.backing.id,sourceEntry) := by
        simpa only [same,ite_false,sourceLive] using postLookup
      have present : Present (ActualWorld post.machine) source.role.backing.id source.role.backing.allocation := by
        simpa only [sourceAllocation] using (present_of_live post.machine source.role.backing.id sourceEntry live)
      have currentBinding:=CurrentCallConversionEntryFrame.binding source.binding source.tag source.concrete sourceEntry sourceEntry sourceLive live rfl rfl cached
      let updates:=updates_of_cells source.role post.machine ⟨output.global,tracker.retagMode⟩ source.role.backing.allocation source.grant
        (fun i=>source.role.backing.cells[i].completion) (source_grants source)
        (other_cells source.role source.runtime borrowFrame fresh physical.id post.machine ⟨output.global,tracker.retagMode⟩ globalEq present)
      have afterRuntime : DuplicatePrefixBorrowContract.RuntimeFacts source.role.backing.allocation.extra output.global := by
        rw [globalEq]
        exact (GeneralBorrowFnEntryRegistrationRuntime.prepare source.role.backing.allocation.extra tracker.global borrowFrame physical.id fresh source.runtime).2.2.2.1
      obtain ⟨current,ready,family,alloc,id,tagEq,grantEq⟩:=assemble source post.machine _ source.role.backing.allocation present updates
        afterRuntime source.distinct source.node source.nodeAt source.nodeTag source.hidden source.activity currentBinding
        source.nodes copyReady.storage postProfile
      exact ⟨current,ready,family,id,tagEq,grantEq⟩
  obtain ⟨current,copyReady,family,id,tagEq,grantEq⟩:=currentExists
  exact ⟨output,post,R,current,protect,copyReady,family,id,tagEq,grantEq,idEq,offsetEq,original,tracked,globalEq,stackEq,nodeTag,growth,actual,tagsEq,extra,mutation,postEq⟩
end
end DuplicatePrefix.CurrentCallConversionSourceAfterBool

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallConversionSourceAfterBool" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual source-after-Bool dependency {dependency}"
