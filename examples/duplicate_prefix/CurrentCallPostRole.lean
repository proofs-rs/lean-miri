import duplicate_prefix.CurrentCallResourceFnEntry
import duplicate_prefix.CurrentCallResourceInstallation
import duplicate_prefix.CurrentCallBorrowIssuance
import duplicate_prefix.CurrentCallBoolWriteRuntime

/-! A retained role in the actual installed world. The private operational view
only supplies bookkeeping to the existing resource backend; it asserts neither
a valid rewritten interpretation nor a whole post-call denotation. -/
namespace DuplicatePrefix.CurrentCallPostRole
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.DataStructures
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization GeneralBorrowFnEntryRegistration
open TypedBorrowSteps ReferenceBorrowDriver ReturnProtection CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- Original family and loan lookups are retained in `W`; all operational
resources below refer to the actual post heap and actual extended parent map. -/
structure InstalledRole {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode)
    (post : Before) (next : MachineHooks.BorrowState) where
  tree : BorrowTree
  completion : Completion
  present : Present (ActualWorld post) id (W.allocation.setExtra tree)
  binding : PointerBinds (W.allocation.setExtra tree) W.pointer
  issued : SpatialDelegation post next id (W.allocation.setExtra tree) completion W.pointer.grant
  parents : ParentInterpretation tree completion
  window : ∀ byte, Window id offset length byte → byte.2 < W.allocation.len ∧
    Embeds (W.allocation.setExtra tree) next.global.protectedTags completion W.pointer.grant byte.2 (demandOf mode)

theorem InstalledRole.runtime {before tracker data owner id offset length mode}
    {W : UniformWindow before tracker data owner id offset length mode} {post next}
    (R : InstalledRole W post next) (state : DuplicatePrefixRuntimeInput.State post next)
    (highwater : ∀ row∈post.memory.live.toList,GeneralBorrowForestTagHighWater.Below row.2.allocation.extra
      next.global.protectedTags next.global.nextPointerTag) :
    DuplicatePrefixBorrowContract.RuntimeFacts R.tree next.global := by
  have present := R.present
  simp only [Present,ActualWorld,Array.toList_map] at present
  obtain ⟨⟨actualId,entry⟩,member,equal⟩ := List.mem_map.mp present
  rcases Prod.mk.inj equal with ⟨rfl,equal⟩
  have treeEq : entry.allocation.extra=R.tree := congrArg Allocation.extra equal
  exact ⟨by simpa only [treeEq] using state.formed (actualId,entry) member,
    by simpa only [treeEq] using state.coherent (actualId,entry) member,
    by simpa only [treeEq] using state.possible (actualId,entry) member,
    by simpa only [treeEq] using highwater (actualId,entry) member⟩

private def viewData {before tracker data owner id offset length mode}
    {W : UniformWindow before tracker data owner id offset length mode} {post next}
    (R : InstalledRole W post next) : Identities :=
  {data with interpretation := {data.interpretation with precise := (
    data.interpretation.precise.map (fun pair =>
      if pair.1 = id then (id,{pair.2 with completion := R.completion}) else pair))}}

private def view {before tracker data owner id offset length mode}
    {W : UniformWindow before tracker data owner id offset length mode} {post next}
    (R : InstalledRole W post next) : UniformWindow post next (viewData R) owner id offset length mode where
  loan := W.loan
  pointer := W.pointer
  allocation := W.allocation.setExtra R.tree
  precise := {W.precise with completion := R.completion}
  loanAt := W.loanAt
  pointerAt := W.pointerAt
  pointerId := W.pointerId
  present := R.present
  preciseAt := by
    change (id,{W.precise with completion := R.completion}) ∈
      (data.interpretation.precise.map (fun pair =>
        if pair.1 = id then (id,{pair.2 with completion := R.completion}) else pair)).toList
    apply Array.mem_toList_iff.mpr
    apply Array.mem_map.mpr
    refine ⟨(id,W.precise),Array.mem_toList_iff.mp W.preciseAt,?_⟩
    simp only [ite_true]
  binding := R.binding
  issued := R.issued
  parents := R.parents
  window := R.window

private def atGeometry {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode)
    (newId : AllocId) (newOffset : Nat) (sameId : newId=id) (sameOffset : newOffset=offset) :
    UniformWindow before tracker data owner newId newOffset length mode where
  loan := W.loan
  pointer := W.pointer
  allocation := W.allocation
  precise := W.precise
  loanAt := W.loanAt
  pointerAt := W.pointerAt
  pointerId := W.pointerId.trans sameId.symm
  present := by rw [sameId];exact W.present
  preciseAt := by rw [sameId];exact W.preciseAt
  binding := W.binding
  issued := by rw [sameId];exact W.issued
  parents := W.parents
  window := by
    intro byte inside
    exact W.window byte (by simpa only [sameId,sameOffset] using inside)

/-- The retained post-world role immediately drives the actual next FnEntry
operation. Its Read and constructor certificates are derived internally from
the same operation, using the existing common backend. -/
theorem borrow_steps {before tracker data owner id offset length mode}
    {W : UniformWindow before tracker data owner id offset length mode} {post next}
    (R : InstalledRole W post next)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts R.tree next.global)
    (state : DuplicatePrefixRuntimeInput.State post next)
    (highwater : ∀ row ∈ post.memory.live.toList, GeneralBorrowForestTagHighWater.Below row.2.allocation.extra
      next.global.protectedTags next.global.nextPointerTag)
    (frame : FrameState) (room : next.global.nextPointerTag.value < 18446744073709551615)
    (exclusive : demandOf mode = .exclusive) (distinct : R.tree.roots.toList.Nodup)
    (short : R.tree.nodes.size < 65536) (nodeRoom : R.tree.nodes.size+1 ≤ 4294967295)
    (start amount : UInt64) (startEq : start.toNat = offset) (amountEq : amount.toNat = length)
    (nonzero : amount ≠ 0) (bounds : start.toNat+amount.toNat ≤ R.tree.locations.size.bytes.toNat) :
    ∃ (output : GeneralBorrowForestFnEntry.Output) (child : UniIndex),
      CandidateCurrentFnEntryRaw.operation R.tree next.global frame id W.pointer.value.provenance start amount = .ok output ∧
      output.tag = next.global.nextPointerTag ∧
      output.global = (registered next.global frame id room).1 ∧
      output.frame = (registered next.global frame id room).2 ∧
      output.access.status = .Completed ∧
      output.child.outcome = .ok () ∧
      output.child.tree.indexOfTag output.tag = some child ∧
      ParentInterpretation output.child.tree (S05ConcreteProtectedChildCompletion.extend R.completion child W.pointer.grant) ∧
      GeneralRangeMapOrigins.OwnedOn (S05CompletedAncestryReadMutable.Authority output.child.tree
        (S05ConcreteProtectedChildCompletion.extend R.completion child W.pointer.grant) output.global.protectedTags child)
        start (start+amount) output.child.tree.locations := by
  obtain ⟨output,child,actual,tag,global,callFrame,readDone,childDone,lookup,⟨witness⟩⟩ :=
    CurrentCallResourceFnEntry.correlated_borrow (view R) runtime state highwater frame room exclusive distinct short nodeRoom
      start amount startEq amountEq nonzero bounds
  exact ⟨output,child,actual,tag,global,callFrame,readDone,childDone,lookup,witness.parents,witness.owned⟩

/-- Same-allocation source installation retains the original return role. The
source operation and installed presence are facts of the preceding actual
producer; return resources are derived by disjoint framing, not assumed. -/
theorem after_source_same {before tracker data owner id offset length mode returnOwner returnOffset}
    (W : UniformWindow before tracker data owner id offset length mode)
    (V : UniformWindow before tracker data returnOwner id returnOffset 1 .ret)
    (allocationEq : V.allocation = W.allocation) (completionEq : V.precise.completion = W.precise.completion)
    (separate : ∀ byte,Window id offset length byte → Window id returnOffset 1 byte → False)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (state : DuplicatePrefixRuntimeInput.State before tracker)
    (highwater : ∀ row ∈ before.memory.live.toList, GeneralBorrowForestTagHighWater.Below row.2.allocation.extra
      tracker.global.protectedTags tracker.global.nextPointerTag)
    (frame : FrameState) (room : tracker.global.nextPointerTag.value < 18446744073709551615)
    (exclusive : demandOf mode = .exclusive) (distinct : W.allocation.extra.roots.toList.Nodup)
    (short : W.allocation.extra.nodes.size < 65536) (nodeRoom : W.allocation.extra.nodes.size+1 ≤ 4294967295)
    (start amount : UInt64) (startEq : start.toNat = offset) (amountEq : amount.toNat = length)
    (nonzero : amount ≠ 0) (bounds : start.toNat+amount.toNat ≤ W.allocation.extra.locations.size.bytes.toNat)
    (output : GeneralBorrowForestFnEntry.Output) (child : UniIndex)
    (actual : CandidateCurrentFnEntryRaw.operation W.allocation.extra tracker.global frame id W.pointer.value.provenance start amount = .ok output)
    (witness : CurrentCallResourceFnEntry.BorrowWitness W output child start amount)
    (tag : output.tag = tracker.global.nextPointerTag)
    (global : output.global = (registered tracker.global frame id room).1)
    (post : Before) (present : Present (ActualWorld post) id (W.allocation.setExtra output.child.tree)) :
    ∃ R : InstalledRole V post ⟨output.global,tracker.retagMode⟩,
      R.tree = output.child.tree ∧
      R.completion = S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant := by
  obtain ⟨other,otherChild,otherActual,⟨otherWitness⟩,_,binding,window⟩ :=
    CurrentCallResourceFnEntry.invoke_framed W V allocationEq completionEq separate runtime state highwater frame room exclusive distinct short nodeRoom
      start amount startEq amountEq nonzero bounds
  have same : other = output := Except.ok.inj (otherActual.symm.trans actual)
  subst other
  have lookup := witness.runtime.formed.allocator.nodeTags child witness.node witness.nodeAt
  have otherLookup := otherWitness.runtime.formed.allocator.nodeTags otherChild otherWitness.node otherWitness.nodeAt
  rw [witness.tag] at lookup
  rw [otherWitness.tag] at otherLookup
  have childEq : otherChild = child := Option.some.inj (otherLookup.symm.trans lookup)
  subst otherChild
  have vacant : V.allocation.extra.nodes.get child = none := by
    rw [allocationEq]
    cases oldAt : W.allocation.extra.nodes.get child with
    | none => rfl
    | some old =>
      obtain ⟨changed,changedAt,changedTag,_,_,_⟩ := witness.oldNodes child old oldAt
      have sameNode : changed = witness.node := Option.some.inj (changedAt.symm.trans witness.nodeAt)
      have oldTag : old.tag = output.tag := changedTag.symm.trans ((congrArg TreeNode.tag sameNode).trans witness.tag)
      have older := GeneralBorrowParentTagInvariant.parent_below_fresh W.allocation.extra tracker.global runtime child old oldAt
      rw [oldTag,tag] at older
      exact False.elim (Nat.lt_irrefl _ (UInt64.lt_iff_toNat_lt.mp older))
  have retPresent : Present (ActualWorld post) id (V.allocation.setExtra output.child.tree) := by
    simpa only [allocationEq] using present
  have rootTag : output.global.rootTag? id = tracker.global.rootTag? id := by rw [global];rfl
  have capacity : output.child.tree.locations.size = V.allocation.extra.locations.size := by
    rw [allocationEq];exact witness.capacity
  have roots : ∀ (position : Nat) (root : UniIndex),V.allocation.extra.roots[position]? = some root → output.child.tree.roots[position]? = some root := by
    rw [allocationEq];exact witness.oldRoots
  have metadata : ∀ index node,V.allocation.extra.nodes.get index = some node →
      ∃ changed,output.child.tree.nodes.get index = some changed ∧ changed.tag = node.tag ∧ changed.parent = node.parent ∧
        changed.isExposed = node.isExposed ∧ changed.defaultInitialPermission = node.defaultInitialPermission := by
    rw [allocationEq];exact witness.oldNodes
  have issued := CurrentCallResourceInstallation.spatial V.issued V.parents post ⟨output.global,tracker.retagMode⟩
    output.child.tree retPresent rootTag capacity roots metadata child W.pointer.grant vacant
  rw [completionEq] at issued
  refine ⟨⟨output.child.tree,_,retPresent,?_,issued,witness.parents,?_⟩,rfl,rfl⟩
  · simpa only [allocationEq] using binding
  · intro byte inside
    obtain ⟨bound,embedding⟩ := window byte inside
    exact ⟨bound,by simpa [allocationEq,demandOf] using embedding⟩

/-- An unchanged allocation row moves to the actual post world. Fresh source
registration changes no old node's protector flag, so its original role remains
available without constructing a new denotation or choosing another family. -/
theorem after_source_unchanged {before tracker data owner id offset length mode}
    (V : UniformWindow before tracker data owner id offset length mode)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts V.allocation.extra tracker.global)
    (frame : FrameState) (room : tracker.global.nextPointerTag.value < 18446744073709551615)
    (sourceId : AllocId) (post : Before)
    (present : Present (ActualWorld post) id V.allocation) :
    ∃ R : InstalledRole V post {tracker with global := (registered tracker.global frame sourceId room).1},
      R.tree = V.allocation.extra ∧ R.completion = V.precise.completion := by
  let registered := CurrentCallResourceFnEntry.registered_window V runtime frame room
  have actualPresent : Present (ActualWorld post) id (V.allocation.setExtra V.allocation.extra) := by
    simpa only [Allocation.setExtra,Allocation.mapExtra] using present
  have rootTag : (GeneralBorrowFnEntryRegistration.registered tracker.global frame sourceId room).1.rootTag? id = tracker.global.rootTag? id := rfl
  have metadata : ∀ index node,V.allocation.extra.nodes.get index = some node →
      ∃ changed,V.allocation.extra.nodes.get index = some changed ∧ changed.tag = node.tag ∧ changed.parent = node.parent ∧
        changed.isExposed = node.isExposed ∧ changed.defaultInitialPermission = node.defaultInitialPermission := by
    intro index node atNode
    exact ⟨node,atNode,rfl,rfl,rfl,rfl⟩
  have issued := CurrentCallResourceInstallation.spatial_frame V.issued post
    {tracker with global := (GeneralBorrowFnEntryRegistration.registered tracker.global frame sourceId room).1}
    V.allocation.extra actualPresent rootTag rfl (fun _ _ found => found) metadata V.precise.completion (fun _ _ edge => edge)
  refine ⟨⟨V.allocation.extra,V.precise.completion,actualPresent,?_,issued,V.parents,?_⟩,rfl,rfl⟩
  · simpa only [Allocation.setExtra,Allocation.mapExtra] using V.binding
  · intro byte inside
    have retained : byte.2 < V.allocation.len ∧
        Embeds V.allocation (GeneralBorrowFnEntryRegistration.registered tracker.global frame sourceId room).1.protectedTags
          V.precise.completion V.pointer.grant byte.2 (demandOf mode) := registered.window byte inside
    simpa only [Allocation.setExtra,Allocation.mapExtra] using retained

/-- The actual installed return role, rather than an invented post-denotation,
feeds typed protection and activation. The returned child resources describe
the constructor tree before activation; the mutation equation identifies the
actual subsequent write tree separately. -/
theorem protect_role (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (ctx : ActualRetagContext.Context options remaining span)
    {before : Before} {originTracker : MachineHooks.BorrowState} {data : Identities} {owner : Nat} {id : AllocId} {offset : Nat}
    (machine : Before) (tracker : MachineHooks.BorrowState)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState)
    (state : DuplicatePrefixRuntimeInput.State machine tracker)
    (highwater : ∀ row∈machine.memory.live.toList,GeneralBorrowForestTagHighWater.Below row.2.allocation.extra tracker.global.protectedTags tracker.global.nextPointerTag)
    (frameBorrow : frame.extra.borrowTracker=some borrowFrame)
    (place : MPlaceTy Provenance) (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow machine place)
    (V : UniformWindow before originTracker data owner id offset 1 .ret)
    (R : InstalledRole V machine tracker)
    (physicalId : physical.id=id) (physicalOffset : physical.offset.toNat=offset)
    (pointer : physical.pointer=V.pointer.value) (allocation : physical.entry.allocation=V.allocation.setExtra R.tree)
    (binding : CandidateCallBindings.WindowBinding machine physical.pointer physical.id physical.offset.toNat 1)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615) (short : R.tree.nodes.size+1<65536)
    (ghost : machine.user.payload.ghost=false) (race : machine.dataRace=none) (backend : machine.user.payload.payload.user.backend=.none)
    (ready : CurrentCallBoolProtection.WindowReady machine physical.id physical.offset.toNat 1) :
    ∃ (output : GeneralBorrowForestFnEntry.Output) (child : UniIndex),
      CandidateCurrentFnEntryRaw.operation R.tree tracker.global borrowFrame physical.id V.pointer.value.provenance physical.offset 1=.ok output ∧
      output.tag=tracker.global.nextPointerTag ∧ output.global=(registered tracker.global borrowFrame physical.id fresh).1 ∧
      output.frame=(registered tracker.global borrowFrame physical.id fresh).2 ∧
      ParentInterpretation output.child.tree (S05ConcreteProtectedChildCompletion.extend R.completion child V.pointer.grant) ∧
      GeneralRangeMapOrigins.OwnedOn (S05CompletedAncestryReadMutable.Authority output.child.tree
        (S05ConcreteProtectedChildCompletion.extend R.completion child V.pointer.grant) output.global.protectedTags child)
        physical.offset (physical.offset+1) output.child.tree.locations ∧
      (∃ node,output.child.tree.nodes.get child=some node ∧ node.tag=output.tag) ∧
    let retagged := ReturnProtection.borrowedState frames frame borrowFrame machine tracker fresh physical.id physical.entry output.child.tree
    let written := output.child.tree.performBorrowAccessRange (.concrete tracker.global.nextPointerTag) (Size.ofBytes physical.offset) (Size.ofBytes 1)
      .Write (registeredGlobal (allocatedTracker tracker fresh) tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed
    ∃ updated, (ExecutionMachine.callHooks (config options remaining span) limits).protectArgument () place
      (Storage.withCurrent frames frame machine)=
      .ok () {retagged with machine:={retagged.machine with memory:={retagged.machine.memory with live:=
        ((retagged.machine.memory.live.filter (fun row=>row.1 != physical.id)).push (physical.id,{physical.entry with allocation:=updated}))}}} ∧
      updated.extra=written.tree ∧ updated.byteSize=physical.entry.allocation.byteSize ∧ updated.len=physical.entry.allocation.len ∧
      updated.mutability=.Mut ∧ Allocation.writeUninit (allocRange (Size.ofBytes physical.offset) (Size.ofBytes 1)) (Size.ofBytes 8)
        ((physical.entry.allocation.setExtra output.child.tree).setExtra written.tree)=.ok () updated ∧
      AllocationCopy.snapshot updated=AllocationCopy.snapshot physical.entry.allocation ∧
      retagged.machine.borrowTracker=some (registeredTracker (allocatedTracker tracker fresh) tracker.global.nextPointerTag) ∧
      (registeredFrame frame borrowFrame physical.id tracker.global.nextPointerTag).extra.borrowTracker=
        some (borrowFrame.addProtector physical.id tracker.global.nextPointerTag) ∧
      (registeredFrame frame borrowFrame physical.id tracker.global.nextPointerTag).returnPlace=frame.returnPlace ∧
      DuplicatePrefixBorrowContract.RuntimeFacts updated.extra output.global ∧
      ParentInterpretation updated.extra (S05ConcreteProtectedChildCompletion.extend R.completion child V.pointer.grant) ∧
      GeneralRangeMapOrigins.OwnedOn
        (S05CompletedAncestryReadMutable.Authority updated.extra
          (S05ConcreteProtectedChildCompletion.extend R.completion child V.pointer.grant) output.global.protectedTags child)
        physical.offset (physical.offset+1) updated.extra.locations ∧
      updated.extra.nodes=output.child.tree.nodes ∧ updated.extra.roots=output.child.tree.roots ∧
      updated.extra.tagMapping=output.child.tree.tagMapping ∧ updated.extra.locations.size=output.child.tree.locations.size ∧
      let finalMachine : Before := {retagged.machine with memory := {retagged.machine.memory with live :=
        ((retagged.machine.memory.live.filter (fun row=>row.1 != physical.id)).push (physical.id,{physical.entry with allocation:=updated}))}}
      finalMachine.borrowTracker=some ⟨output.global,tracker.retagMode⟩ ∧
      (finalMachine.memory.live.toList.map Prod.fst).Nodup ∧
      (finalMachine.memory.live.toList.flatMap fun row=>row.2.allocation.extra.tagMapping.mapping.toList.map Prod.fst).Nodup ∧
      (∀ row∈finalMachine.memory.live.toList,DuplicatePrefixBorrowContract.RuntimeFacts row.2.allocation.extra output.global) ∧
      (∀ row∈finalMachine.memory.live.toList,row.2.allocation.extra.roots.toList.Nodup) ∧
      (∀ row∈finalMachine.memory.live.toList,GeneralBorrowForestTagHighWater.Below row.2.allocation.extra
        output.global.protectedTags output.global.nextPointerTag) ∧
      ActualRealized (ActualWorld finalMachine) output.global.protectedTags := by
  obtain ⟨output,child,actual,tag,global,callFrame,⟨witness⟩,activation⟩ :=
    CurrentCallBoolWriteRuntime.activate_resources options limits remaining span ctx machine tracker (viewData R) owner
      frames frame borrowFrame state highwater frameBorrow place physical
      (atGeometry (view R) physical.id physical.offset.toNat physicalId physicalOffset) pointer allocation (R.runtime state highwater) binding fresh short ghost race backend ready
  exact ⟨output,child,actual,tag,global,callFrame,witness.parents,witness.owned,
    ⟨witness.node,witness.nodeAt,witness.tag⟩,activation⟩

end
end DuplicatePrefix.CurrentCallPostRole
open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallPostRole" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved post-role dependency {dependency}"
