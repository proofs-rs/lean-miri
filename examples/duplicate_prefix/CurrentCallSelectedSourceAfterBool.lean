import duplicate_prefix.CurrentCallPostEntryCheckpoint
import duplicate_prefix.CurrentCallSpatialEntryActivity
import duplicate_prefix.CurrentCallSelectedBoolCurrent
import duplicate_prefix.CurrentCallSpatialJointInstall
import duplicate_prefix.CurrentCallResourceBoolActivation
import duplicate_prefix.CurrentCallAllocationLicense
import duplicate_prefix.CurrentCallExclusiveWindowFrame
import duplicate_prefix.CurrentCallResourceBorrowGrowth
import duplicate_prefix.CurrentCallBoolWriteRuntime

/-! Bool activation consumes the original return role from the SAME current
joint cover. The temporary protected pointer is discarded; the original return
place remains the later store destination. -/
namespace DuplicatePrefix.CurrentCallSelectedSourceAfterBool
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Input Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization CurrentCallSpatialCover CurrentCallSpatialReturnFrame
open GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowFnEntryRegistration
open CanonicalConfigFacts ActualReferenceContext TypedBorrowSteps ReferenceBorrowDriver CurrentCallBoolProtection
open CurrentCallTypedFnEntry ReturnProtection
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
noncomputable section

private def asReturn {machine tracker sourceContext sourceOffset sourceLength}
    (source : RoleCover machine tracker sourceContext .mut sourceOffset sourceLength)
    (i : Fin source.backing.cells.size) (overlap : CurrentCallSpatialSourceCover.Active source i)
    (byte : AllocId×Nat) (request : Window source.backing.id sourceOffset sourceLength byte)
    (cell : Window source.backing.id source.backing.cells[i].offset source.backing.cells[i].length byte) :
    UniformWindow machine tracker (source.roles i overlap).identities 0 source.backing.id byte.2 1 .ret := by
  let Q := CurrentCallSpatialRows.singleByte source i overlap byte request cell
  refine ⟨Q.loan,Q.pointer,Q.allocation,Q.precise,Q.loanAt,Q.pointerAt,Q.pointerId,Q.present,Q.preciseAt,Q.binding,Q.issued,Q.parents,?_⟩
  intro other hit
  simpa [demandOf] using Q.window other hit

private def reindex {machine tracker data owner id offset length}
    (V : UniformWindow machine tracker data owner id offset length .ret) (newId : AllocId) (same : id=newId) :
    UniformWindow machine tracker data owner newId offset length .ret := by
  refine ⟨V.loan,V.pointer,V.allocation,V.precise,V.loanAt,V.pointerAt,V.pointerId.trans same,?_,?_,V.binding,?_,V.parents,?_⟩
  · simpa only [same] using V.present
  · simpa only [same] using V.preciseAt
  · simpa only [same] using V.issued
  · intro other hit
    apply V.window
    simpa only [same] using hit

/-- One fixed Bool cell/grant drives the actual Read/constructor. Each source
cell keeps its own SAME map, extended at that SAME Bool child. The target is
one byte only to reuse the scalar frame; no operation is split at proof cells. -/
private theorem source_byte {machine tracker sourceContext returnContext sourceOffset sourceLength returnOffset}
    (source : RoleCover machine tracker sourceContext .mut sourceOffset sourceLength)
    (ret : RoleCover machine tracker returnContext .ret returnOffset 1)
    (same : source.backing.id=ret.backing.id)
    (sameAllocation : source.backing.allocation=ret.backing.allocation)
    (separate : ∀byte,Window source.backing.id sourceOffset sourceLength byte→Window ret.backing.id returnOffset 1 byte→False)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts ret.backing.allocation.extra tracker.global)
    (distinct : ret.backing.allocation.extra.roots.toList.Nodup) (short : ret.backing.allocation.extra.nodes.size<65536)
    (nodeRoom : ret.backing.allocation.extra.nodes.size+1≤4294967295)
    (borrowFrame : FrameState) (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (start : UInt64) (startEq : start.toNat=returnOffset)
    (bounds : start.toNat+1≤ret.backing.allocation.extra.locations.size.bytes.toNat)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (entryEq : entry.allocation=ret.backing.allocation)
    (i : Fin source.backing.cells.size) (overlap : CurrentCallSpatialSourceCover.Active source i)
    (byte : AllocId×Nat) (request : Window source.backing.id sourceOffset sourceLength byte)
    (cell : Window source.backing.id source.backing.cells[i].offset source.backing.cells[i].length byte) :
    let V := reindex (asReturn source i overlap byte request cell) ret.backing.id same
    let output := CurrentCallSpatialEntryRead.output ret borrowFrame fresh start 1
    ∃child,output.child.tree.indexOfTag output.tag=some child ∧
      Nonempty (UniformWindow (CurrentCallSpatialSourceInstall.copiedMachine ret borrowFrame fresh start 1 entry)
        ⟨output.global,tracker.retagMode⟩
        (windowData ret.backing.id V.pointer (S05ConcreteProtectedChildCompletion.extend V.precise.completion child (ret.roles (returnIndex ret) (returnOverlap ret)).grant))
        0 ret.backing.id byte.2 1 .ret) := by
  let V := reindex (asReturn source i overlap byte request cell) ret.backing.id same
  have allocationEq : V.allocation=ret.backing.allocation := by
    change source.backing.allocation=ret.backing.allocation
    exact sameAllocation
  have disjoint : ∀other,Window ret.backing.id returnOffset 1 other→Window ret.backing.id byte.2 1 other→False := by
    intro other boolHit pointHit
    have pointEq : other.2=byte.2 := by have := pointHit.2;omega
    apply separate other
    · refine ⟨pointHit.1.trans same.symm,?_,?_⟩
      · rw [pointEq]
        exact request.2.1
      · rw [pointEq]
        exact request.2.2
    · exact boolHit
  exact CurrentCallSpatialReturnFrame.same_selected ret V allocationEq disjoint rfl runtime distinct short nodeRoom borrowFrame fresh start 1 startEq rfl (by decide) bounds
    (returnIndex ret) (returnOverlap ret) entry entryEq

open Lean Elab Tactic in
elab "selected_source_rule " suffix:str : term => do
  let found := (←getEnv).constants.toList.filter (fun (name,_)=>name.toString.endsWith suffix.getString)
  match found with | [(name,_)]=>return mkConst name | _=>throwError "expected checked Bool-frame theorem {suffix.getString}"

/-- A source-byte certificate survives the actual disjoint ranged Write and
actual writeUninit allocation replacement. No post-clear State is required. -/
private theorem after_write_byte {before tracker data owner id off}
    (V : UniformWindow before tracker data owner id off 1 .ret)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts V.allocation.extra tracker.global)
    (provenance : ProvenanceExtra) (offset amount : Size) (visit : ChildrenVisitMode)
    (bounds : offset.bytes.toNat+amount.bytes.toNat≤V.allocation.extra.locations.size.bytes.toNat)
    (capacity : (V.allocation.extra.performBorrowAccessRange provenance offset amount .Write tracker.global.protectedTags visit).tree.locations.size=V.allocation.extra.locations.size)
    (lower upper : UInt64) (lowerEq : lower.toNat=off) (upperEq : upper.toNat=off+1)
    (disjoint : ∀point : UInt64,lower.toNat≤point.toNat→point.toNat<upper.toNat→point.toNat<offset.bytes.toNat ∨(offset.bytes+amount.bytes).toNat≤point.toNat)
    (post : Before) (next : MachineHooks.BorrowState) (updated : Allocation Provenance BorrowTree)
    (present : Present (ActualWorld post) id updated)
    (rootTag : next.global.rootTag? id=tracker.global.rootTag? id)
    (flags : next.global.protectedTags=tracker.global.protectedTags)
    (extra : updated.extra=(V.allocation.extra.performBorrowAccessRange provenance offset amount .Write tracker.global.protectedTags visit).tree)
    (len : updated.len=V.allocation.len) (size : updated.byteSize=V.allocation.byteSize)
    (afterRuntime : DuplicatePrefixBorrowContract.RuntimeFacts updated.extra next.global) :
    ∃Q : UniformWindow post next data owner id off 1 .ret,Q.allocation=updated ∧Q.pointer=V.pointer ∧Q.precise=V.precise := by
  let written := V.allocation.extra.performBorrowAccessRange provenance offset amount .Write tracker.global.protectedTags visit
  have frame := GeneralBorrowFreshReadFrame.frame V.allocation.extra provenance offset amount .Write tracker.global.protectedTags visit
  have nodeFrame := congrArg BorrowTree.nodes frame
  have nodes : written.tree.nodes=V.allocation.extra.nodes := nodeFrame
  have rootFrame := congrArg BorrowTree.roots frame
  have roots : written.tree.roots=V.allocation.extra.roots := rootFrame
  have tagFrame := congrArg BorrowTree.tagMapping frame
  have tags : written.tree.tagMapping=V.allocation.extra.tagMapping := tagFrame
  have initial := (selected_source_rule ".CurrentCallResourceFnEntry.window_owned") V (by rfl) runtime lower upper (by omega) (by omega)
  have resultRuntime : DuplicatePrefixBorrowContract.RuntimeFacts written.tree next.global := by rw [extra] at afterRuntime;exact afterRuntime
  have retained := (CurrentCallExclusiveWindowFrame.write_outside V.allocation.extra V.precise.completion tracker.global.protectedTags V.pointer.grant provenance offset amount visit lower upper runtime.formed.well bounds disjoint initial).2
  have parents : ParentInterpretation updated.extra V.precise.completion := by
    rw [extra,frame]
    exact (selected_source_rule ".CurrentCallSpatialReturnFrame.parents_locations") V.allocation.extra _ V.precise.completion V.parents
  have issued := CurrentCallAllocationLicense.spatial V.issued post next updated present rootTag len size
    (by rw [extra];exact capacity)
    (by intro position root found;rw [extra,roots];exact found)
    (by intro index node found;refine ⟨node,?_,rfl,rfl,rfl,rfl⟩;rw [extra,nodes];exact found)
    V.precise.completion (by intros;assumption)
  have binding : PointerBinds updated V.pointer := by
    obtain ⟨node,nodeAt,_,value⟩ := V.binding
    have foundAt : updated.extra.nodes.get V.pointer.grant=some node := by rw [extra,nodes];exact nodeAt
    exact ⟨node,foundAt,afterRuntime.formed.allocator.nodeTags _ _ foundAt,value⟩
  refine ⟨⟨V.loan,V.pointer,updated,V.precise,V.loanAt,V.pointerAt,V.pointerId,present,V.preciseAt,binding,issued,parents,?_⟩,rfl,rfl,rfl⟩
  intro byte inside
  refine ⟨by rw [len];exact (V.window byte inside).1,?_⟩
  intro segment member lo hi index node nodeAt
  have writtenMember : segment∈written.tree.locations.entries.toList := by rw [extra] at member;exact member
  obtain ⟨position,valid,same⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp writtenMember)
  subst segment
  have byteEq : byte.2=off := by have := inside.2;omega
  dsimp only [written] at lo hi valid
  have rights := retained position valid (by omega) (by rw [upperEq];omega) (by rw [lowerEq];omega) index node (by rw [extra] at nodeAt;exact nodeAt)
  have writtenAt : written.tree.nodes.get index=some node := by rw [extra] at nodeAt;exact nodeAt
  have rowPossible := resultRuntime.possible position valid index node writtenAt
  have rowProfile := (resultRuntime.formed.profile position valid).present index node writtenAt
  have realized := CandidateCurrentGrantRuntime.realized _ _ rowPossible rowProfile
  rw [flags] at realized
  rw [flags]
  constructor
  · intro below
    exact (selected_source_rule ".CurrentCallResourceFnEntry.local_token") _ _ realized (rights.1 below)
  · intro clash
    apply Classical.byContradiction
    intro outside
    exact (selected_source_rule ".CurrentCallResourceFnEntry.foreign_no_clash") _ _ realized (rights.2 outside) clash

def written {machine tracker returnContext returnOffset}
    (ret : RoleCover machine tracker returnContext .ret returnOffset 1) (borrowFrame : FrameState)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615) (start : UInt64) :=
  let output := CurrentCallSpatialEntryRead.output ret borrowFrame fresh start 1
  output.child.tree.performBorrowAccessRange (.concrete output.tag) (Size.ofBytes start) (Size.ofBytes 1)
    .Write output.global.protectedTags .VisitChildrenOfAccessed

/-- Universal source-cell framing for the SAME one Bool operation. The child,
Bool origin and each cell completion are fixed before quantifying source bytes. -/
theorem same_cells {machine tracker sourceContext returnContext sourceOffset sourceLength returnOffset}
    (source : RoleCover machine tracker sourceContext .mut sourceOffset sourceLength)
    (ret : RoleCover machine tracker returnContext .ret returnOffset 1)
    (same : source.backing.id=ret.backing.id)
    (sameAllocation : source.backing.allocation=ret.backing.allocation)
    (separate : ∀byte,Window source.backing.id sourceOffset sourceLength byte→Window ret.backing.id returnOffset 1 byte→False)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts ret.backing.allocation.extra tracker.global)
    (distinct : ret.backing.allocation.extra.roots.toList.Nodup) (short : ret.backing.allocation.extra.nodes.size<65536)
    (nodeRoom : ret.backing.allocation.extra.nodes.size+1≤4294967295)
    (borrowFrame : FrameState) (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (start : UInt64) (startEq : start.toNat=returnOffset)
    (bounds : start.toNat+1≤ret.backing.allocation.extra.locations.size.bytes.toNat)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (entryEq : entry.allocation=ret.backing.allocation)
    (child : UniIndex)
    (lookup : (CurrentCallSpatialEntryRead.output ret borrowFrame fresh start 1).child.tree.indexOfTag tracker.global.nextPointerTag=some child)
    (ctorRuntime : DuplicatePrefixBorrowContract.RuntimeFacts (CurrentCallSpatialEntryRead.output ret borrowFrame fresh start 1).child.tree
      (CurrentCallSpatialEntryRead.output ret borrowFrame fresh start 1).global)
    (ctorCapacity : (CurrentCallSpatialEntryRead.output ret borrowFrame fresh start 1).child.tree.locations.size=ret.backing.allocation.extra.locations.size)
    (writeCapacity : (written ret borrowFrame fresh start).tree.locations.size=(CurrentCallSpatialEntryRead.output ret borrowFrame fresh start 1).child.tree.locations.size)
    (post : Before) (updated : Allocation Provenance BorrowTree) (present : Present (ActualWorld post) ret.backing.id updated)
    (extra : updated.extra=(written ret borrowFrame fresh start).tree)
    (len : updated.len=ret.backing.allocation.len) (size : updated.byteSize=ret.backing.allocation.byteSize)
    (afterRuntime : DuplicatePrefixBorrowContract.RuntimeFacts updated.extra (CurrentCallSpatialEntryRead.output ret borrowFrame fresh start 1).global) :
    ∀(i : Fin source.backing.cells.size) (overlap : CurrentCallSpatialSourceCover.Active source i)
      (byte : AllocId×Nat) (request : Window source.backing.id sourceOffset sourceLength byte)
      (cell : Window source.backing.id source.backing.cells[i].offset source.backing.cells[i].length byte),
      ∃Q : UniformWindow post ⟨(CurrentCallSpatialEntryRead.output ret borrowFrame fresh start 1).global,tracker.retagMode⟩
        (windowData ret.backing.id (source.family.at (source.roles i overlap).grant)
          (S05ConcreteProtectedChildCompletion.extend source.backing.cells[i].completion child (ret.roles (returnIndex ret) (returnOverlap ret)).grant))
        0 ret.backing.id byte.2 1 .ret,
        Q.allocation=updated ∧Q.pointer=source.family.at (source.roles i overlap).grant ∧
        Q.precise.completion=S05ConcreteProtectedChildCompletion.extend source.backing.cells[i].completion child (ret.roles (returnIndex ret) (returnOverlap ret)).grant := by
  intro i overlap byte request cell
  obtain ⟨other,otherLookup,⟨V⟩⟩ := source_byte source ret same sameAllocation separate runtime distinct short nodeRoom borrowFrame fresh start startEq bounds entry entryEq i overlap byte request cell
  have equal : other=child := Option.some.inj (otherLookup.symm.trans lookup)
  subst other
  change UniformWindow (CurrentCallSpatialSourceInstall.copiedMachine ret borrowFrame fresh start 1 entry)
    ⟨(CurrentCallSpatialEntryRead.output ret borrowFrame fresh start 1).global,tracker.retagMode⟩
    (windowData ret.backing.id (source.family.at (source.roles i overlap).grant)
      (S05ConcreteProtectedChildCompletion.extend source.backing.cells[i].completion child (ret.roles (returnIndex ret) (returnOverlap ret)).grant))
    0 ret.backing.id byte.2 1 .ret at V
  have fields := (selected_source_rule ".CurrentCallSpatialJointInstall.canonical_fields") _ _ V
  have allocationEq : V.allocation=ret.backing.allocation.setExtra (CurrentCallSpatialEntryRead.output ret borrowFrame fresh start 1).child.tree := by
    have selected := V.present
    simp only [Present,ActualWorld,Array.toList_map] at selected
    obtain ⟨row,member,equal⟩ := List.mem_map.mp selected
    have idEq : row.1=ret.backing.id := (Prod.mk.inj equal).1
    change row∈((machine.memory.live.filter (fun r=>r.1!=ret.backing.id)).push
      (ret.backing.id,{entry with allocation:=entry.allocation.setExtra (CurrentCallSpatialEntryRead.output ret borrowFrame fresh start 1).child.tree})).toList at member
    rcases Array.mem_push.mp (Array.mem_toList_iff.mp member) with old|last
    · have excluded := (Array.mem_filter.mp old).2
      simp [idEq] at excluded
    · have alloc := (Prod.mk.inj equal).2
      rw [last] at alloc
      simpa only [entryEq] using alloc.symm
  have currentRuntime : DuplicatePrefixBorrowContract.RuntimeFacts V.allocation.extra (CurrentCallSpatialEntryRead.output ret borrowFrame fresh start 1).global := by
    rw [allocationEq]
    exact ctorRuntime
  have pointBound := (V.window (ret.backing.id,byte.2) ⟨rfl,Nat.le_refl _,by omega⟩).1
  have fits : byte.2+1<2^64 := by have := V.issued.capability.extent;have := UInt64.toNat_lt V.allocation.byteSize.bytes;omega
  let lower := UInt64.ofNat byte.2
  let upper := UInt64.ofNat (byte.2+1)
  have lowerEq : lower.toNat=byte.2 := by simp only [lower,UInt64.toNat_ofNat',Nat.mod_eq_of_lt (by omega : byte.2<2^64)]
  have upperEq : upper.toNat=byte.2+1 := by simp only [upper,UInt64.toNat_ofNat',Nat.mod_eq_of_lt fits]
  have boolEnd : (start+1).toNat=returnOffset+1 := by
    have noWrap : start.toNat+1<2^64 := Nat.lt_of_le_of_lt bounds (UInt64.toNat_lt ret.backing.allocation.extra.locations.size.bytes)
    rw [UInt64.toNat_add,startEq,show (1:UInt64).toNat=1 from rfl,Nat.mod_eq_of_lt (by omega)]
  have disjoint : ∀point : UInt64,lower.toNat≤point.toNat→point.toNat<upper.toNat→point.toNat<start.toNat ∨(start+1).toNat≤point.toNat := by
    intro point lo hi
    have pointEq : point.toNat=byte.2 := by omega
    by_cases early : point.toNat<start.toNat
    · exact Or.inl early
    · apply Or.inr
      apply Nat.le_of_not_gt
      intro inside
      apply separate (ret.backing.id,point.toNat)
      · exact ⟨same.symm,by rw [pointEq];exact request.2.1,by rw [pointEq];exact request.2.2⟩
      · exact ⟨rfl,by omega,by omega⟩
  have writeBounds : start.toNat+1≤V.allocation.extra.locations.size.bytes.toNat := by rw [allocationEq];exact ctorCapacity ▸ bounds
  obtain ⟨Q,actualAllocation,actualPointer,actualPrecise⟩ := after_write_byte V currentRuntime (.concrete tracker.global.nextPointerTag) (Size.ofBytes start) (Size.ofBytes 1) .VisitChildrenOfAccessed writeBounds
    (by simpa only [allocationEq,Allocation.setExtra,Allocation.mapExtra,written,CurrentCallSpatialEntryRead.output] using writeCapacity)
    lower upper lowerEq upperEq disjoint post ⟨(CurrentCallSpatialEntryRead.output ret borrowFrame fresh start 1).global,tracker.retagMode⟩ updated present rfl rfl
    (by simpa only [allocationEq,Allocation.setExtra,Allocation.mapExtra,written,CurrentCallSpatialEntryRead.output] using extra)
    (by simpa only [allocationEq,Allocation.setExtra,Allocation.mapExtra,Allocation.len] using len)
    (by simpa only [allocationEq,Allocation.setExtra,Allocation.mapExtra,Allocation.byteSize] using size) afterRuntime
  exact ⟨Q,actualAllocation,actualPointer.trans fields.1,(congrArg PreciseAllocation.completion actualPrecise).trans fields.2⟩

/-- Fixed per-cell scalar frames assemble without selecting a new completion. -/
def updates_of_cells {before tracker context offset length}
    (source : RoleCover before tracker context .mut offset length)
    (post : Before) (next : MachineHooks.BorrowState) (allocation : Allocation Provenance BorrowTree)
    (grant : UniIndex) (completions : Fin source.backing.cells.size → Completion)
    (grants : ∀i overlap,(source.roles i overlap).grant=grant)
    (frames : ∀(i : Fin source.backing.cells.size) (overlap : CurrentCallSpatialSourceCover.Active source i)
      (byte : AllocId×Nat) (request : Window source.backing.id offset length byte)
      (cell : Window source.backing.id source.backing.cells[i].offset source.backing.cells[i].length byte),
      ∃(data : Identities) (Q : UniformWindow post next data 0 source.backing.id byte.2 1 .ret),
        Q.allocation=allocation ∧Q.pointer=source.family.at (source.roles i overlap).grant ∧Q.precise.completion=completions i)
    (i : Fin source.backing.cells.size) (overlap : CurrentCallSpatialSourceCover.Active source i) :
    CurrentCallSpatialSourceCover.Update source post next allocation source.family grant i overlap := by
  apply Classical.choice
  refine ?_
  have pointExists:=overlap
  obtain ⟨byte,request,cell⟩:=pointExists
  obtain ⟨data,Q,allocEq,pointerEq,completionEq⟩:=frames i overlap byte request cell
  have parents : ParentInterpretation allocation.extra (completions i) := by
    rw [←allocEq,←completionEq]
    exact Q.parents
  refine ⟨⟨⟨source.backing.cells[i].offset,source.backing.cells[i].length,completions i,parents⟩,rfl,rfl,?_,?_,?_⟩⟩
  · simpa only [allocEq,pointerEq,grants i overlap] using Q.binding
  · simpa only [allocEq,pointerEq,completionEq,grants i overlap,Family.at] using Q.issued
  · intro point requestHit cellHit
    obtain ⟨otherData,R,otherAlloc,otherPointer,otherCompletion⟩:=frames i overlap point requestHit cellHit
    have pointHit : Window source.backing.id point.2 1 point:=⟨requestHit.1,Nat.le_refl _,by omega⟩
    simpa only [otherAlloc,otherPointer,otherCompletion,grants i overlap,Family.at,demandOf,reduceCtorEq,ite_false] using R.window point pointHit

private theorem other_transport {machine tracker data owner id off}
    (V : UniformWindow machine tracker data owner id off 1 .ret)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts V.allocation.extra tracker.global)
    (borrowFrame : FrameState) (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (boolId : AllocId) (post : Before) (next : MachineHooks.BorrowState)
    (global : next.global=(registered tracker.global borrowFrame boolId fresh).1)
    (present : Present (ActualWorld post) id V.allocation) :
    ∃Q : UniformWindow post next data owner id off 1 .ret,Q.allocation=V.allocation ∧Q.pointer=V.pointer ∧Q.precise=V.precise := by
  let current := CurrentCallResourceFnEntry.registered_window V runtime borrowFrame fresh
  have fields := (selected_source_rule ".CurrentCallSpatialEntryRead.registered_window_fields") V runtime borrowFrame fresh
  have issued := CurrentCallAllocationLicense.spatial V.issued post next V.allocation present (by rw [global];rfl) rfl rfl rfl
    (by intros;assumption) (by intro index node found;exact ⟨node,found,rfl,rfl,rfl,rfl⟩) V.precise.completion (by intros;assumption)
  refine ⟨⟨V.loan,V.pointer,V.allocation,V.precise,V.loanAt,V.pointerAt,V.pointerId,present,V.preciseAt,V.binding,issued,V.parents,?_⟩,rfl,rfl,rfl⟩
  intro byte inside
  have available := current.window byte inside
  rw [fields.1,fields.2.1,fields.2.2] at available
  rw [global]
  exact available

/-- Unchanged source rows keep all fixed cells under the actual registration. -/
theorem other_cells {before tracker context offset length}
    (source : RoleCover before tracker context .mut offset length)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts source.backing.allocation.extra tracker.global)
    (frame : FrameState) (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (boolId : AllocId) (post : Before) (next : MachineHooks.BorrowState)
    (global : next.global=(registered tracker.global frame boolId fresh).1)
    (present : Present (ActualWorld post) source.backing.id source.backing.allocation)
    (i : Fin source.backing.cells.size) (overlap : CurrentCallSpatialSourceCover.Active source i)
    (byte : AllocId×Nat) (request : Window source.backing.id offset length byte)
    (cell : Window source.backing.id source.backing.cells[i].offset source.backing.cells[i].length byte) :
    ∃(data : Identities) (Q : UniformWindow post next data 0 source.backing.id byte.2 1 .ret),
      Q.allocation=source.backing.allocation ∧Q.pointer=source.family.at (source.roles i overlap).grant ∧
      Q.precise.completion=source.backing.cells[i].completion := by
  let V:=asReturn source i overlap byte request cell
  have fields := (selected_source_rule ".CurrentCallSpatialJointInstall.canonical_fields") _ _ V
  obtain ⟨Q,allocation,pointer,precise⟩:=other_transport V runtime frame fresh boolId post next global present
  exact ⟨_,Q,allocation,pointer.trans fields.1,(congrArg PreciseAllocation.completion precise).trans fields.2⟩

def same_updates {machine tracker sourceContext returnContext sourceOffset sourceLength returnOffset}
    (source : RoleCover machine tracker sourceContext .mut sourceOffset sourceLength)
    (ret : RoleCover machine tracker returnContext .ret returnOffset 1)
    (same : source.backing.id=ret.backing.id)
    (sameAllocation : source.backing.allocation=ret.backing.allocation)
    (separate : ∀byte,Window source.backing.id sourceOffset sourceLength byte→Window ret.backing.id returnOffset 1 byte→False)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts ret.backing.allocation.extra tracker.global)
    (distinct : ret.backing.allocation.extra.roots.toList.Nodup) (short : ret.backing.allocation.extra.nodes.size<65536)
    (nodeRoom : ret.backing.allocation.extra.nodes.size+1≤4294967295)
    (borrowFrame : FrameState) (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (start : UInt64) (startEq : start.toNat=returnOffset)
    (bounds : start.toNat+1≤ret.backing.allocation.extra.locations.size.bytes.toNat)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (entryEq : entry.allocation=ret.backing.allocation)
    (child : UniIndex)
    (lookup : (CurrentCallSpatialEntryRead.output ret borrowFrame fresh start 1).child.tree.indexOfTag tracker.global.nextPointerTag=some child)
    (ctorRuntime : DuplicatePrefixBorrowContract.RuntimeFacts (CurrentCallSpatialEntryRead.output ret borrowFrame fresh start 1).child.tree
      (CurrentCallSpatialEntryRead.output ret borrowFrame fresh start 1).global)
    (ctorCapacity : (CurrentCallSpatialEntryRead.output ret borrowFrame fresh start 1).child.tree.locations.size=ret.backing.allocation.extra.locations.size)
    (writeCapacity : (written ret borrowFrame fresh start).tree.locations.size=(CurrentCallSpatialEntryRead.output ret borrowFrame fresh start 1).child.tree.locations.size)
    (post : Before) (updated : Allocation Provenance BorrowTree) (present : Present (ActualWorld post) ret.backing.id updated)
    (extra : updated.extra=(written ret borrowFrame fresh start).tree)
    (len : updated.len=ret.backing.allocation.len) (size : updated.byteSize=ret.backing.allocation.byteSize)
    (afterRuntime : DuplicatePrefixBorrowContract.RuntimeFacts updated.extra (CurrentCallSpatialEntryRead.output ret borrowFrame fresh start 1).global)
    (grant : UniIndex) (grants : ∀i overlap,(source.roles i overlap).grant=grant)
    (i : Fin source.backing.cells.size) (overlap : CurrentCallSpatialSourceCover.Active source i) :
    CurrentCallSpatialSourceCover.Update source post
      ⟨(CurrentCallSpatialEntryRead.output ret borrowFrame fresh start 1).global,tracker.retagMode⟩
      updated source.family grant i overlap := by
  apply updates_of_cells source post _ updated grant
    (fun i=>S05ConcreteProtectedChildCompletion.extend source.backing.cells[i].completion child
      (ret.roles (returnIndex ret) (returnOverlap ret)).grant) grants ?_ i overlap
  intro j active byte request cell
  obtain ⟨Q,alloc,pointer,completion⟩:=same_cells source ret same sameAllocation separate runtime distinct short nodeRoom
    borrowFrame fresh start startEq bounds entry entryEq child lookup ctorRuntime ctorCapacity writeCapacity
    post updated present extra len size afterRuntime j active byte request cell
  exact ⟨_,reindex Q source.backing.id same.symm,alloc,pointer,completion⟩

theorem source_grants {before tracker offset len}
    (source : CurrentCallPostEntryCheckpoint.Source before tracker offset len)
    (i : Fin source.role.backing.cells.size) (overlap : CurrentCallSpatialSourceCover.Active source.role i) :
    (source.role.roles i overlap).grant=source.grant := by
  have binding : PointerBinds source.role.backing.allocation (source.role.family.at source.grant) := by
    refine ⟨source.node,source.nodeAt,source.runtime.formed.allocator.nodeTags _ _ source.nodeAt,?_⟩
    change match source.role.family.value.provenance with
      | .concrete id tag => id=source.role.family.allocation ∧tag=source.node.tag
      | .wildcard => source.node.isExposed=true
    rw [source.concrete]
    exact ⟨source.role.id.symm,source.nodeTag.symm⟩
  exact CurrentCallSpatialCover.concrete_grant_eq (source.role.roles i overlap).binding binding source.concrete source.concrete

/-- Actual selected-cell frames and physical data form the common source packet. -/
theorem assemble {before tracker offset len}
    (source : CurrentCallPostEntryCheckpoint.Source before tracker offset len)
    (post : Before) (next : MachineHooks.BorrowState) (allocation : Allocation Provenance BorrowTree)
    (live : Present (ActualWorld post) source.role.backing.id allocation)
    (updates : ∀i overlap,CurrentCallSpatialSourceCover.Update source.role post next allocation source.role.family source.grant i overlap)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts allocation.extra next.global)
    (distinct : allocation.extra.roots.toList.Nodup)
    (node : TreeNode) (nodeAt : allocation.extra.nodes.get source.grant=some node)
    (nodeTag : node.tag=source.tag) (hidden : node.isExposed=false)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin allocation.extra source.grant .Write
      (UInt64.ofNat offset) (UInt64.ofNat offset+len))
    (binding : CandidateCallBindings.WindowBinding post source.role.family.value source.role.backing.id offset len.toNat)
    (nodes : allocation.extra.nodes.size+6<65536)
    (storage : CurrentCallResourceEntrySourceStorage.Data allocation (UInt64.ofNat offset) len)
    (profile : CurrentCallBoolProtection.WindowReady post source.role.backing.id offset len.toNat) :
    ∃current : CurrentCallPostEntryCheckpoint.Source post next offset len,
      CurrentCallPostEntryCheckpoint.CopyReady current ∧current.role.family=source.role.family ∧
      current.role.backing.allocation=allocation ∧current.role.backing.id=source.role.backing.id ∧
      current.tag=source.tag ∧current.grant=source.grant := by
  let role:=CurrentCallSpatialSourceCover.assemble source.role live updates source.role.id
  let current : CurrentCallPostEntryCheckpoint.Source post next offset len := {
    context:=CurrentCallSpatialSourceCover.context source.role live updates
    role:=role,runtime:=runtime,distinct:=distinct,tag:=source.tag,concrete:=source.concrete,
    grant:=source.grant,node:=node,nodeAt:=nodeAt,nodeTag:=nodeTag,hidden:=hidden,activity:=active,
    binding:=binding,positive:=source.positive,signedFits:=source.signedFits,nodes:=nodes }
  exact ⟨current,⟨storage,profile⟩,rfl,rfl,rfl,rfl,rfl⟩

/-- The actual selected Bool sequence retains a distinct hidden source leaf. -/
theorem source_activity {before tracker data owner id offset}
    (W : UniformWindow before tracker data owner id offset 1 .ret)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (frame : FrameState) (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (distinct : W.allocation.extra.roots.toList.Nodup) (short : W.allocation.extra.nodes.size+1<65536)
    (start : UInt64) (startEq : start.toNat=offset)
    (output : GeneralBorrowForestFnEntry.Output) (child : UniIndex)
    (actual : CandidateCurrentFnEntryRaw.operation W.allocation.extra tracker.global frame id W.pointer.value.provenance start 1=.ok output)
    (witness : CurrentCallResourceFnEntry.BorrowWitness W output child start 1)
    (tag : output.tag=tracker.global.nextPointerTag)
    (post : Before) (present : Present (ActualWorld post) id (W.allocation.setExtra output.child.tree))
    (rootTag : output.global.rootTag? id=tracker.global.rootTag? id)
    (target : UniIndex) (node : TreeNode) (nodeAt : W.allocation.extra.nodes.get target=some node)
    (leaf : node.children=#[]) (hidden : node.isExposed=false) (different : target≠W.pointer.grant)
    (newDifferent : target≠child)
    (lower upper : UInt64) (active : GeneralBorrowFreshActiveWithin.ActiveWithin W.allocation.extra target .Write lower upper) :
    let written := output.child.tree.performBorrowAccessRange (.concrete output.tag) (Size.ofBytes start) (Size.ofBytes 1)
      .Write output.global.protectedTags .VisitChildrenOfAccessed
    ∃next,written.tree.nodes.get target=some next ∧next.tag=node.tag ∧next.children=#[] ∧next.isExposed=false ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin written.tree target .Write lower upper := by
  have bounds : start.toNat+1≤W.allocation.extra.locations.size.bytes.toNat := by
    have hit:=(W.window (id,offset) ⟨rfl,Nat.le_refl _,by omega⟩).1
    rw [W.issued.capability.treeExtent,←W.issued.capability.extent]
    omega
  have nodeRoom : W.allocation.extra.nodes.size+1≤4294967295 := by omega
  obtain ⟨next,atNext,nextTag,_,nextChildren,nextHidden,nextActive⟩ :=
    (selected_source_rule ".CurrentCallSpatialEntryActivity.fnentry_frame") W runtime frame fresh rfl distinct (by omega) nodeRoom
      start 1 startEq rfl (by decide) bounds output actual target node nodeAt leaf hidden different lower upper active
  have writeFacts:=CurrentCallSelectedBoolCurrent.operation_runtime W runtime frame fresh distinct short start startEq
    output child actual witness tag post present rootTag .VisitChildrenOfAccessed
  let childNode := witness.node
  have childAt := witness.nodeAt
  have childTag := witness.tag
  have retained := (selected_source_rule ".CurrentCallSpatialEntryActivity.write_frame") output.child.tree output.global
    (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) witness.runtime witness.parents
    child target childNode next childAt atNext (nextChildren.trans leaf) (nextHidden.trans hidden) newDifferent start 1 lower upper
    (by rw [witness.capacity];exact bounds) witness.owned nextActive
  have childTagEq : childNode.tag=output.tag := childTag
  rw [childTagEq] at retained
  exact ⟨next,by rw [writeFacts.2.2.2.2.1];exact atNext,nextTag,nextChildren.trans leaf,nextHidden.trans hidden,retained⟩

end
end DuplicatePrefix.CurrentCallSelectedSourceAfterBool

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallSelectedSourceAfterBool" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved selected source Bool frame dependency {dependency}"
