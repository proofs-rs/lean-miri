import duplicate_prefix.CurrentCallLazyBoolTyped
import duplicate_prefix.CurrentCallSpatialRows
import duplicate_prefix.CurrentCallOtherAllocationWindow

/-! Fixed source-cell resources across actual latent Bool protection. The new
protector has no old source node; no source cell, grant, family or completion is
chosen again. Actual other-ID presence is discharged by the protected outcome. -/
namespace DuplicatePrefix.CurrentCallLazyBoolSourceFrame
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CurrentCallSpatialCover CurrentCallSpatialRows
open CanonicalConfigFacts ActualReferenceContext TypedBorrowSteps ReferenceBorrowDriver
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

variable {before : Before} {tracker : MachineHooks.BorrowState} {ctx : Context before}
    {offset length : Nat} (source : RoleCover before tracker ctx .mut offset length)
    (post : Before) (present : Present (ActualWorld post) source.backing.id source.backing.allocation)

def backing : AllocationCover post where
  id:=source.backing.id
  allocation:=source.backing.allocation
  live:=present
  cells:=source.backing.cells
  disjoint:=source.backing.disjoint

def context : Context post where
  allocations:=#[backing source post present]
  unique:=by simp

/-- Pure transport on the actual preserved allocation. All old cells and their
assignments remain fixed, including every overlapping wildcard grant. -/
def role (runtime : DuplicatePrefixBorrowContract.RuntimeFacts source.backing.allocation.extra tracker.global)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615) :
    RoleCover post (registeredTracker (allocatedTracker tracker fresh) tracker.global.nextPointerTag)
      (context source post present) .mut offset length where
  family:=source.family
  backing:=backing source post present
  backingAt:=by simp [context]
  id:=source.id
  covered:=source.covered
  roles:=by
    intro i overlap
    let old:=source.roles i overlap
    have issued:=CurrentCallResourceInstallation.spatial_frame old.issued post
      (registeredTracker (allocatedTracker tracker fresh) tracker.global.nextPointerTag)
      source.backing.allocation.extra present rfl rfl (by intros;assumption)
      (by intro index node found;exact ⟨node,found,rfl,rfl,rfl,rfl⟩)
      (source.backing.cells[i.val]'i.isLt).completion (by intros;assumption)
    refine ⟨old.grant,old.binding,issued,?_⟩
    intro byte request cell
    obtain ⟨bound,authority⟩:=old.available byte request cell
    refine ⟨bound,?_⟩
    intro segment member lower upper index node found
    have older:=GeneralBorrowParentTagInvariant.parent_below_fresh source.backing.allocation.extra tracker.global runtime index node found
    have different : node.tag≠tracker.global.nextPointerTag := by
      intro equal
      rw [equal] at older
      exact UInt64.lt_irrefl _ older
    have flags : (registeredTracker (allocatedTracker tracker fresh) tracker.global.nextPointerTag).global.protectedTags.contains node.tag=
        tracker.global.protectedTags.contains node.tag :=
      ProtectorInsertion.contains_other tracker.global.protectedTags tracker.global.nextPointerTag node.tag .StrongProtector different
    rw [flags]
    exact authority segment member lower upper index node found

/-- The actual latent Bool operation retains the current source's ENTIRE
fixed cell assignment. Source/Bool inequality follows from the original live
source and absent Bool; no caller supplies it or a post-state resource. -/
theorem protect_with_source (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (retagCtx : ActualRetagContext.Context options remaining span)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker=some borrowFrame)
    (machine : Before) (tracker : MachineHooks.BorrowState) (sourceCtx : Context machine)
    (start count : Nat) (source : RoleCover machine tracker sourceCtx .mut start count)
    (sourceRuntime : DuplicatePrefixBorrowContract.RuntimeFacts source.backing.allocation.extra tracker.global)
    (family : Family) (root : BorTag) (image : Allocation CtfeProvenance Unit)
    (base offset : UInt64) (place : MPlaceTy Provenance)
    (ready : CurrentCallLazyBoolEnsure.Ready options (Storage.withCurrent frames frame machine) tracker family root image base offset place)
    (noFunction : machine.memory.hasFunctionPointer family.allocation=false)
    (noVaList : machine.memory.hasVaListId family.allocation=false)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (ghost : machine.user.payload.ghost=false) (backend : machine.user.payload.payload.user.backend=.none) :
    ∃post : RootState, ∃output : CurrentCallPostEntryCheckpoint.Return post.machine
        (registeredTracker (allocatedTracker tracker fresh) tracker.global.nextPointerTag) place,
      ∃newCtx : Context post.machine, ∃current : RoleCover post.machine
        (registeredTracker (allocatedTracker tracker fresh) tracker.global.nextPointerTag) newCtx .mut start count,
      TypedRetag.protectInPlaceFunctionArgument (config options remaining span).retag options.limits.retag place
        (Storage.withCurrent frames frame machine)=.ok () post ∧
      current.family=source.family ∧current.backing.allocation=source.backing.allocation ∧
      HEq current.backing.cells source.backing.cells ∧
      output.id=family.allocation ∧output.offset=offset.toNat ∧output.original=family.at allocationRoot ∧output.node.tag=tracker.global.nextPointerTag ∧output.window.allocation.extra.nodes.size≤2 ∧
      post.machine.borrowTracker=some (registeredTracker (allocatedTracker tracker fresh) tracker.global.nextPointerTag) ∧
      post.stack=(Storage.withCurrent frames (registeredFrame frame borrowFrame family.allocation tracker.global.nextPointerTag) machine).stack ∧
      post.machine={MemoryExtras.putAllocation (GlobalDataOnlyActualConfig.extras options) machine family.allocation ⟨none,#[]⟩ with
        memory:={machine.memory with live:=((machine.memory.live.filter (fun row=>row.1!=family.allocation)).push (family.allocation,⟨.machine .global,output.window.allocation⟩))},
        borrowTracker:=some (registeredTracker (allocatedTracker tracker fresh) tracker.global.nextPointerTag)} ∧
      post.machine.user.addresses=machine.user.addresses ∧
      post.machine.memory.live=(machine.memory.live.filter (fun row=>row.1!=family.allocation)).push
        (family.allocation,⟨.machine .global,output.window.allocation⟩) ∧
      post.machine.user.payload.payload.user.runtime.extras.allocations=
        (machine.user.payload.payload.user.runtime.extras.allocations.filter (fun row=>row.1!=family.allocation)).push
          (family.allocation,⟨none,#[]⟩) := by
  obtain ⟨post,data,owner,Q,actual,tracked,stack,runtime,live,machineEq,addresses,extras,issued,binding,output,idEq,offsetEq,originalEq,outputTag,outputAllocation,outputNodes⟩:=
    CurrentCallLazyBoolTyped.protect options remaining span retagCtx frames frame borrowFrame frameBorrow machine tracker
      family root image base offset place ready noFunction noVaList fresh ghost backend
  have old:=source.backing.live
  simp only [Present,ActualWorld,Array.toList_map] at old
  obtain ⟨row,member,equal⟩:=List.mem_map.mp old
  have rowId : row.1=source.backing.id:=(Prod.mk.inj equal).1
  have different : source.backing.id≠family.allocation := by
    intro same
    have missing:=Array.find?_eq_none.mp ready.absent row (Array.mem_toList_iff.mp member)
    simp only [rowId,same,beq_self_eq_true] at missing
    exact missing trivial
  have present : Present (ActualWorld post.machine) source.backing.id source.backing.allocation := by
    simp only [Present,ActualWorld,Array.toList_map]
    apply List.mem_map.mpr
    refine ⟨row,?_,equal⟩
    apply Array.mem_toList_iff.mpr
    rw [live]
    apply Array.mem_push.mpr
    apply Or.inl
    exact Array.mem_filter.mpr ⟨Array.mem_toList_iff.mp member,by simpa only [rowId,bne_iff_ne] using different⟩
  let current:=role source post.machine present sourceRuntime fresh
  refine ⟨post,output,context source post.machine present,current,actual,rfl,rfl,HEq.rfl,
    idEq,offsetEq,originalEq,outputTag,outputNodes,tracked,stack,?_,addresses,?_,extras⟩
  · rw [outputAllocation];exact machineEq
  · rw [outputAllocation];exact live

end
end DuplicatePrefix.CurrentCallLazyBoolSourceFrame
