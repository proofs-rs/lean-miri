import duplicate_prefix.CurrentCallLazyBoolCheckpoint

/-! Derived tag separation for the actual two-node latent Bool forest.
The root/source inequality is current numeric metadata at the internal phase;
full entry derives it from the original cached-root bound before q is created. -/
namespace DuplicatePrefix.CurrentCallLazyBoolTagSeparation
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CurrentCallSpatialCover CurrentCallPostEntryCheckpoint
open CanonicalConfigFacts ActualReferenceContext TypedBorrowSteps ReferenceBorrowDriver
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

theorem node_tag {before : Before} {tracker : MachineHooks.BorrowState} {place : MPlaceTy Provenance}
    (output : Return before tracker place) (root : BorTag)
    (small : output.window.allocation.extra.nodes.size≤2)
    (rootGrant : output.original.grant=allocationRoot)
    (rootValue : output.original.value.provenance=.concrete output.id root)
    (index : UniIndex) (node : TreeNode) (found : output.window.allocation.extra.nodes.get index=some node) :
    node.tag=root ∨node.tag=output.node.tag := by
  obtain ⟨original,originalAt,_,originalValue⟩:=output.originalBinding
  rw [rootValue] at originalValue
  rw [rootGrant] at originalAt
  have childDifferent : output.window.pointer.grant≠allocationRoot := by
    intro equal
    have edge:=output.edge
    rw [equal,rootGrant,output.window.parents.primaryNone] at edge
    cases edge
  have childBound:=GeneralBorrowNodeUpdate.lookup_valid output.window.allocation.extra.nodes output.window.pointer.grant output.node output.nodeAt
  change output.window.pointer.grant.toNat<output.window.allocation.extra.nodes.size at childBound
  have childNonzero : output.window.pointer.grant.toNat≠0 := by
    intro zero
    exact childDifferent (GeneralBorrowNodeUpdate.index_injective _ _ zero)
  have indexBound:=GeneralBorrowNodeUpdate.lookup_valid output.window.allocation.extra.nodes index node found
  change index.toNat<output.window.allocation.extra.nodes.size at indexBound
  by_cases zero : index.toNat=0
  · have equal : index=allocationRoot:=GeneralBorrowNodeUpdate.index_injective _ _ zero
    subst index
    have same : node=original:=Option.some.inj (found.symm.trans originalAt)
    exact Or.inl ((congrArg TreeNode.tag same).trans originalValue.2.symm)
  · have equal : index=output.window.pointer.grant:=GeneralBorrowNodeUpdate.index_injective _ _ (by omega)
    subst index
    exact Or.inr (congrArg TreeNode.tag (Option.some.inj (found.symm.trans output.nodeAt)))

theorem absent {before : Before} {tracker : MachineHooks.BorrowState} {place : MPlaceTy Provenance}
    (output : Return before tracker place) (root sourceTag : BorTag)
    (small : output.window.allocation.extra.nodes.size≤2)
    (rootGrant : output.original.grant=allocationRoot)
    (rootValue : output.original.value.provenance=.concrete output.id root)
    (differentRoot : root≠sourceTag) (differentChild : sourceTag≠output.node.tag) :
    ∀index node,output.window.allocation.extra.nodes.get index=some node→node.tag≠sourceTag := by
  intro index node found equal
  rcases node_tag output root small rootGrant rootValue index node found with rootEq | childEq
  · exact differentRoot (rootEq.symm.trans equal)
  · exact differentChild (equal.symm.trans childEq)

/-- The actual operation feeds the common source/return interfaces and the
release consumer's derived all-Bool-node tag separation. No absence condition
is added to OrdinaryInput; entry supplies root≠q from original root freshness. -/
theorem protect_for_entry (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (retagCtx : ActualRetagContext.Context options remaining span)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker=some borrowFrame)
    (machine : Before) (tracker : MachineHooks.BorrowState) (start : Nat) (len : UInt64)
    (source : Source machine tracker start len) (copyReady : CopyReady source)
    (family : Family) (root : BorTag) (image : Allocation CtfeProvenance Unit)
    (base offset : UInt64) (place : MPlaceTy Provenance)
    (ready : CurrentCallLazyBoolEnsure.Ready options (Storage.withCurrent frames frame machine) tracker family root image base offset place)
    (noFunction : machine.memory.hasFunctionPointer family.allocation=false)
    (noVaList : machine.memory.hasVaListId family.allocation=false)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (ghost : machine.user.payload.ghost=false) (backend : machine.user.payload.payload.user.backend=.none)
    (differentRoot : root≠source.tag) :
    ∃post : RootState, ∃output : Return post.machine
        (registeredTracker (allocatedTracker tracker fresh) tracker.global.nextPointerTag) place,
      ∃current : Source post.machine (registeredTracker (allocatedTracker tracker fresh) tracker.global.nextPointerTag) start len,
      CopyReady current ∧current.tag≠output.node.tag ∧
      (∀index node,output.window.allocation.extra.nodes.get index=some node→node.tag≠current.tag) ∧
      TypedRetag.protectInPlaceFunctionArgument (config options remaining span).retag options.limits.retag place
        (Storage.withCurrent frames frame machine)=.ok () post ∧
      current.role.family=source.role.family ∧current.role.backing.allocation=source.role.backing.allocation ∧
      HEq current.role.backing.cells source.role.backing.cells ∧
      output.id=family.allocation ∧output.offset=offset.toNat ∧output.original=family.at allocationRoot ∧
      post.machine.borrowTracker=some (registeredTracker (allocatedTracker tracker fresh) tracker.global.nextPointerTag) ∧
      post.stack=(Storage.withCurrent frames (registeredFrame frame borrowFrame family.allocation tracker.global.nextPointerTag) machine).stack ∧
      post.machine={MemoryExtras.putAllocation (GlobalDataOnlyActualConfig.extras options) machine family.allocation ⟨none,#[]⟩ with
        memory:={machine.memory with live:=((machine.memory.live.filter (fun row=>row.1!=family.allocation)).push (family.allocation,⟨.machine .global,output.window.allocation⟩))},
        borrowTracker:=some (registeredTracker (allocatedTracker tracker fresh) tracker.global.nextPointerTag)} := by
  obtain ⟨post,output,current,copy,different,small,actual,familyEq,allocationEq,cellsEq,idEq,offsetEq,originalEq,tracked,stack,machineEq⟩:=
    CurrentCallLazyBoolCheckpoint.protect options remaining span retagCtx frames frame borrowFrame frameBorrow machine tracker start len source copyReady
      family root image base offset place ready noFunction noVaList fresh ghost backend
  have currentTag : current.tag=source.tag := by
    have concrete:=current.concrete
    rw [familyEq,source.concrete] at concrete
    exact (Provenance.concrete.inj concrete).2.symm
  have rootGrant : output.original.grant=allocationRoot:=by rw [originalEq];rfl
  have rootValue : output.original.value.provenance=.concrete output.id root := by
    rw [originalEq,idEq]
    change family.value.provenance=.concrete family.allocation root
    rw [ready.value];rfl
  have separated:=absent output root current.tag small rootGrant rootValue
    (by rw [currentTag];exact differentRoot) different
  exact ⟨post,output,current,copy,different,separated,actual,familyEq,allocationEq,cellsEq,idEq,offsetEq,originalEq,tracked,stack,machineEq⟩

end
end DuplicatePrefix.CurrentCallLazyBoolTagSeparation
