import duplicate_prefix.CurrentCallLazyBoolCheckpoint

/-! The fixed Bool protection policy has no recursive interior traversal.
Its actual retag and protection operations are independent of the retag budget;
this connects the selected proof to arbitrary public execution limits. -/
namespace DuplicatePrefix.CurrentCallBoolRetagBudget
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext TypedBorrowSteps
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

theorem reborrow (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : ActualRetagContext.Context options remaining span)
    (place : MPlaceTy Provenance) (layout : place.layout=RootCompilerFacts.boolLayout)
    (first second : Nat) (tag : BorTag) :
    TypedRetag.reborrow (config options remaining span).retag first place (Size.ofBytes 1) MachineHooks.protectionPolicy tag=
      TypedRetag.reborrow (config options remaining span).retag second place (Size.ofBytes 1) MachineHooks.protectionPolicy tag := by
  let h:=(config options remaining span).retag
  have frozen : h.typeIsFreeze place.layout.ty=pure true := by
    rw [layout];exact ActualRetagContext.bool_freeze options remaining span ctx
  have left:=TypedRetagPolicyFields.inside_for_policy h first place (Size.ofBytes 1)
    MachineHooks.protectionPolicy ChildBorrow.fnEntryLocation rfl ctx.source.precise frozen
  have right:=TypedRetagPolicyFields.inside_for_policy h second place (Size.ofBytes 1)
    MachineHooks.protectionPolicy ChildBorrow.fnEntryLocation rfl ctx.source.precise frozen
  change TypedRetag.reborrow h first place (Size.ofBytes 1) MachineHooks.protectionPolicy tag=
    TypedRetag.reborrow h second place (Size.ofBytes 1) MachineHooks.protectionPolicy tag
  unfold TypedRetag.reborrow
  rw [left,right]

theorem retag (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : ActualRetagContext.Context options remaining span)
    (place : MPlaceTy Provenance) (layout : place.layout=RootCompilerFacts.boolLayout) (first second : Nat) :
    TypedRetag.retagPlace (config options remaining span).retag first place MachineHooks.protectionPolicy=
      TypedRetag.retagPlace (config options remaining span).retag second place MachineHooks.protectionPolicy := by
  unfold TypedRetag.retagPlace
  rw [ActualRetagContext.bool_size options remaining span ctx place layout]
  funext state
  simp only [bind,EStateM.bind,pure,EStateM.pure,Option.map_some,Option.getD_some]
  simp only [reborrow options remaining span ctx place layout first second]

theorem protect (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : ActualRetagContext.Context options remaining span)
    (place : MPlaceTy Provenance) (layout : place.layout=RootCompilerFacts.boolLayout) (first second : Nat) :
    TypedRetag.protectInPlaceFunctionArgument (config options remaining span).retag first place=
      TypedRetag.protectInPlaceFunctionArgument (config options remaining span).retag second place := by
  unfold TypedRetag.protectInPlaceFunctionArgument TypedRetag.protectPlace
  rw [retag options remaining span ctx place layout first second]

end
end DuplicatePrefix.CurrentCallBoolRetagBudget
