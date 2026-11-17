import duplicate_prefix.GeneralBorrowPositiveConcreteWindowAcceptedCompleteInput
import duplicate_prefix.GeneralBorrowPositiveConcreteWindowAcceptedCopyEntry
import duplicate_prefix.GeneralBorrowPositiveConcreteWindowAcceptedCopyData
import duplicate_prefix.GeneralBorrowScopedInactiveWritableCopyPhysicalOutput
namespace DuplicatePrefix.GeneralBorrowPositiveConcreteWindowAcceptedCopyStage
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open ActualReferenceContext GeneralBorrowExposedScopedInactiveWritableAsMutCallReturn GeneralBorrowExposedScopedInactiveWritableAsMutToCopy
variable [area : GeneralBorrowExposedKnownRootState.Scope]
variable {profileMode : ProfileMode}
set_option maxRecDepth 1000000
set_option maxHeartbeats 12000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
structure Stage (s : GeneralBorrowPositiveConcreteWindowAcceptedCompleteInput.InitialFor profileMode) where
  updated : Allocation Provenance BorrowTree
  i : GeneralBorrowExposedScopedInactiveWritableLenCallInput.InputFor profileMode
  stage : GeneralBorrowExposedScopedInactiveWritableAcceptedAfterLen.InitialFor profileMode
  expression : GeneralBorrowExposedScopedInactiveWritableAcceptedExpression.InputFor profileMode
  call : GeneralBorrowExposedScopedInactiveWritableAsMutToCopy.InputFor profileMode
  installed : MachineHooks.State MiriMemoryKind Machine.RootUser
  origin : GeneralBorrowPositiveConcreteWindowAcceptedAfterLen.Origin s.toAccepted updated i stage
  firstOffset : i.first.offset=s.offset
  firstLen : i.first.len=s.len
  expressionOrigin : GeneralBorrowExposedScopedInactiveWritableAcceptedAfterLen.Origin stage expression
  callOrigin : GeneralBorrowExposedScopedInactiveWritableAcceptedToAsMut.Origin expression call.toInput
  countEq : call.count=s.count
  originalCall : Call.initStackFrame (ExecutionMachine.callHooks (config s.options (s.remaining+1) s.span) s.limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
          (Pointer.new (.concrete s.id s.parentTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm,ActualReferenceMetadata.reference⟩,
          .Copy (EmptyRootArguments.second s.count)] false (.memory s.place) (.stop true) ⟨⟨#[]⟩,s.before⟩=.ok () installed
  root : CompilerFrameContext.ActualFrame
  post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser
  trace : SuccessfulTrace.Trace (config s.options (s.remaining+1) s.span) s.limits installed (Storage.withCurrent #[] root post)
  shape : PositiveRootSuccessProfile.FrameShape call.caller root (scalar call) (destinationScalar call) call.count
  memory : post.memory=RetagEntry.updatedMemory call.machine.memory call.id call.entry (released call.toInput)
  tracked : post.borrowTracker=some {GeneralBorrowExposedScopedInactiveWritableAsMutCallInput.held call.toInput with global:=GeneralBorrowPositiveConcreteWindowAcceptedCopyData.ended call}
  runtime : GenericSharedLenAccepted.RuntimeFacts call.options call.remaining call.span call.machine post
  copy : CopyRootEntry.Input call.options call.limits call.remaining call.span #[] root post (scalar call) (destinationScalar call) call.count
  context : GeneralBorrowExposedKnownRootRangeData.Context (released call.toInput) (GeneralBorrowPositiveConcreteWindowAcceptedCopyData.anchor call) call.selected call.head call.tail
  owned : GeneralRangeMapOrigins.OwnedOn (fun location=>Nonempty
    (GeneralBorrowExposedScopedInactiveWritableAccessData.Data (released call.toInput) location
      (GeneralBorrowPositiveConcreteWindowAcceptedCopyData.ended call).protectedTags
      (GeneralBorrowPositiveConcreteWindowAcceptedCopyData.anchor call) call.selected call.head call.tail
      (fun position=>call.data.resources.component.support position ∨position=(GeneralBorrowPositiveConcreteWindowAcceptedCopyData.anchor call).toNat)))
      call.offset (call.offset+call.len) (released call.toInput).locations
  well : (released call.toInput).locations.WellFormed
  capacity : (released call.toInput).locations.size=call.entry.allocation.extra.locations.size

def data (s : GeneralBorrowPositiveConcreteWindowAcceptedCompleteInput.InitialFor profileMode) (p : Stage s) :=
  GeneralBorrowPositiveConcreteWindowAcceptedCopyData.form s.toAccepted p.updated p.i p.stage p.expression p.call p.origin p.expressionOrigin p.callOrigin p.countEq p.root p.post p.memory p.tracked p.runtime p.context p.owned p.well p.capacity p.copy

theorem forms (s : GeneralBorrowPositiveConcreteWindowAcceptedCompleteInput.InitialFor profileMode) : Nonempty (Stage s) := by
  obtain ⟨updated,i,stage,expression,call,installed,origin,firstOffset,firstLen,expressionOrigin,callOrigin,countEq,initialCall,root,post,trace,shape,memory,tracked,runtime,⟨copy,_⟩,context,owned,well,capacity⟩ :=
    GeneralBorrowPositiveConcreteWindowAcceptedCopyEntry.invoke s.toAccepted
  exact ⟨⟨updated,i,stage,expression,call,installed,origin,firstOffset,firstLen,expressionOrigin,callOrigin,countEq,initialCall,root,post,trace,shape,memory,tracked,runtime,copy,context,owned,well,capacity⟩⟩

theorem run (s : GeneralBorrowPositiveConcreteWindowAcceptedCompleteInput.InitialFor profileMode) (p : Stage s) :
    Nonempty (GeneralBorrowScopedInactiveWritableCopyPhysicalOutput.Output p.call.options p.call.limits p.call.remaining p.call.span #[] p.root p.post (scalar p.call) (destinationScalar p.call) p.call.count p.copy (data s p)) := by
  exact GeneralBorrowScopedInactiveWritableCopyPhysicalOutput.run p.call.options p.call.limits p.call.remaining p.call.span #[] p.root p.post (scalar p.call) (destinationScalar p.call) p.call.count p.copy (data s p)
    (GeneralBorrowPositiveConcreteWindowAcceptedCopyData.statement_fuel s.toAccepted p.updated p.i p.stage p.expression p.call p.origin p.expressionOrigin p.callOrigin p.root p.post p.copy s.statementFuel)
    (GeneralBorrowPositiveConcreteWindowAcceptedCopyData.mode p.call p.root p.post p.tracked p.copy)
end
end DuplicatePrefix.GeneralBorrowPositiveConcreteWindowAcceptedCopyStage
