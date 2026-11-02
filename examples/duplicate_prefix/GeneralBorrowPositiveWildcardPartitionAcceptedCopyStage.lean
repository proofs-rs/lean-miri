import duplicate_prefix.GeneralBorrowPositiveWildcardPartitionAcceptedCompleteInput
import duplicate_prefix.GeneralBorrowPositiveWildcardPartitionAcceptedCopyEntry
import duplicate_prefix.GeneralBorrowPositiveWildcardPartitionAcceptedCopyData
import duplicate_prefix.GeneralBorrowScopedCopyPhysicalOutput
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardPartitionAcceptedCopyStage
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open ActualReferenceContext GeneralBorrowExposedScopedAsMutCallReturn GeneralBorrowExposedScopedAsMutToCopy
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 1000000
set_option maxHeartbeats 12000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
structure Stage (s : GeneralBorrowPositiveWildcardPartitionAcceptedCompleteInput.Initial) where
  updated : Allocation Provenance BorrowTree
  i : GeneralBorrowExposedScopedLenCallInput.Input
  stage : GeneralBorrowExposedScopedAcceptedAfterLen.Initial
  expression : GeneralBorrowExposedScopedAcceptedExpression.Input
  call : GeneralBorrowExposedScopedAsMutToCopy.Input
  installed : MachineHooks.State MiriMemoryKind Machine.RootUser
  origin : GeneralBorrowPositiveWildcardPartitionAcceptedAfterLen.Origin s.toAccepted updated i stage
  expressionOrigin : GeneralBorrowExposedScopedAcceptedAfterLen.Origin stage expression
  callOrigin : GeneralBorrowExposedScopedAcceptedToAsMut.Origin expression call.toInput
  countEq : call.count=s.count
  originalCall : Call.initStackFrame (ExecutionMachine.callHooks (config s.options (s.remaining+1) s.span) s.limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
          (Pointer.new .wildcard (Size.ofBytes s.base)) s.len ActualReferenceMetadata.reference).imm,ActualReferenceMetadata.reference⟩,
          .Copy (EmptyRootArguments.second s.count)] false (.memory s.place) (.stop true) ⟨⟨#[]⟩,s.before⟩=.ok () installed
  root : CompilerFrameContext.ActualFrame
  post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser
  trace : SuccessfulTrace.Trace (config s.options (s.remaining+1) s.span) s.limits installed (Storage.withCurrent #[] root post)
  shape : PositiveRootSuccessProfile.FrameShape call.caller root (scalar call) (destinationScalar call) call.count
  memory : post.memory=RetagEntry.updatedMemory call.machine.memory call.id call.entry (released call.toInput)
  tracked : post.borrowTracker=some {GeneralBorrowExposedScopedAsMutCallInput.held call.toInput with global:=GeneralBorrowPositiveWildcardPartitionAcceptedCopyData.ended call}
  runtime : GenericSharedLenAccepted.RuntimeFacts call.options call.remaining call.span call.machine post
  copy : CopyRootEntry.Input call.options call.limits call.remaining call.span #[] root post (scalar call) (destinationScalar call) call.count
  context : GeneralBorrowExposedKnownRootRangeData.Context (released call.toInput) (GeneralBorrowPositiveWildcardPartitionAcceptedCopyData.anchor call) call.selected call.head call.tail
  owned : GeneralRangeMapOrigins.OwnedOn (fun location=>
    Nonempty (GeneralBorrowExposedScopedUniqueReadData.Data (released call.toInput) location (GeneralBorrowPositiveWildcardPartitionAcceptedCopyData.ended call).protectedTags (GeneralBorrowPositiveWildcardPartitionAcceptedCopyData.anchor call) call.selected call.head call.tail (fun position=>call.data.resources.component.support position ∨position=(GeneralBorrowPositiveWildcardPartitionAcceptedCopyData.anchor call).toNat) (fun _=>true)) ∧
    Nonempty (GeneralBorrowExposedKnownRootRangeData.Data (released call.toInput) location (GeneralBorrowPositiveWildcardPartitionAcceptedCopyData.ended call).protectedTags (GeneralBorrowPositiveWildcardPartitionAcceptedCopyData.anchor call) call.selected call.head call.tail .Write)) call.offset (call.offset+call.len) (released call.toInput).locations
  well : (released call.toInput).locations.WellFormed
  capacity : (released call.toInput).locations.size=call.entry.allocation.extra.locations.size

def data (s : GeneralBorrowPositiveWildcardPartitionAcceptedCompleteInput.Initial) (p : Stage s) :=
  GeneralBorrowPositiveWildcardPartitionAcceptedCopyData.form s.toAccepted p.updated p.i p.stage p.expression p.call p.origin p.expressionOrigin p.callOrigin p.countEq p.root p.post p.memory p.tracked p.runtime p.context p.owned p.well p.capacity p.copy

theorem forms (s : GeneralBorrowPositiveWildcardPartitionAcceptedCompleteInput.Initial) : Nonempty (Stage s) := by
  obtain ⟨updated,i,stage,expression,call,installed,origin,expressionOrigin,callOrigin,countEq,initialCall,root,post,trace,shape,memory,tracked,runtime,⟨copy,_⟩,context,owned,well,capacity⟩ :=
    GeneralBorrowPositiveWildcardPartitionAcceptedCopyEntry.invoke s.toAccepted
  exact ⟨⟨updated,i,stage,expression,call,installed,origin,expressionOrigin,callOrigin,countEq,initialCall,root,post,trace,shape,memory,tracked,runtime,copy,context,owned,well,capacity⟩⟩

theorem run (s : GeneralBorrowPositiveWildcardPartitionAcceptedCompleteInput.Initial) (p : Stage s) :
    Nonempty (GeneralBorrowScopedCopyPhysicalOutput.Output p.call.options p.call.limits p.call.remaining p.call.span #[] p.root p.post (scalar p.call) (destinationScalar p.call) p.call.count p.copy (data s p)) := by
  exact GeneralBorrowScopedCopyPhysicalOutput.run p.call.options p.call.limits p.call.remaining p.call.span #[] p.root p.post (scalar p.call) (destinationScalar p.call) p.call.count p.copy (data s p)
    (GeneralBorrowPositiveWildcardPartitionAcceptedCopyData.statement_fuel s.toAccepted p.updated p.i p.stage p.expression p.call p.origin p.expressionOrigin p.callOrigin p.root p.post p.copy s.statementFuel)
    (GeneralBorrowPositiveWildcardPartitionAcceptedCopyData.mode p.call p.root p.post p.tracked p.copy)
end
end DuplicatePrefix.GeneralBorrowPositiveWildcardPartitionAcceptedCopyStage
