import duplicate_prefix.CurrentCallSplitOriginTypedInput

/-! One real fixed-metadata whole-slice FnEntry retag of the constructed
split-origin current machine. Only the library's existing fixed decoder
contracts remain parameters; all runtime operations succeed as conclusions. -/
namespace DuplicatePrefix.CurrentCallSplitOriginTypedEntry
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.Input
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.DataStructures
open CanonicalConfigFacts ActualReferenceContext CurrentCallTypedFnEntry
open CurrentCallSplitOriginTypedInput
open CurrentCallSplitOriginTrace (tag ix)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option cbv.maxSteps 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail
noncomputable section

def limits : ExecutionMachine.Limits := ⟨64,64,64,64⟩
def options : EvalConfigurationCore.Options := Machine.exampleOptions limits 64 64 64 64 .Shallow ⟨false,false⟩
def remaining : Nat := 63
theorem fresh : tracker.global.nextPointerTag.value<18446744073709551615 := by decide +kernel

def output : GeneralBorrowForestFnEntry.Output := literal sourceAllocation.extra tracker.global {} sourceId fresh sourcePointer.provenance 0 2

theorem actual_operation : CandidateCurrentFnEntryRaw.operation sourceAllocation.extra tracker.global {} sourceId sourcePointer.provenance 0 2=.ok output :=
  literal_operation _ _ _ _ fresh _ _ _

theorem completed : output.access.status=.Completed ∧ output.child.outcome=.ok () := by cbv <;> decide +kernel

theorem actual_child :
    output.tag=tag 6 ∧ output.child.tree.indexOfTag (tag 6)=some (ix 4) ∧
    (output.child.tree.nodeAt (ix 4)).map TreeNode.parent=some (some (ix 3)) ∧
    output.global.protectedTags.get (tag 6)=some .StrongProtector ∧
    output.frame.protectedTags=#[(sourceId,tag 6)] ∧ output.global.nextPointerTag=tag 7 := by cbv <;> decide +kernel

def finalMachine := installed machine tracker fresh sourceId sourceEntry output.child.tree
def finalFrame := TypedBorrowSteps.registeredFrame root.frame {} sourceId tracker.global.nextPointerTag

/-- Finite structural cache-origin check over the unchanged fixed catalog. -/
def checkOrigin (world : RuntimeArrayTypes.World) (entry : RuntimeArrayTypes.Entry) : Bool :=
  match entry.origin with
  | .compiler id => entry.value.ty==id &&
      ((world.metadata.source.types.find? (fun node=>node.id==id)).map (fun node=>node.shapeKind==.array)).getD false
  | .runtimeConstructor => !(world.metadata.source.types.any (fun node=>node.id==entry.value.ty))

private theorem checkOrigin_sound (world : RuntimeArrayTypes.World) (entry : RuntimeArrayTypes.Entry)
    (good : checkOrigin world entry=true) : DuplicatePrefixTypeCacheOrigins.EntryOrigin world entry := by
  cases origin : entry.origin with
  | compiler id =>
    simp only [checkOrigin,origin,Bool.and_eq_true,beq_iff_eq] at good
    simp only [DuplicatePrefixTypeCacheOrigins.EntryOrigin,origin]
    refine ⟨good.1,?_⟩
    cases found : world.metadata.source.types.find? (fun node=>node.id==id) with
    | none =>
      simp only [found,Option.map_none,Option.getD_none,Bool.false_eq_true] at good
      exact False.elim good.2
    | some node =>
      refine ⟨node,rfl,?_⟩
      simpa only [found,Option.map_some,Option.getD_some,beq_iff_eq] using good.2
  | runtimeConstructor =>
    simp only [DuplicatePrefixTypeCacheOrigins.EntryOrigin,origin]
    cases checked : world.metadata.source.types.any (fun node=>node.id==entry.value.ty) with
    | false => rfl
    | true => simp only [checkOrigin,origin,checked,Bool.not_true,Bool.false_eq_true] at good

theorem catalog_cache_checked : PreparedReflection.actual.types.entries.all (checkOrigin PreparedReflection.actual.types)=true := by
  decide +kernel

theorem cache_origins : DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get state) := by
  change DuplicatePrefixTypeCacheOrigins.Origins PreparedReflection.actual.types
  intro entry member
  exact checkOrigin_sound _ entry (Array.all_eq_true'.mp catalog_cache_checked entry member)

/-- The adapted hooks are the actual fixed compiler/validity hooks supplied by
ActualReferenceContext. No resource interpretation or operation status is an input. -/
theorem typed_fnentry (span : PreparedContracts.FixedSpanQuery) (cmp : ProjectionMetadataFacts.NullComparator) :
    ∃ ctx : ActualReferenceContext.Context options remaining span,
    TypedRetag.retagPtrValue (adapted options remaining span ctx.pointers) options.limits.retag
      (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base sourcePointer 2 ActualReferenceMetadata.reference)
      ActualReferenceMetadata.reference.ty .FnEntry state =
      .ok (some (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (changedPointer sourcePointer sourceId (tag 6)) 2 ActualReferenceMetadata.reference))
        (Storage.withCurrent #[] finalFrame finalMachine) ∧
      finalMachine.borrowTracker=some ⟨output.global,tracker.retagMode⟩ ∧
      finalFrame.extra.borrowTracker=some output.frame ∧
      finalFrame.returnPlace=.memory place := by
  obtain ⟨ctx⟩ := ActualReferenceContext.exists_context options remaining span rfl rfl
  have metadata : (EvalProjectionMachine.arrays.get state).metadata=PreparedReflection.actual.runtime := rfl
  obtain ⟨retag,global,tagEq,frameEq,tracked,_,_,_,_,_⟩ := CurrentCallTypedSourceOperation.typed_of_operation options remaining span ctx
    machine tracker #[] root.frame {} rfl frame_borrow sourcePointer sourceId 0 2 sourceEntry source_present source_binding
    (by decide) (by decide) fresh rfl cmp 63 rfl metadata cache_origins output actual_operation completed.1 completed.2
  refine ⟨ctx,retag,tracked,frameEq,?_⟩
  change root.frame.returnPlace=.memory place
  exact (RawRootInvocation.control {before with borrowTracker:=some tracker} place (by rfl)).2.2.2

end
end DuplicatePrefix.CurrentCallSplitOriginTypedEntry
open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallSplitOriginTypedEntry" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved split-origin typed entry dependency {dependency}"
