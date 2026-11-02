import duplicate_prefix.SliceLenRawAssign
import duplicate_prefix.SourceSteps
namespace DuplicatePrefix.SliceLenPrefix
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
open PtrMetadataExecution PtrMetadataHelper PtrMetadataComplete
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem two_statements
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debug : options.place.debugAssertions = false) (fuel : Nat) (validationFuel : options.limits.validation = fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (carrier : Pointer Provenance ⊕ UInt64) (len : UInt64) (carrierValid : SliceCarrier.Valid machine carrier len)
    (size : frame.locals.size = 3)
    (live1 : (frame.locals[1]'(by omega)).value = .live (.immediate
      (rawImmediate carrier (PreparedContracts.actualConfig options () remaining span).access.runtime.base len)))
    (cached1 : (frame.locals[1]'(by omega)).layout = some SharedReferenceMetadata.sharedLayout)
    (dead2 : (frame.locals[2]'(by omega)).value = .dead) (uncached2 : (frame.locals[2]'(by omega)).layout = none)
    (body : frame.body = SliceLenFacts.body.body) (identity : frame.bodyIdentity = SliceLenFacts.body.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.lenCall.callee) (located : frame.location = .mir ⟨0,0⟩)
    (noClocks : frame.extra.dataRace = none) (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (dynamicFuel : Nat) (dynamicEq : options.place.dynamicFuel = dynamicFuel+1)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false) :
    ∃ first second : CompilerFrameContext.ActualFrame,
      ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
        (Storage.withCurrent frames frame machine) = (Storage.withCurrent frames first machine,.ok true) ∧
      ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
        (Storage.withCurrent frames first machine) = (Storage.withCurrent frames second machine,.ok true) ∧
      second.body = frame.body ∧ second.bodyIdentity = frame.bodyIdentity ∧
      second.functionInstance = frame.functionInstance ∧ second.extra = frame.extra ∧
      second.returnPlace = frame.returnPlace ∧ second.returnContinuation = frame.returnContinuation ∧
      second.vaList = frame.vaList ∧ second.localsIdentity = frame.localsIdentity ∧
      second.locals.size = 3 ∧ second.location = .mir ⟨0,2⟩ ∧
      second.locals[0]? = frame.locals[0]? ∧ second.locals[1]? = frame.locals[1]? ∧
      second.locals[2]? = some ⟨.live (.immediate (rawImmediate carrier
        (PreparedContracts.actualConfig options () remaining span).access.runtime.base len)),some rawLayout⟩ := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let value := rawImmediate carrier (PreparedContracts.actualConfig options () remaining span).access.runtime.base len
  have valid1 : 1 < frame.locals.size := by rw [size];decide
  have valid2 : 2 < frame.locals.size := by rw [size];decide
  let block := SliceLenFacts.body.body.basicBlocks[0]'(by with_unfolding_all decide +kernel)
  let stmt0 := block.statements[0]'(by with_unfolding_all decide +kernel)
  let stmt1 := block.statements[1]'(by with_unfolding_all decide +kernel)
  have blockAt : SliceLenFacts.body.body.basicBlocks[0]? = some block := by simp [block]
  have stmtAt0 : block.statements[0]? = some stmt0 := by simp [stmt0]
  have stmtAt1 : block.statements[1]? = some stmt1 := by simp [stmt1]
  have kind0 : stmt0.kind = .StorageLive 2 := by with_unfolding_all rfl
  have kind1 : stmt1.kind = .Assign ⟨2,#[]⟩ (.RawPtr .Const ⟨1,#[.Deref]⟩) := by with_unfolding_all rfl
  have trivial : cfg.lifecycle.storage.veryTriviallySized 154 = .ok true := by
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).storage]
    decide +kernel
  let first := SourceSteps.liveFrame frame ⟨0,0⟩ 2 valid2
  have step1 := SourceSteps.storage_live_exact cfg limits () frames frame machine ⟨0,0⟩ block stmt0 2 154
    located (by rw [body];exact blockAt) stmtAt0 kind0 valid2 (by rw [body];with_unfolding_all rfl) trivial dead2 noClocks
  have firstSize : first.locals.size = 3 := by simp [first,SourceSteps.liveFrame,size]
  have firstValid1 : 1 < first.locals.size := by rw [firstSize];decide
  have firstValid2 : 2 < first.locals.size := by rw [firstSize];decide
  have copied := SliceLenRawAssign.actual_raw_assignment options limits remaining span debug fuel validationFuel frames first machine carrier len
    carrierValid firstValid1 firstValid2
    (by simpa [first,SourceSteps.liveFrame,Array.getElem_set,value] using live1)
    (by simpa [first,SourceSteps.liveFrame,Array.getElem_set] using cached1)
    (by simp [first,SourceSteps.liveFrame])
    (by simpa [first,SourceSteps.liveFrame] using uncached2)
    body identity callee noClocks ghost shallow dynamicFuel dynamicEq cmp metadata notConstructed
  let written := copied2 first firstValid2 value
  let second := {written with location := .mir ⟨0,2⟩}
  have step2 := SourceSteps.assign_exact cfg limits () frames first written machine machine ⟨0,1⟩ block stmt1
    ⟨2,#[]⟩ (.RawPtr .Const ⟨1,#[.Deref]⟩) rfl
    (by change frame.body.basicBlocks[0]? = _;rw [body];exact blockAt) stmtAt1 kind1 copied rfl
  refine ⟨first,second,step1,step2,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_,rfl,?_,?_,?_⟩
  · simp [second,written,copied2,cached2,writeFrame,LocalPlaces.cachePlaceLayout,firstSize]
  · simp [second,written,copied2,cached2,writeFrame,LocalPlaces.cachePlaceLayout,first,SourceSteps.liveFrame,Array.getElem?_set]
  · simp [second,written,copied2,cached2,writeFrame,LocalPlaces.cachePlaceLayout,first,SourceSteps.liveFrame,Array.getElem?_set]
  · simp [second,written,copied2,cached2,writeFrame,LocalPlaces.cachePlaceLayout,first,SourceSteps.liveFrame,value,Array.getElem?_set]
end
end DuplicatePrefix.SliceLenPrefix
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.SliceLenPrefix.two_statements) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved actual slice len prefix dependency {dependency}"
