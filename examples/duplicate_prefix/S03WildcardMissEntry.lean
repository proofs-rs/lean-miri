import duplicate_prefix.S03IntegerZeroState
import duplicate_prefix.S03WildcardMissArgumentScope

namespace DuplicatePrefix.S03WildcardMissEntry
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- The original integer/NoProv empty argument and count-zero initStackFrame,
from original physical/borrow/configuration data. The real first argument
consumes a tag without installing a protector; return protection uses only
its residual local margin. No future Input or successful helper is assumed. -/
theorem after_tail
    {options : EvalConfigurationCore.Options} {remaining : Nat} {span : PreparedContracts.FixedSpanQuery}
    (limits : ExecutionMachine.Limits) (before : Before)
    (model : DuplicatePrefixCallModel.Model options remaining span before)
    (place : MPlaceTy Provenance) (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (first : input.tracker.global.nextPointerTag.value < 18446744073709551615)
    (address count : UInt64) (nonzero : address ≠ 0)
    (addressMode : before.user.addresses.provenanceMode ≠ .strict)
    (miss : before.user.addresses.allocIdFromAddr address 0
      (GlobalAddressLiveErrorExclusion.lookup before.memory) = .ok none)
    (dynamicFuel validityFuel : Nat) (dynamicEq : options.place.dynamicFuel = dynamicFuel+1)
    (validityEq : options.limits.validation = validityFuel+1)
    (notConstructed : before.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false)
    (thread : Miri.Concurrency.ThreadRecord) (active : before.threads.activeThread? = some thread)
    (noCache : thread.topUserRelevantFrame = none) :
    let root := RawRootInvocation.root before place model.noDataRace
    let args := S03WildcardMissArguments.result root (config options remaining span).access.runtime.base address count
    let current := S03IntegerZeroState.argumentsMachine before input.tracker first
    ∀ done : RootState,
      RootEntryTail.tail (ExecutionMachine.callHooks (config options (remaining+1) span) limits) place
        (Storage.withCurrent #[] args.frame current) = .ok () done →
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (S03WildcardMissArguments.first (config options remaining span).access.runtime.base address),.Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () done := by
  dsimp only
  intro done tail
  let raw := RawRootInvocation.root before place model.noDataRace
  let rawMachine := RawRootInvocation.machine #[] before
  let args := S03WildcardMissArguments.result raw (config options remaining span).access.runtime.base address count
  let current := S03IntegerZeroState.argumentsMachine before input.tracker first
  let currentInput := S03IntegerZeroState.input input first
  have slot (i : Fin 25) : (raw.frame.locals[i.val]'(raw.valid i)) = ⟨.dead,none⟩ := by
    have rows := congrArg (fun rows : Array (LocalState Provenance LocalLayout) => rows[i.val]?)
      (RawRootInvocation.locals before place model.noDataRace)
    have row : raw.frame.locals[i.val]? = some (⟨.dead,none⟩ : LocalState Provenance LocalLayout) := by
      simpa only [Array.getElem?_replicate,i.isLt,↓reduceIte] using rows
    exact Option.some.inj ((Array.getElem?_eq_getElem (raw.valid i)).symm.trans row)
  have arguments := S03WildcardMissArgumentScope.arguments_in_scope options limits remaining span model.nullComparator
    model.preciseOff model.implicitOff model.debugOff dynamicFuel validityFuel dynamicEq validityEq #[] raw rawMachine (config options remaining span).access.runtime.base rfl address count nonzero
    (congrArg (fun row => row.value) (slot EmptyRootArguments.i1))
    (congrArg (fun row => row.layout) (slot EmptyRootArguments.i1))
    (congrArg (fun row => row.value) (slot EmptyRootArguments.i2))
    (congrArg (fun row => row.layout) (slot EmptyRootArguments.i2))
    model.ghostOff model.shallow input.tracker input.enabled first addressMode miss model.metadata notConstructed
  have push := CallEntryFacts.actual_call_hooks_push_raw options () (remaining+1) span limits model.debugOff
    (⟨⟨#[]⟩,before⟩ : RootState) (.memory place) thread active noCache
  have getFrame := CallEntryLocals.get_frame options limits (remaining+1) span #[] raw.frame rawMachine
  have setFrame := CallEntryLocals.set_frame options limits (remaining+1) span #[] raw.frame raw.frame rawMachine
  have control := RawRootInvocation.control before place model.noDataRace
  have preamble : raw.frame.location = .unwinding ⟨559⟩ := control.1
  have unchanged : {raw.frame with trackCallerArg := none} = raw.frame := by rw [←control.2.1]
  simp only [preamble] at unchanged
  rw [RootCallCore.actual_entry_eq]
  unfold RootCallCore.core
  simp only [bind,EStateM.bind]
  unfold CallEntryFacts.config at push
  rw [push,RawRootInvocation.raw_eq #[] before place model.noDataRace]
  simp only [EStateM.bind]
  rw [getFrame]
  simp only [EStateM.bind,preamble,pure,EStateM.pure]
  rw [unchanged,setFrame]
  simp only [EStateM.bind]
  simp only [S03WildcardMissArguments.second] at arguments
  simp only [EmptyRootArguments.second]
  rw [arguments]
  simp only [EStateM.bind]
  exact tail

end
end DuplicatePrefix.S03WildcardMissEntry
