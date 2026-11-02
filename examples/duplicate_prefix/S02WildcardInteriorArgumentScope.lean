import duplicate_prefix.S02WildcardArgumentGeometry
import duplicate_prefix.GeneralBorrowRawWildcardWindowFunctionScope
import duplicate_prefix.RawRootInvocation
import duplicate_prefix.S05ConsistentCallSpecification

namespace DuplicatePrefix.S02WildcardInteriorArgumentScope
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open CanonicalConfigFacts ActualReferenceContext RootFrameData DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- Interior wildcard case of the real typed FnEntry argument body. The
inverse-map Cut is the case witness supplied by the reference's existing
binding geometry; no tree shape, free-pool profile or operation outcome is
assumed. This is an intermediate case lemma, not final call safety. -/
theorem argument_body
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (reference : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new .wildcard (Size.ofBytes address)) len)
    (position : Nat)
    (cut : WildcardInteriorHitAddress.Cut before.user.addresses.intToPtrMap address (position+1))
    (row : before.user.addresses.intToPtrMap[position]? = some ⟨reference.base,reference.id⟩)
    (inside : address-reference.base < reference.entry.allocation.byteSize.bytes) :
    ∃ (output : GeneralBorrowForestFnEntry.Output)
      (fresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615),
      let root := RawRootInvocation.root before place input.contract.model.noDataRace
      let machine := RawRootInvocation.machine #[] before
      let current := GeneralBorrowRawWildcardWindowFunctionScope.resultMachine machine reference.tracker fresh
        reference.id reference.entry output.child.tree
      let cfg := PreparedContracts.actualConfig options () (remaining+1) span
      let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
          (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
      GeneralBorrowRawWildcardFnEntryRuntime.operation reference.entry.allocation.extra
        reference.tracker.global ({} : FrameState) reference.id reference.offset len = .ok output ∧
      (ExecutionMachine.callHooks cfg limits).withRetagMode () .FnEntry
        (RootCallCore.argumentBody (ExecutionMachine.callHooks cfg limits)
          (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
            (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len)
          (EmptyRootArguments.second count))
        (Storage.withCurrent #[] root.frame machine) =
        .ok (2,2) (Storage.withCurrent #[]
          (RootArgumentsTwo.result
            (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
              reference.id reference.tracker.global.nextPointerTag) count).frame current) := by
  have offsetEq := (S02WildcardArgumentGeometry.cases address len reference).1
  have binding := reference.binding
  simp only [DuplicatePrefixReferenceInput.Binding,Pointer.new] at binding
  obtain ⟨source,mode,exposed,_⟩ := binding
  obtain ⟨_,_,_,capability,runtime,distinct,short,nodeRoom,tagRoom⟩ :=
    S05WildcardEntryBridge.from_positive address len reference input.contract.runtime.toState
      input.contract.resources
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let machine := RawRootInvocation.machine #[] before
  obtain ⟨memory,borrow,race,addresses,ghost,shallow,types,_,_⟩ :=
    RawRootInvocation.preservation #[] before
  have dead (i : Fin 25) : (root.frame.locals[i.val]'(root.valid i)) = ⟨.dead,none⟩ := by
    have rows := congrArg (fun rows : Array (LocalState Provenance LocalLayout) => rows[i.val]?)
      (RawRootInvocation.locals before place input.contract.model.noDataRace)
    have row : root.frame.locals[i.val]? = some (⟨.dead,none⟩ : LocalState Provenance LocalLayout) := by
      simpa only [Array.getElem?_replicate,i.isLt,↓reduceIte] using rows
    exact Option.some.inj ((Array.getElem?_eq_getElem (root.valid i)).symm.trans row)
  have frameBorrow := RawRootInvocation.frame_borrow before place input.contract.model.noDataRace
    reference.tracker reference.enabled
  have positive : (0 : UInt64) < len := UInt64.lt_iff_toNat_lt.mpr reference.storage.positive
  have bounds : (address-reference.base).toNat + len.toNat ≤
      reference.entry.allocation.byteSize.bytes.toNat := by
    rw [←offsetEq]
    simpa only [reference.size,Size.ofBytes] using reference.storage.bounds
  have positionValid : position < before.user.addresses.intToPtrMap.size := by
    have := cut.1
    omega
  have initialWork : 64 ≤ work before len := by unfold work;omega
  have dynamicEq : options.place.dynamicFuel = (options.place.dynamicFuel-1)+1 := by
    have room := input.contract.resources.dynamicFuel
    omega
  have validityEq : options.limits.validation = (options.limits.validation-1)+1 := by
    have room := input.contract.resources.configuredFuel.2.2.2
    omega
  let ctx := Classical.choice (DuplicatePrefixCallModel.contexts options remaining span before input.contract.model).1
  obtain ⟨output,run,passed,_,_,_,_⟩ := GeneralBorrowRawWildcardWindowFunctionScope.scope
    options limits remaining span ctx input.contract.model.debugOff input.contract.model.nullComparator
    (options.place.dynamicFuel-1) (options.limits.validation-1) dynamicEq validityEq
    reference.id reference.tracker address reference.base len count reference.nonnull
    reference.entry positive reference.storage.signedSize bounds #[] root machine
    (congrArg (fun row => row.value) (dead EmptyRootArguments.i1))
    (congrArg (fun row => row.layout) (dead EmptyRootArguments.i1))
    (congrArg (fun row => row.value) (dead EmptyRootArguments.i2))
    (congrArg (fun row => row.layout) (dead EmptyRootArguments.i2))
    (ghost.trans input.contract.model.ghostOff) (shallow.trans input.contract.model.shallow)
    (by rw [addresses];exact reference.cachedBase)
    (by rw [memory];exact reference.live)
    {} frameBorrow (borrow.trans reference.enabled) tagRoom
    position (by rw [addresses];exact cut) (by simpa only [reference.size] using inside)
    (by rw [addresses];exact row) (by rw [addresses];exact mode)
    (by rw [addresses];exact exposed) runtime (by simpa only [offsetEq] using capability)
    distinct short nodeRoom (race.trans input.contract.model.noDataRace)
    (by rw [types];exact input.contract.model.metadata)
    (by rw [types];exact input.slice_not_constructed)
  refine ⟨output,tagRoom,?_,?_⟩
  · simpa only [offsetEq] using run
  · simpa only [DuplicatePrefixSliceArgument.first,DuplicatePrefixSliceArgument.rawValue,
      root,machine] using passed

end
end DuplicatePrefix.S02WildcardInteriorArgumentScope

open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms ``DuplicatePrefix.S02WildcardInteriorArgumentScope.argument_body) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
