import duplicate_prefix.CurrentCallOrdinaryInput
import duplicate_prefix.CurrentCallMaterializedRootBoolFrame

namespace DuplicatePrefix.CurrentCallOrdinarySameAllocationBool
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open CandidateCurrentJointCall CurrentCallOrdinaryInput CurrentCallSpatialCover
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- CURRENT query payloads are functional, including the actual fixed static
initializer lookup. No equality with an initial global catalog is used. -/
theorem current_unique {before : Before} {id : AllocId} {first second : Allocation CtfeProvenance Unit}
    (one : CurrentPayload before id first) (two : CurrentPayload before id second) : first=second := by
  cases one with
  | memory descriptor=>
    cases two with
    | memory other=>
      have equal:=congrArg GlobalAllocation.payload (Option.some.inj (descriptor.symm.trans other))
      simpa only [Option.some.injEq,GlobalAllocationPayload.memory.injEq] using equal
    | internalStatic definition other initializer=>
      have equal:=congrArg GlobalAllocation.payload (Option.some.inj (descriptor.symm.trans other))
      cases equal
  | internalStatic definition descriptor initializer=>
    cases two with
    | memory other=>
      have equal:=congrArg GlobalAllocation.payload (Option.some.inj (descriptor.symm.trans other))
      cases equal
    | internalStatic otherDefinition other otherInitializer=>
      have equal:=congrArg GlobalAllocation.payload (Option.some.inj (descriptor.symm.trans other))
      have definitionEq : definition=otherDefinition := by injection equal with values;injection values
      subst otherDefinition
      exact congrArg Prod.snd (Option.some.inj (initializer.symm.trans otherInitializer))

/-- Extract Bool-only physical facts for the SAME actual source conversion.
A latent return role fixes its CURRENT payload, cached root, and cached base;
these equal the source query's values by uniqueness. This does not require a
source family, initialized source bytes, or a source window. -/
theorem physical_data {options limits remaining span before argument len place}
    (input : OrdinaryInput options limits remaining span before argument len place)
    (latent : LatentRole before input.tracker input.returnFamily input.returnOffset 1 input.returnCapacity false)
    (source : Allocation CtfeProvenance Unit) (current : CurrentPayload before input.returnFamily.allocation source)
    (root : BorTag) (cachedRoot : input.tracker.global.rootTag? input.returnFamily.allocation=some root)
    (base : UInt64) (cachedBase : before.user.addresses.baseAddr.find? (fun row=>row.allocId==input.returnFamily.allocation)=some ⟨input.returnFamily.allocation,base⟩)
    (converted : Allocation Provenance Unit) (attributes : GlobalAllocationAttributes.Attributes source converted)
    (provenance : ProvenanceCopy.WellFormed converted.provenanceMap converted.len) :
    CurrentCallMaterializedRootBoolFrame.PhysicalData input.returnFamily root converted base input.returnOffset place := by
  obtain ⟨_,_,_,_,⟨retRoot,concrete,rootAt⟩,retSource,retCurrent,size,_,physical⟩:=latent
  have sameSource:=current_unique retCurrent current
  subst retSource
  have sameRoot : retRoot=root:=Option.some.inj (rootAt.symm.trans cachedRoot)
  subst retRoot
  obtain ⟨retBase,retCached,room,address,nonnull,_⟩:=input.returnRepresentation
  have sameBase : retBase=base:=congrArg (fun row : AllocAddresses.BaseAddressEntry=>row.address)
    (Option.some.inj (retCached.symm.trans cachedBase))
  subst retBase
  have extent : source.len=input.returnCapacity.toNat:=by rw [physical.1.1,size];rfl
  have bounds : input.returnOffset.toNat+1≤input.returnCapacity.toNat:=by
    simpa only [size,Size.ofBytes,UInt64.toNat_one] using physical.2.2.1
  have sumFits : base.toNat+input.returnOffset.toNat<2^64:=by omega
  have bits : input.returnFamily.value.offset.bytes=base+input.returnOffset:=by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt sumFits]
    exact address
  have value : input.returnFamily.value=Pointer.new (.concrete input.returnFamily.allocation root) (Size.ofBytes (base+input.returnOffset)) := by
    cases equal : input.returnFamily.value with
    | mk position prov=>
      simp only [equal] at concrete bits
      cases position
      simp only [Pointer.new,Size.ofBytes]
      simp_all
  exact {
    extent:=by rw [attributes.storage,attributes.size];exact physical.1.1
    mutable:=attributes.mutability.trans physical.2.1
    maskValid:=by rw [attributes.mask];exact physical.1.2.1
    maskLength:=by rw [attributes.mask,attributes.size];exact physical.1.2.2.1
    provenance:=provenance
    bounds:=by rw [attributes.size];simpa only [UInt64.toNat_one] using physical.2.2.1
    addressRoom:=by rw [attributes.storage,extent];exact room
    nonnull:=by rw [←bits];exact nonnull
    value:=value,physicalPointer:=input.returnEncoding,layout:=input.returnLayout,aligned:=input.returnAligned}

/-- The adopted source/return charges separate bytes even when both latent
roles select the same descriptor. No allocation-inequality shortcut is used. -/
theorem apart {options limits remaining span before argument len place}
    (input : OrdinaryInput options limits remaining span before argument len place)
    (sourceFamily : Family) (sourceOffset : UInt64)
    (same : sourceFamily.allocation=input.returnFamily.allocation)
    (charge : CurrentCallPointwiseSpatialCover.ExactCharge input.Fs input.sourceOwner .mut sourceFamily.allocation sourceOffset.toNat len.toNat) :
    ∀point : UInt64,input.returnOffset.toNat≤point.toNat→point.toNat<(input.returnOffset+1).toNat→
      point.toNat<sourceOffset.toNat∨(sourceOffset+len).toNat≤point.toNat := by
  intro point lower upper
  by_cases earlier : point.toNat<sourceOffset.toNat
  · exact Or.inl earlier
  · right
    apply Classical.byContradiction
    intro after
    have endLe : (sourceOffset+len).toNat≤sourceOffset.toNat+len.toNat := by
      rw [UInt64.toNat_add]
      exact Nat.mod_le _ _
    have boolEndLe : (input.returnOffset+1).toNat≤input.returnOffset.toNat+1 := by
      rw [UInt64.toNat_add,UInt64.toNat_one]
      exact Nat.mod_le _ _
    have sourceHit : CandidateStableCallOwnership.Window sourceFamily.allocation sourceOffset.toNat len.toNat
        (sourceFamily.allocation,point.toNat) := ⟨rfl,by omega,by omega⟩
    have returnHit : CandidateStableCallOwnership.Window input.returnFamily.allocation input.returnOffset.toNat 1
        (sourceFamily.allocation,point.toNat) := ⟨same,lower,by omega⟩
    exact CurrentCallPointwiseSpatialCover.exclusive_separate input.composable charge input.returnCharge _ sourceHit returnHit

end
end DuplicatePrefix.CurrentCallOrdinarySameAllocationBool

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "CurrentCallOrdinarySameAllocationBool.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved ordinary same-allocation Bool dependency {name}: {dependency}"
