import duplicate_prefix.CurrentCallPointwiseSpatialCover
import duplicate_prefix.CurrentCallSplitOriginSpatialPair

/-! The existing actual split-origin packet admits the pointwise construction.
This is a concrete candidate-current ownership witness, not Ordinary adoption.
No actual operation status or new generic runtime certificate is assumed. -/
namespace DuplicatePrefix.CurrentCallSplitOriginPointwiseAdmission
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources CandidateFreezeContentResources
open CurrentCallResourceNormalization CurrentCallSpatialCover CurrentCallPointwiseSpatialCover
open CurrentCallSplitOriginTypedInput
open CurrentCallSplitOriginSpatialPair (source ret sourceFragment returnFragment)
open CurrentCallSplitOriginTrace (ix)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

theorem source_bound : 0+2≤sourceEntry.allocation.len := by
  change 0+2≤sourceAllocation.len
  rw [source_physical.storage.byteLength]
  exact source_physical.contained

theorem return_bound : 0+1≤destinationEntry.allocation.len := by
  change 0+1≤destinationAllocation.len
  rw [destination_physical.storage.byteLength]
  exact destination_physical.contained

/-- Real interpreter rows cover both requested source bytes. The fact is
proved from the already checked endpoints, not from resource vacuity. -/
theorem source_rows : Rows sourceAllocation sourceId 0 2 := by
  intro byte hit
  have alternatives : byte.2=0 ∨ byte.2=1 := by have h:=hit.2;omega
  rcases alternatives with zero | one
  · refine ⟨CurrentCallSplitOriginTrace.leftSegment,CurrentCallSplitOriginTrace.segment_endpoints.1,?_,?_⟩
    · rw [CurrentCallSplitOriginTrace.segment_endpoints.2.2.1,zero]
      exact Nat.le_refl _
    · rw [CurrentCallSplitOriginTrace.segment_endpoints.2.2.2.1,zero]
      decide
  · refine ⟨CurrentCallSplitOriginTrace.rightSegment,CurrentCallSplitOriginTrace.segment_endpoints.2.1,?_,?_⟩
    · rw [CurrentCallSplitOriginTrace.segment_endpoints.2.2.2.2.1,one]
      exact Nat.le_refl _
    · rw [CurrentCallSplitOriginTrace.segment_endpoints.2.2.2.2.2.1,one]
      decide

theorem return_rows : Rows destinationAllocation destinationId 0 1 := by
  intro byte hit
  have zero : byte.2=0 := by have h:=hit.2;omega
  refine ⟨CurrentCallSplitOriginSpatialPair.destinationSegment,?_,?_,?_⟩
  · have entries : destinationAllocation.extra.locations.entries=#[CurrentCallSplitOriginSpatialPair.destinationSegment] := rfl
    rw [entries]
    simp
  · have start : CurrentCallSplitOriginSpatialPair.destinationSegment.range.start=0 := rfl
    rw [start,zero]
    exact Nat.le_refl _
  · have stop : CurrentCallSplitOriginSpatialPair.destinationSegment.range.stop=1 := rfl
    rw [stop,zero]
    decide

theorem source_charge : ExactCharge sourceFragment source.family.slot .mut source.family.allocation 0 2 := by
  intro byte
  constructor
  · intro found
    exact ((CurrentCallSplitOriginSpatialPair.source_role_footprint byte ⟨.mut,.active⟩).mp found).1
  · intro hit
    exact (CurrentCallSplitOriginSpatialPair.source_role_footprint byte ⟨.mut,.active⟩).mpr ⟨hit,rfl⟩

theorem return_charge : ExactCharge returnFragment ret.family.slot .ret ret.family.allocation 0 1 := by
  intro byte
  constructor
  · intro found
    exact ((CurrentCallSplitOriginSpatialPair.return_role_footprint byte ⟨.ret,.active⟩).mp found).1
  · intro hit
    exact (CurrentCallSplitOriginSpatialPair.return_role_footprint byte ⟨.ret,.active⟩).mpr ⟨hit,rfl⟩

/-- The same fixed families have raw-chain presentations at each requested
byte, by extraction from their actual existing cell interpretations. -/
theorem raw_support :
    Chained tracker source.family sourceAllocation .mut 0 2 ∧
    Chained tracker ret.family destinationAllocation .ret 0 1 :=
  ⟨chains_of_pointwise (pointwise_of_role source),chains_of_pointwise (pointwise_of_role ret)⟩

/-- The NEW finite assembly admits both roles of the SAME actual packet, with
fixed family values/slots and actual physical allocations. The old absence of
one whole-source origin persists; no caller-uniformity premise was added. -/
theorem admitted :
    ∃ ctx : Context machine,
      ∃ sourceRole : RoleCover machine tracker ctx .mut 0 2,
      ∃ returnRole : RoleCover machine tracker ctx .ret 0 1,
        sourceRole.family=source.family ∧ returnRole.family=ret.family ∧
        sourceRole.family.value=sourcePointer ∧ returnRole.family.value=destinationPointer ∧
        sourceRole.backing.allocation=sourceAllocation ∧ returnRole.backing.allocation=destinationAllocation ∧
        Rows sourceRole.backing.allocation sourceId 0 2 ∧ Rows returnRole.backing.allocation destinationId 0 1 ∧
        (¬∃ C,ParentInterpretation sourceAllocation.extra C ∧
          SpatialDelegation machine tracker sourceId sourceAllocation C (ix 3) ∧
          ∀ byte,byte<2 → Embeds sourceAllocation tracker.global.protectedTags C (ix 3) byte .exclusive) := by
  obtain ⟨ctx,S,R,familyS,familyR,allocationS,allocationR,rowsS,rowsR⟩:=assemble source.family ret.family 0 2 0 (by decide)
    sourceEntry destinationEntry source_present destination_present source_bound return_bound source_rows return_rows
    sourceFragment returnFragment source.family.slot ret.family.slot CurrentCallSplitOriginSpatialPair.composable
    source_charge return_charge (pointwise_of_role source) (pointwise_of_role ret)
  exact ⟨ctx,S,R,familyS,familyR,by rw [familyS];rfl,by rw [familyR];rfl,allocationS,allocationR,rowsS,rowsR,
    CurrentCallSplitOriginTypedSeparation.no_uniform_input⟩

end
end DuplicatePrefix.CurrentCallSplitOriginPointwiseAdmission
