import duplicate_prefix.CurrentCallFamilySatisfaction
import duplicate_prefix.DuplicatePrefixCallSpecification

/-! Current-family satisfaction consumed by the finite spatial frontend.
Physical normalization, allocation licensing, realization and numeric execution
budgets are separate from ownership. These theorems form current RoleCovers;
they assert no MIR operation, future permission, or Rust-history equivalence. -/
namespace DuplicatePrefix.CurrentCallFamilySpatialAdmission
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter Miri.Input
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources CandidateFreezeContentResources
open CurrentCallResourceNormalization CurrentCallSpatialCover CurrentCallFamilySatisfaction
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

/-- Empty source metadata is tied to the ACTUAL image/state and raw optional
pointer encoding. It imposes NO source allocation, family, grant or chain.
Positive integer encodings may be represented by a wildcard family; their real
normalization/materialization execution is a separate frontend obligation. -/
def SourceSatisfies (options : EvalConfigurationCore.Options) (before : Before) (tracker : MachineHooks.BorrowState)
    {actual : Array (Pointer (Option Provenance))} (assignment : Assignment actual) (occurrence : Nat)
    (argument : DuplicatePrefixSliceArgument.Argument) (len : UInt64) (offset : Nat) : Prop :=
  if len=0 then
    actual[occurrence]?=some (DuplicatePrefixSliceArgument.placePointer argument) ∧
    DuplicatePrefixEmptyReferenceInput.Candidate (DuplicatePrefixCallSpecification.imageContext options before tracker)
      before.memory before.user.addresses (DuplicatePrefixSliceArgument.placePointer argument)
  else ∃ family allocation,
    assignment.Binds occurrence family ∧ actual[occurrence]?=some (DuplicatePrefixSliceArgument.placePointer argument) ∧
    Satisfies tracker family allocation (Window family.allocation offset len.toNat)

def ReturnSatisfies (tracker : MachineHooks.BorrowState)
    {actual : Array (Pointer (Option Provenance))} (assignment : Assignment actual) (occurrence : Nat)
    (place : MPlaceTy Provenance) (family : Family) (allocation : Allocation Provenance BorrowTree) (offset : Nat) : Prop :=
  assignment.Binds occurrence family ∧ actual[occurrence]?=some place.mplace.ptr ∧
    place.layout=RootCompilerFacts.boolLayout ∧ Satisfies tracker family allocation (Window family.allocation offset 1)

theorem empty_source_iff {options before tracker actual assignment occurrence argument offset} :
    SourceSatisfies options before tracker (actual:=actual) assignment occurrence argument 0 offset ↔
      actual[occurrence]?=some (DuplicatePrefixSliceArgument.placePointer argument) ∧
      DuplicatePrefixEmptyReferenceInput.Candidate (DuplicatePrefixCallSpecification.imageContext options before tracker)
        before.memory before.user.addresses (DuplicatePrefixSliceArgument.placePointer argument) := by
  simp only [SourceSatisfies,ite_true]

theorem integer_empty_iff {options before tracker actual assignment occurrence offset} (address : UInt64) :
    SourceSatisfies options before tracker (actual:=actual) assignment occurrence (.integer address) 0 offset ↔
      actual[occurrence]?=some (Pointer.withoutProvenance address) ∧ address≠0 := by
  rw [empty_source_iff]
  exact and_congr Iff.rfl (DuplicatePrefixEmptyReferenceInput.no_provenance_iff _ _ _ address)

theorem positive_source {options before tracker actual assignment occurrence argument len offset}
    (owned : SourceSatisfies options before tracker (actual:=actual) assignment occurrence argument len offset)
    (nonzero : len≠0) :
    ∃ family allocation,assignment.Binds occurrence family ∧
      Represents (DuplicatePrefixSliceArgument.placePointer argument) family.value ∧
      Satisfies tracker family allocation (Window family.allocation offset len.toNat) := by
  simp only [SourceSatisfies,ite_eq_right nonzero] at owned
  obtain ⟨family,allocation,bound,stored,rights⟩:=owned
  obtain ⟨raw,present,represented⟩:=assignment.actual_value bound
  have equal : raw=(DuplicatePrefixSliceArgument.placePointer argument):=Option.some.inj (present.symm.trans stored)
  subst raw
  exact ⟨family,allocation,bound,represented,rights⟩

private theorem bound_of_binding {before : Before} {value : Pointer Provenance} {id : AllocId} {offset length : Nat}
    {entry : LocalAllocation Provenance BorrowTree MiriMemoryKind}
    (live : before.memory.live.find? (fun row=>row.1==id)=some (id,entry))
    (binding : CandidateCallBindings.WindowBinding before value id offset length) : offset+length≤entry.allocation.len := by
  obtain ⟨actual,base,found,cache,extent,headroom,bound,address,nonnull,provenance⟩:=binding
  have same : actual=entry:=(Prod.mk.inj (Option.some.inj (found.symm.trans live))).2
  subst actual
  exact bound

/-- Two disjoint exclusive ABI roles from ONE coherent occurrence assignment
consume the SAME fixed semantic families. Source encoding is not syntactically
restricted to `.pointer`; actual raw bits must represent that family, while
real normalization/materialization remains a separate execution obligation. -/
theorem positive_live {before tracker actual}
    (assignment : Assignment actual) (sourceOccurrence returnOccurrence : Nat)
    (argument : DuplicatePrefixSliceArgument.Argument) (len : UInt64) (place : MPlaceTy Provenance)
    (positive : 0<len.toNat) (S R : Family) (sourceOffset returnOffset : Nat)
    (sourceAssigned : assignment.Binds sourceOccurrence S)
    (sourceActual : actual[sourceOccurrence]?=some (DuplicatePrefixSliceArgument.placePointer argument))
    (returnAssigned : assignment.Binds returnOccurrence R)
    (returnActual : actual[returnOccurrence]?=some place.mplace.ptr)
    (_returnLayout : place.layout=RootCompilerFacts.boolLayout)
    (sourceEntry returnEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (sourceLive : before.memory.live.find? (fun row=>row.1==S.allocation)=some (S.allocation,sourceEntry))
    (returnLive : before.memory.live.find? (fun row=>row.1==R.allocation)=some (R.allocation,returnEntry))
    (sourcePhysical : CandidateCallBindings.WindowBinding before S.value S.allocation sourceOffset len.toNat)
    (returnPhysical : CandidateCallBindings.WindowBinding before R.value R.allocation returnOffset 1)
    (Fs Fr : Fragment) (sourceOwner returnOwner : Nat)
    (composable : Composable Fs Fr)
    (sourceCharge : CurrentCallPointwiseSpatialCover.ExactCharge Fs sourceOwner .mut S.allocation sourceOffset len.toNat)
    (returnCharge : CurrentCallPointwiseSpatialCover.ExactCharge Fr returnOwner .ret R.allocation returnOffset 1)
    (sourceCap : AllocationCapability before tracker S.allocation sourceEntry.allocation)
    (returnCap : AllocationCapability before tracker R.allocation returnEntry.allocation)
    (sourceRuntime : DuplicatePrefixBorrowContract.RuntimeFacts sourceEntry.allocation.extra tracker.global)
    (returnRuntime : DuplicatePrefixBorrowContract.RuntimeFacts returnEntry.allocation.extra tracker.global)
    (sourceOrder : GeneralBorrowWildcardParentTagOrder.ParentTagOrder sourceEntry.allocation.extra)
    (returnOrder : GeneralBorrowWildcardParentTagOrder.ParentTagOrder returnEntry.allocation.extra)
    (sourceDistinct : sourceEntry.allocation.extra.roots.toList.Nodup)
    (returnDistinct : returnEntry.allocation.extra.roots.toList.Nodup)
    (sourceOwned : Satisfies tracker S sourceEntry.allocation (Window S.allocation sourceOffset len.toNat))
    (returnOwned : Satisfies tracker R returnEntry.allocation (Window R.allocation returnOffset 1)) :
    ∃ ctx : Context before,
      ∃ sourceRole : RoleCover before tracker ctx .mut sourceOffset len.toNat,
      ∃ returnRole : RoleCover before tracker ctx .ret returnOffset 1,
        sourceRole.family=S ∧ returnRole.family=R ∧
        assignment.Binds sourceOccurrence sourceRole.family ∧ assignment.Binds returnOccurrence returnRole.family ∧
        Represents (DuplicatePrefixSliceArgument.placePointer argument) sourceRole.family.value ∧ Represents place.mplace.ptr returnRole.family.value ∧
        sourceRole.backing.allocation=sourceEntry.allocation ∧ returnRole.backing.allocation=returnEntry.allocation := by
  obtain ⟨ctx,sourceRole,returnRole,sourceFamily,returnFamily,sourceAllocation,returnAllocation,_,_⟩:=
    CurrentCallPointwiseSpatialCover.assemble_chains S R sourceOffset len.toNat returnOffset positive
      sourceEntry returnEntry sourceLive returnLive (bound_of_binding sourceLive sourcePhysical) (bound_of_binding returnLive returnPhysical)
      Fs Fr sourceOwner returnOwner composable sourceCharge returnCharge sourceCap returnCap sourceRuntime returnRuntime
      sourceOrder returnOrder sourceDistinct returnDistinct (to_chained sourceOwned) (to_chained_return returnOwned)
  obtain ⟨sourceRaw,sourceAt,sourceRepresents⟩:=assignment.actual_value sourceAssigned
  obtain ⟨returnRaw,returnAt,returnRepresents⟩:=assignment.actual_value returnAssigned
  have sourceEq : sourceRaw=(DuplicatePrefixSliceArgument.placePointer argument):=Option.some.inj (sourceAt.symm.trans sourceActual)
  have returnEq : returnRaw=place.mplace.ptr:=Option.some.inj (returnAt.symm.trans returnActual)
  subst sourceRaw
  subst returnRaw
  exact ⟨ctx,sourceRole,returnRole,sourceFamily,returnFamily,by rwa [sourceFamily],by rwa [returnFamily],
    by rwa [sourceFamily],by rwa [returnFamily],sourceAllocation,returnAllocation⟩

/-- Empty-source resource admission needs ONLY the assigned Bool family. No
source family, live allocation, grant or chain occurs in this interface. -/
theorem return_only {before tracker actual}
    (assignment : Assignment actual) (occurrence : Nat) (family : Family)
    (assigned : assignment.Binds occurrence family)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (live : before.memory.live.find? (fun row=>row.1==family.allocation)=some (family.allocation,entry))
    (offset : Nat) (physical : CandidateCallBindings.WindowBinding before family.value family.allocation offset 1)
    (cap : AllocationCapability before tracker family.allocation entry.allocation)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder entry.allocation.extra)
    (distinct : entry.allocation.extra.roots.toList.Nodup)
    (owned : Satisfies tracker family entry.allocation (Window family.allocation offset 1)) :
    ∃ ctx : Context before,∃ role : RoleCover before tracker ctx .ret offset 1,
      role.family=family ∧ role.backing.allocation=entry.allocation ∧ assignment.Binds occurrence role.family := by
  obtain ⟨_,grant,chain,binding,support⟩:=owned (family.allocation,offset) ⟨rfl,Nat.le_refl _,by omega⟩
  obtain ⟨C,parents,binding,issued,embeds⟩:=CurrentCallSupportChain.adequate cap runtime order distinct (family.at grant) rfl binding chain offset .exclusive support
  let backing : AllocationCover before:=⟨family.allocation,entry.allocation,cap.live,#[⟨offset,1,C,parents⟩],by
    intro i j different
    exact False.elim (different (Fin.ext (by have a:i.val<1:=i.isLt;have b:j.val<1:=j.isLt;omega)))⟩
  let ctx : Context before:=⟨#[backing],by simp⟩
  let role : RoleCover before tracker ctx .ret offset 1 :=
    { family:=family,backing:=backing,backingAt:=by simp [ctx],id:=rfl
      covered:=by intro byte hit;exact ⟨⟨0,by change 0<1;exact Nat.zero_lt_succ 0⟩,hit⟩
      roles:=by
        intro i overlap
        have zero : i.val=0:=by have a:i.val<1:=i.isLt;omega
        have same : i=⟨0,by change 0<1;exact Nat.zero_lt_succ 0⟩:=Fin.ext zero
        subst i
        refine ⟨grant,binding,issued,?_⟩
        intro byte request inside
        have equal : byte.2=offset:=by have h:=inside.2;change offset≤byte.2 ∧ byte.2<offset+1 at h;omega
        refine ⟨by have bound:=bound_of_binding live physical;change byte.2<entry.allocation.len;omega,?_⟩
        change Embeds entry.allocation tracker.global.protectedTags C grant byte.2 .exclusive
        rw [equal]
        exact embeds }
  exact ⟨ctx,role,rfl,rfl,assigned⟩

/-- Empty reference metadata and Bool ownership directly form the current
resource frontend. There is still NO source family/live allocation/chain and
NO claim that actual Call.entry-zero has executed. -/
theorem empty {options before tracker actual sourceOffset}
    (assignment : Assignment actual) (sourceOccurrence returnOccurrence : Nat)
    (argument : DuplicatePrefixSliceArgument.Argument) (place : MPlaceTy Provenance)
    (source : SourceSatisfies options before tracker assignment sourceOccurrence argument 0 sourceOffset)
    (family : Family) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (offset : Nat)
    (ret : ReturnSatisfies tracker assignment returnOccurrence place family entry.allocation offset)
    (live : before.memory.live.find? (fun row=>row.1==family.allocation)=some (family.allocation,entry))
    (physical : CandidateCallBindings.WindowBinding before family.value family.allocation offset 1)
    (cap : AllocationCapability before tracker family.allocation entry.allocation)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder entry.allocation.extra)
    (distinct : entry.allocation.extra.roots.toList.Nodup) :
    ∃ ctx : Context before,∃ role : RoleCover before tracker ctx .ret offset 1,
      role.family=family ∧ role.backing.allocation=entry.allocation ∧
      assignment.Binds returnOccurrence role.family ∧ Represents place.mplace.ptr role.family.value ∧
      place.layout=RootCompilerFacts.boolLayout ∧
      SourceSatisfies options before tracker assignment sourceOccurrence argument 0 sourceOffset := by
  obtain ⟨ctx,role,familyEq,allocationEq,assigned⟩:=return_only assignment returnOccurrence family ret.1 entry live offset physical cap runtime order distinct ret.2.2.2
  obtain ⟨raw,stored,represented⟩:=assignment.actual_value ret.1
  have same : raw=place.mplace.ptr:=Option.some.inj (stored.symm.trans ret.2.1)
  subst raw
  exact ⟨ctx,role,familyEq,allocationEq,assigned,by rwa [familyEq],ret.2.2.1,source⟩


end
end DuplicatePrefix.CurrentCallFamilySpatialAdmission
