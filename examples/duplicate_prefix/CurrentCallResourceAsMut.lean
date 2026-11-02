import duplicate_prefix.CurrentCallResourceLenCapability
import duplicate_prefix.CurrentCallResourceLenFacts

namespace DuplicatePrefix.CurrentCallResourceAsMut
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources CurrentCallResourceNormalization
open CurrentCallResourceEntryBody GeneralBorrowExposedNonleafPrimaryPath GeneralRangeMapOrigins
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

private theorem local_token (state : LocationState) (held : Bool)
    (realized : Realized state held) (right : OrdinaryBorrowAuthority.LocalWrite state held) :
    .exclusive ∈ tokens (denote state held) := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflicted => cases conflicted <;> cases accessed <;> cases held <;>
      simp_all [OrdinaryBorrowAuthority.LocalWrite,Realized,WellFormed,denote,tokens,LocationState.possible]
  | Cell | ReservedIM | Unique | Frozen | Disabled => cases accessed <;> cases held <;>
      simp_all [OrdinaryBorrowAuthority.LocalWrite,Realized,WellFormed,denote,tokens,LocationState.possible,Permission.isUnique]

private theorem foreign_no_clash (state : LocationState) (held : Bool)
    (realized : Realized state held) (right : OrdinaryBorrowAuthority.ForeignWrite state held) :
    ¬Clash (guard (denote state held)) .exclusive := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflicted => cases conflicted <;> cases accessed <;> cases held <;>
      simp_all [OrdinaryBorrowAuthority.ForeignWrite,Realized,WellFormed,denote,CandidateCurrentGrantResources.guard,Clash,LocationState.possible]
  | Cell | ReservedIM | Unique | Frozen | Disabled => cases accessed <;> cases held <;>
      simp_all [OrdinaryBorrowAuthority.ForeignWrite,Realized,WellFormed,denote,CandidateCurrentGrantResources.guard,Clash,LocationState.possible,Permission.isUnique]


variable {options remaining span root before tracker data owner id offset len W place limits count}
    {C : Conditions options remaining span #[] root before tracker data owner id offset len W place}
    (out : Output limits C count) (ready : CurrentCallResourceBodyReadiness.Ready C)
    {nextData nextOwner}
    {Q : UniformWindow (CurrentCallResourceSharedStage.machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ nextData nextOwner id offset len.toNat .mut}
    {stage : CurrentCallResourceSharedResources.Stage Q out.sourceOutput.tag (UInt64.ofNat offset) len (CurrentCallResourceBodyReadiness.current_room out ready)}
    (returned : CurrentCallResourceLenReturn.Result out ready Q stage)

include returned in
theorem binding : PointerBinds (CurrentCallResourceLenCapability.sourceAllocation out ready) Q.pointer := by
  have concrete : Q.pointer.value.provenance=.concrete id out.sourceOutput.tag:=by rw [returned.sourcePointer];rfl
  simp only [PointerBinds,CurrentCallResourceLenCapability.sourceAllocation,Allocation.setExtra,Allocation.mapExtra]
  refine ⟨returned.sourceNode,returned.sourceAt,returned.runtime.formed.allocator.nodeTags _ _ returned.sourceAt,?_⟩
  rw [concrete]
  exact ⟨Q.pointerId.symm,returned.sourceTag.symm⟩

theorem window (byte : CandidateFreezeContentResources.Byte) (inside : Window id offset len.toNat byte) :
    byte.2 < (CurrentCallResourceLenCapability.sourceAllocation out ready).len ∧
      Embeds (CurrentCallResourceLenCapability.sourceAllocation out ready) (CurrentCallResourceLenReturn.postTracker out ready).global.protectedTags
        returned.completion Q.pointer.grant byte.2 .exclusive := by
  have lenEq:=CurrentCallResourceLenCapability.source_len out ready returned
  refine ⟨by rw [lenEq];exact (Q.window byte inside).1,?_⟩
  obtain ⟨snapshot⟩:=CurrentCallResourceLenReturn.preStrongSnapshot out ready Q returned.sourcePointer returned.sourceAllocation stage
  have bounds : (UInt64.ofNat offset).toNat+len.toNat≤(CurrentCallResourceLenReturn.releasedTree out ready).locations.size.bytes.toNat:=by rw [returned.capacity];exact snapshot.bounds
  have noWrap : (UInt64.ofNat offset).toNat+len.toNat<2^64:=Nat.lt_of_le_of_lt bounds (UInt64.toNat_lt _)
  have endEq : (UInt64.ofNat offset+len).toNat=(UInt64.ofNat offset).toNat+len.toNat:=by simp only [UInt64.toNat_add,Nat.mod_eq_of_lt noWrap]
  have startEq := (CurrentCallResourceSharedStage.source_bounds out).1
  have byteLower : (UInt64.ofNat offset).toNat≤byte.2:=by have interval:=inside.2;omega
  have byteUpper : byte.2<(UInt64.ofNat offset+len).toNat:=by have interval:=inside.2;omega
  intro segment member lower upper index node present
  simp only [CurrentCallResourceLenCapability.sourceAllocation,Allocation.setExtra,Allocation.mapExtra] at member lower upper present ⊢
  obtain ⟨position,valid,same⟩:=Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
  subst segment
  have rights:=returned.owned position valid (by omega) (by omega) (by omega) index node present
  have realized:=CandidateCurrentGrantRuntime.realized _ _ (returned.runtime.possible position valid index node present)
    ((returned.runtime.formed.profile position valid).present index node present)
  constructor
  · intro below
    exact local_token _ _ realized (rights.1 below)
  · intro clash
    apply Classical.byContradiction
    intro outside
    exact foreign_no_clash _ _ realized (rights.2 outside) clash

private def viewData : Identities :=
  {nextData with interpretation:={nextData.interpretation with
    pointers:=nextData.interpretation.pointers.push Q.pointer
    loans:=nextData.interpretation.loans.push ⟨nextData.interpretation.pointers.size,some nextOwner,Q.loan.depth⟩
    precise:=nextData.interpretation.precise.push (id,{Q.precise with completion:=returned.completion})}}

private def view : UniformWindow returned.machine (CurrentCallResourceLenReturn.postTracker out ready) (viewData out ready returned)
    nextData.interpretation.loans.size id offset len.toNat .mut where
  loan:=⟨nextData.interpretation.pointers.size,some nextOwner,Q.loan.depth⟩
  pointer:=Q.pointer
  allocation:=CurrentCallResourceLenCapability.sourceAllocation out ready
  precise:={Q.precise with completion:=returned.completion}
  loanAt:=by simp [viewData]
  pointerAt:=by simp [viewData]
  pointerId:=Q.pointerId
  present:=CurrentCallResourceLenCapability.present out ready returned
  preciseAt:=by simp [viewData]
  binding:=binding out ready returned
  issued:=CurrentCallResourceLenCapability.issued out ready returned
  parents:=by simpa only [CurrentCallResourceLenCapability.sourceAllocation,Allocation.setExtra,Allocation.mapExtra,CurrentCallResourceLenReturn.Result.completion] using returned.parents
  window:=window out ready returned

/-- A technical current q view at the actual post-Len machine. It carries the
SAME pointer and chosen optional parents, without asserting a whole denotation. -/
theorem current : ∃ currentData currentOwner,
    ∃ current : UniformWindow returned.machine (CurrentCallResourceLenReturn.postTracker out ready) currentData currentOwner id offset len.toNat .mut,
      current.pointer=Q.pointer ∧ current.allocation=CurrentCallResourceLenCapability.sourceAllocation out ready ∧
      current.precise.completion=returned.completion :=
  ⟨viewData out ready returned,nextData.interpretation.loans.size,view out ready returned,rfl,rfl,rfl⟩

end
end DuplicatePrefix.CurrentCallResourceAsMut
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallResourceAsMut.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual resource AsMut dependency {dependency}"
