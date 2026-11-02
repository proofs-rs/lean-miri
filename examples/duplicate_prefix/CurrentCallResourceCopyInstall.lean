import duplicate_prefix.CurrentCallAllocationLicense
import duplicate_prefix.CurrentCallResourceReleaseInstall
namespace DuplicatePrefix.CurrentCallResourceCopyInstall
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources CurrentCallResourceNormalization GeneralRangeMapOrigins
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
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


/-- Reuse the exact current family in the actual physically copied allocation.
Only tree locations change; bytes, initialization and provenance may change. -/
theorem window {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode) (exclusive : demandOf mode=.exclusive)
    (post : Before) (updated : Allocation Provenance BorrowTree)
    (present : Present (ActualWorld post) id updated)
    (lengthEq : updated.len=W.allocation.len) (bytesEq : updated.byteSize=W.allocation.byteSize)
    (frame : updated.extra={W.allocation.extra with locations:=updated.extra.locations})
    (capacity : updated.extra.locations.size=W.allocation.extra.locations.size)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts updated.extra tracker.global)
    (parents : ParentInterpretation updated.extra W.precise.completion)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
    (positive : start.toNat<(start+amount).toNat) (noWrap : (start+amount).toNat=start.toNat+amount.toNat)
    (owned : OwnedOn (S05CompletedAncestryReadMutable.Authority updated.extra W.precise.completion tracker.global.protectedTags W.pointer.grant)
      start (start+amount) updated.extra.locations) :
    ∃ Q : UniformWindow post tracker data owner id offset length mode,
      Q.loan=W.loan ∧Q.pointer=W.pointer ∧Q.allocation=updated ∧Q.precise=W.precise:=by
  have metadata : ∀ index node,W.allocation.extra.nodes.get index=some node→
      ∃ changed,updated.extra.nodes.get index=some changed ∧changed.tag=node.tag ∧changed.parent=node.parent ∧
        changed.isExposed=node.isExposed ∧changed.defaultInitialPermission=node.defaultInitialPermission:=by
    intro index node found
    exact ⟨node,by rw [frame];exact found,rfl,rfl,rfl,rfl⟩
  have issued:=CurrentCallAllocationLicense.spatial W.issued post tracker updated present rfl lengthEq bytesEq capacity
    (by intro position root found;rw [frame];exact found) metadata W.precise.completion (by intro root origin edge;exact edge)
  have binding : PointerBinds updated W.pointer:=by
    obtain ⟨node,nodeAt,mapped,provenance⟩:=W.binding
    refine ⟨node,?_,?_,provenance⟩
    · rw [frame];exact nodeAt
    · rw [frame];exact mapped
  let Q : UniformWindow post tracker data owner id offset length mode:={
    loan:=W.loan,pointer:=W.pointer,allocation:=updated,precise:=W.precise,
    loanAt:=W.loanAt,pointerAt:=W.pointerAt,pointerId:=W.pointerId,present:=present,preciseAt:=W.preciseAt,
    binding:=binding,issued:=issued,parents:=parents,window:=by
      intro byte inside
      refine ⟨by rw [lengthEq];exact (W.window byte inside).1,?_⟩
      rw [exclusive]
      intro segment member lower upper index node found
      obtain ⟨position,valid,same⟩:=Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
      subst segment
      have rights:=owned position valid positive (by have h:=inside.2;omega) (by have h:=inside.2;omega) index node found
      have actual:=CandidateCurrentGrantRuntime.realized _ _ (runtime.possible position valid index node found)
        ((runtime.formed.profile position valid).present index node found)
      exact ⟨fun below=>local_token _ _ actual (rights.1 below),fun clash=>Classical.byContradiction (fun outside=>foreign_no_clash _ _ actual (rights.2 outside) clash)⟩}
  exact ⟨Q,rfl,rfl,rfl,rfl⟩
end
end DuplicatePrefix.CurrentCallResourceCopyInstall
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceCopyInstall" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual copied allocation window dependency {dependency}"
