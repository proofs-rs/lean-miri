import duplicate_prefix.CurrentCallResourceReleaseFrame
import duplicate_prefix.CurrentCallResourceInstallation
import duplicate_prefix.StackPopRelease

namespace DuplicatePrefix.CurrentCallResourceReleaseInstall
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources CurrentCallResourceNormalization
open GeneralBorrowProjection GeneralRangeMapOrigins
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

/-- Install one actual released tree before the next protector is processed.
This is the literal live-row commit used by StackPopRelease.Plan. -/
theorem window {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode) (exclusive : demandOf mode=.exclusive)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (_live : before.memory.live.find? (fun row=>row.1==id)=some (id,entry)) (allocation : entry.allocation=W.allocation)
    (tree : BorrowTree) (frame : tree={W.allocation.extra with locations:=tree.locations})
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (parents : ParentInterpretation tree W.precise.completion) (capacity : tree.locations.size=W.allocation.extra.locations.size)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
    (positive : start.toNat<(start+amount).toNat) (noWrap : (start+amount).toNat=start.toNat+amount.toNat)
    (owned : OwnedOn (S05CompletedAncestryReadMutable.Authority tree W.precise.completion tracker.global.protectedTags W.pointer.grant)
      start (start+amount) tree.locations) :
    let post:={before with memory:=StackPopRelease.commitTree before.memory id entry tree}
    ∃ Q : UniformWindow post tracker data owner id offset length mode,
      Q.loan=W.loan ∧ Q.pointer=W.pointer ∧ Q.allocation=W.allocation.setExtra tree ∧ Q.precise=W.precise := by
  let post:={before with memory:=StackPopRelease.commitTree before.memory id entry tree}
  have postLive:=StackPopRelease.lookup_commit_same before.memory id entry tree
  have postPresent : Present (ActualWorld post) id (W.allocation.setExtra tree) := by
    simp only [Present,ActualWorld,Array.toList_map]
    exact List.mem_map.mpr ⟨(id,{entry with allocation:=entry.allocation.setExtra tree}),
      Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some postLive),by simp only [allocation]⟩
  have metadata : ∀ index node,W.allocation.extra.nodes.get index=some node→
      ∃ changed,tree.nodes.get index=some changed ∧ changed.tag=node.tag ∧ changed.parent=node.parent ∧
        changed.isExposed=node.isExposed ∧ changed.defaultInitialPermission=node.defaultInitialPermission := by
    intro index node found
    exact ⟨node,by rw [frame];exact found,rfl,rfl,rfl,rfl⟩
  have issued:=CurrentCallResourceInstallation.spatial_frame W.issued post tracker tree postPresent rfl capacity
    (by intro position root found;rw [frame];exact found) metadata W.precise.completion (by intro root origin edge;exact edge)
  have binding : PointerBinds (W.allocation.setExtra tree) W.pointer := by
    obtain ⟨node,nodeAt,mapped,provenance⟩:=W.binding
    refine ⟨node,?_,?_,provenance⟩
    · change tree.nodes.get _=_;rw [frame];exact nodeAt
    · change tree.tagMapping.get _=_;rw [frame];exact mapped
  let Q : UniformWindow post tracker data owner id offset length mode := {
    loan:=W.loan,pointer:=W.pointer,allocation:=W.allocation.setExtra tree,precise:=W.precise,
    loanAt:=W.loanAt,pointerAt:=W.pointerAt,pointerId:=W.pointerId,present:=postPresent,
    preciseAt:=W.preciseAt,binding:=binding,issued:=issued,parents:=parents,window:=by
      intro byte inside
      refine ⟨(W.window byte inside).1,?_⟩
      rw [exclusive]
      intro segment member lower upper index node present
      change segment∈tree.locations.entries.toList at member
      obtain ⟨position,valid,same⟩:=Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
      subst segment
      have rights:=owned position valid positive (by have h:=inside.2;omega) (by have h:=inside.2;omega) index node present
      have actual:=CandidateCurrentGrantRuntime.realized _ _ (runtime.possible position valid index node present)
        ((runtime.formed.profile position valid).present index node present)
      constructor
      · intro below;exact local_token _ _ actual (rights.1 below)
      · intro clash
        apply Classical.byContradiction
        intro outside
        exact foreign_no_clash _ _ actual (rights.2 outside) clash }
  exact ⟨Q,rfl,rfl,rfl,rfl⟩

end
end DuplicatePrefix.CurrentCallResourceReleaseInstall
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceReleaseInstall" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual release-install dependency {dependency}"
