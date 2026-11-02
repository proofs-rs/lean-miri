import duplicate_prefix.CurrentCallResourceRootPhysical
import duplicate_prefix.CurrentCallResourceAccess

namespace DuplicatePrefix.CurrentCallResourceFinalWrite
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources CurrentCallResourceNormalization
open GeneralRangeMapOrigins
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

/-- A one-pointer operational dictionary is created only in the actual
post-release world. It asserts neither a historical loan nor CurrentDenotation. -/
private def viewData (id : AllocId) (original : PointerInstance) (completion : Completion) : Identities :=
  ⟨⟨#[(id,⟨completion,#[]⟩)],#[original],#[⟨0,none,0⟩],fun _ _=>none⟩,#[],#[]⟩

/-- Original-pointer Write from current post-release resources, without an
initial live UniformWindow or historical identity dictionary. -/
theorem completed_pointer {id offset post next place}
    (original : PointerInstance) (originalId : original.allocation=id)
    (physical : CurrentCallBoolScalarWrite.Window post place)
    (sameId : physical.id=id) (sameOffset : physical.offset.toNat=offset) (samePointer : physical.pointer=original.value)
    (completion : Completion)
    (binding : PointerBinds physical.entry.allocation original)
    (issued : SpatialDelegation post next id physical.entry.allocation completion original.grant)
    (parents : ParentInterpretation physical.entry.allocation.extra completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts physical.entry.allocation.extra next.global)
    (distinct : physical.entry.allocation.extra.roots.toList.Nodup) (short : physical.entry.allocation.extra.nodes.size<65536)
    (owned : OwnedOn (S05CompletedAncestryReadMutable.Authority physical.entry.allocation.extra completion next.global.protectedTags original.grant)
      physical.offset (physical.offset+1) physical.entry.allocation.extra.locations) :
    (physical.entry.allocation.extra.performBorrowAccessRange (S04ReturnBorrowBridge.extra physical.pointer.provenance)
      (Size.ofBytes physical.offset) (Size.ofBytes 1) .Write next.global.protectedTags .VisitChildrenOfAccessed).status=.Completed := by
  have bound:=physical.bounds
  have limit:=physical.capacity.toNat_lt
  have noWrap : (physical.offset+1).toNat=physical.offset.toNat+1 := by
    simp only [UInt64.toNat_add,UInt64.toNat_one,Nat.mod_eq_of_lt (by omega : physical.offset.toNat+1<2^64)]
  have positive : physical.offset.toNat<(physical.offset+1).toNat := by omega
  have live : post.memory.live.find? (fun row=>row.1==id)=some (id,physical.entry) := by simpa only [sameId] using physical.live
  have present : Present (ActualWorld post) id physical.entry.allocation := by
    simp only [Present,ActualWorld,Array.toList_map]
    exact List.mem_map.mpr ⟨(id,physical.entry),Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live),rfl⟩
  let Q : UniformWindow post next (viewData id original completion) 0 id offset 1 .ret := {
    loan:=⟨0,none,0⟩,pointer:=original,allocation:=physical.entry.allocation,
    precise:=⟨completion,#[]⟩,loanAt:=by simp [viewData],pointerAt:=by simp [viewData],
    pointerId:=originalId,present:=present,preciseAt:=by simp [viewData],binding:=binding,issued:=issued,parents:=parents,
    window:=by
      intro byte inside
      refine ⟨?_,?_⟩
      · rw [physical.bytes]
        have interval:=inside.2
        omega
      · intro segment member lower upper index node present
        obtain ⟨position,valid,same⟩:=Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
        subst segment
        have rights:=owned position valid positive (by have interval:=inside.2;omega) (by have interval:=inside.2;omega) index node present
        have actual:=CandidateCurrentGrantRuntime.realized _ _ (runtime.possible position valid index node present)
          ((runtime.formed.profile position valid).present index node present)
        constructor
        · intro below;exact local_token _ _ actual (rights.1 below)
        · intro clash
          apply Classical.byContradiction
          intro outside
          exact foreign_no_clash _ _ actual (rights.2 outside) clash}
  obtain ⟨G⟩:=geometry_selected Q (CandidateCurrentGrantRuntime.tree_rows _ _ runtime) rfl
  have bounds : physical.offset.toNat+1≤physical.entry.allocation.extra.locations.size.bytes.toNat := by
    rw [issued.capability.treeExtent,physical.size]
    exact physical.bounds
  have contract:=CurrentCallResourceAccess.write_range Q G rfl distinct short runtime.formed.well
    (by intro position valid;exact ⟨runtime.coherent position valid,runtime.formed.profile position valid,runtime.possible position valid⟩)
    (Size.ofBytes physical.offset) (Size.ofBytes 1) physical.offset (physical.offset+1)
    (by exact Nat.le_of_eq sameOffset.symm) (by omega) (by simpa only [Size.ofBytes,UInt64.toNat_one] using bounds)
    (Nat.le_refl _) (Nat.le_refl _) .VisitChildrenOfAccessed
  have done:=contract.completed
  change (physical.entry.allocation.extra.performBorrowAccessRange
    (match original.value.provenance with | .concrete _ tag=>.concrete tag | .wildcard=>.wildcard)
    (Size.ofBytes physical.offset) (Size.ofBytes 1) .Write next.global.protectedTags .VisitChildrenOfAccessed).status=.Completed at done
  rw [←samePointer] at done
  exact done

/-- Backward-compatible uniform-window interface. -/
theorem completed {initial oldTracker data owner id offset post next place}
    (original : UniformWindow initial oldTracker data owner id offset 1 .ret)
    (physical : CurrentCallBoolScalarWrite.Window post place)
    (sameId : physical.id=id) (sameOffset : physical.offset.toNat=offset) (samePointer : physical.pointer=original.pointer.value)
    (completion : Completion)
    (binding : PointerBinds physical.entry.allocation original.pointer)
    (issued : SpatialDelegation post next id physical.entry.allocation completion original.pointer.grant)
    (parents : ParentInterpretation physical.entry.allocation.extra completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts physical.entry.allocation.extra next.global)
    (distinct : physical.entry.allocation.extra.roots.toList.Nodup) (short : physical.entry.allocation.extra.nodes.size<65536)
    (owned : OwnedOn (S05CompletedAncestryReadMutable.Authority physical.entry.allocation.extra completion next.global.protectedTags original.pointer.grant)
      physical.offset (physical.offset+1) physical.entry.allocation.extra.locations) :
    (physical.entry.allocation.extra.performBorrowAccessRange (S04ReturnBorrowBridge.extra physical.pointer.provenance)
      (Size.ofBytes physical.offset) (Size.ofBytes 1) .Write next.global.protectedTags .VisitChildrenOfAccessed).status=.Completed := by
  exact completed_pointer original.pointer original.pointerId physical sameId sameOffset samePointer completion binding issued parents runtime distinct short owned

end
end DuplicatePrefix.CurrentCallResourceFinalWrite
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceFinalWrite" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual final-write dependency {dependency}"
