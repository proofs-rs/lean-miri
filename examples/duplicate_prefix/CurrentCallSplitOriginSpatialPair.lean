import duplicate_prefix.CurrentCallSplitOriginSpatialCover
import duplicate_prefix.CurrentCallSplitOriginTypedSeparation
import duplicate_prefix.GeneralBorrowStructuralHistorySeed
import duplicate_prefix.GeneralBorrowParentTagRootFrames

/-! One concrete common source/return spatial packet on the existing typed
split-origin machine. This is an admission test witness, not ordinary coverage. -/
namespace DuplicatePrefix.CurrentCallSplitOriginSpatialPair
open Miri Miri.ABI Miri.Memory Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization CurrentCallSpatialCover CandidateFreezeContentResources
open CurrentCallSplitOriginTrace (ix tag)
open CurrentCallSplitOriginTypedInput
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

def destinationNode : TreeNode := ⟨tag 5,none,#[],.Disabled,.None,false,none⟩
def destinationCompletion : Completion := ⟨#[none],#[0]⟩

theorem destination_only (index : UniIndex) (node : TreeNode)
    (present : destinationAllocation.extra.nodes.get index=some node) :
    index=ix 0 ∧ node=destinationNode := by
  have bound := GeneralBorrowNodeUpdate.lookup_valid destinationAllocation.extra.nodes index node present
  have zero : index.toNat=0 := by change index.toNat<1 at bound;omega
  have same : index=ix 0 := GeneralBorrowNodeUpdate.index_injective _ _ zero
  subst index
  have rootAt : destinationAllocation.extra.nodes.get (ix 0)=some destinationNode := rfl
  exact ⟨rfl,Option.some.inj (present.symm.trans rootAt)⟩

theorem destination_parents : ParentInterpretation destinationAllocation.extra destinationCompletion := by
  refine ⟨(GeneralBorrowStructuralHistorySeed.initial (tag 5) (Size.ofBytes 1)).toGraphState,
    GeneralBorrowParentTagRootFrames.new_root (tag 5) (Size.ofBytes 1),rfl,?_,?_,rfl,?_⟩
  · intro index node present parent edge
    obtain ⟨rfl,rfl⟩ := destination_only index node present
    cases edge
  · intro child parent edge
    have bound : child.toNat<1 := (Array.getElem?_eq_some_iff.mp edge).1
    have zero : child.toNat=0 := by omega
    simp [destinationCompletion,zero] at edge
  · intro position root slot origin edge
    have bound : position<1 := (Array.getElem?_eq_some_iff.mp slot).1
    have zero : position=0 := by omega
    subst position
    have same : root=ix 0 := (Option.some.inj slot).symm
    subst root
    cases edge

theorem destination_live : Present (ActualWorld machine) destinationId destinationAllocation := by
  unfold Present ActualWorld
  rw [Array.toList_map]
  exact List.mem_map.mpr ⟨(destinationId,destinationEntry),
    Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some destination_present),rfl⟩

theorem destination_capability : AllocationCapability machine tracker destinationId destinationAllocation := by
  refine ⟨destination_live,by cbv,by cbv,rfl,?_,⟩
  exact ⟨destinationNode,rfl,rfl,rfl,by decide +kernel⟩

def destinationFamily : Family := ⟨1,destinationId,destinationPointer⟩

theorem destination_binding : PointerBinds destinationAllocation (destinationFamily.at (ix 0)) :=
  ⟨destinationNode,rfl,by decide +kernel,rfl,rfl⟩

def destinationSegment : RangeMapSegment LocationTree := destinationAllocation.extra.locations.entries[0]

theorem destination_embeds : Embeds destinationAllocation tracker.global.protectedTags destinationCompletion (ix 0) 0 .exclusive := by
  intro segment member _ _ index node present
  have entries : destinationAllocation.extra.locations.entries=#[destinationSegment] := rfl
  rw [entries] at member
  have same : segment=destinationSegment := by simpa using member
  subst segment
  obtain ⟨rfl,rfl⟩ := destination_only index node present
  constructor
  · intro _
    change .exclusive ∈ tokens (denote ⟨.Unique,true,.None⟩ false)
    exact .tail _ (.head _)
  · intro clash
    change Clash (CandidateCurrentGrantResources.guard (denote ⟨.Unique,true,.None⟩ false)) .exclusive at clash
    cases clash

def destinationBacking : AllocationCover machine where
  id := destinationId
  allocation := destinationAllocation
  live := destination_live
  cells := #[⟨0,1,destinationCompletion,destination_parents⟩]
  disjoint := by
    intro i j different
    exact False.elim (different (Fin.ext (by have hi : i.val<1 := i.isLt;have hj : j.val<1 := j.isLt;omega)))

/-- Both roles use the same allocation-to-cover assignment. The source's two
original cells and completed origins are retained verbatim. -/
def context : Context machine where
  allocations := #[CurrentCallSplitOriginSpatialCover.backing,destinationBacking]
  unique := by change [sourceId,destinationId].Nodup;decide +kernel

def source : RoleCover machine tracker context .mut 0 2 where
  family := CurrentCallSplitOriginSpatialCover.sourceRole.family
  backing := CurrentCallSplitOriginSpatialCover.sourceRole.backing
  backingAt := by simp [context,CurrentCallSplitOriginSpatialCover.sourceRole]
  id := CurrentCallSplitOriginSpatialCover.sourceRole.id
  covered := CurrentCallSplitOriginSpatialCover.sourceRole.covered
  roles := CurrentCallSplitOriginSpatialCover.sourceRole.roles

def ret : RoleCover machine tracker context .ret 0 1 where
  family := destinationFamily
  backing := destinationBacking
  backingAt := by simp [context]
  id := rfl
  covered := by intro byte inside;exact ⟨⟨0,by decide⟩,inside⟩
  roles := by
    intro i _
    have zero : i.val=0 := by have bound : i.val<1 := i.isLt;omega
    have same : i=⟨0,by decide⟩ := Fin.ext zero
    subst i
    refine ⟨ix 0,destination_binding,.allocated destination_capability,?_⟩
    intro byte inside _
    have zero : byte.2=0 := by have := inside.2;change 0≤byte.2 ∧ byte.2<0+1 at this;omega
    refine ⟨?_,?_⟩
    · have len : destinationAllocation.len=1 := by cbv
      change byte.2<destinationAllocation.len
      rw [len];omega
    · change Embeds destinationAllocation tracker.global.protectedTags destinationCompletion (ix 0) byte.2 .exclusive
      rw [zero];exact destination_embeds

def sourceFragment : Fragment := by
  classical
  exact fun byte owner => if owner=0 ∧ Window sourceId 0 2 byte then some ⟨.mut,.active⟩ else none

def returnFragment : Fragment := by
  classical
  exact fun byte owner => if owner=1 ∧ Window destinationId 0 1 byte then some ⟨.ret,.active⟩ else none

theorem source_found {byte owner charge} (found : sourceFragment byte owner=some charge) :
    owner=0 ∧ Window sourceId 0 2 byte ∧ charge=⟨.mut,.active⟩ := by
  classical
  simp only [sourceFragment] at found
  split at found
  · rename_i hit
    exact ⟨hit.1,hit.2,(Option.some.inj found).symm⟩
  · cases found

theorem return_found {byte owner charge} (found : returnFragment byte owner=some charge) :
    owner=1 ∧ Window destinationId 0 1 byte ∧ charge=⟨.ret,.active⟩ := by
  classical
  simp only [returnFragment] at found
  split at found
  · rename_i hit
    exact ⟨hit.1,hit.2,(Option.some.inj found).symm⟩
  · cases found

theorem source_footprint (byte : Byte) (charge : Charge) :
    sourceFragment byte 0=some charge ↔ Window sourceId 0 2 byte ∧ charge=⟨.mut,.active⟩ := by
  classical
  constructor
  · intro found;exact (source_found found).2
  · rintro ⟨inside,rfl⟩;simp [sourceFragment,inside]

theorem return_footprint (byte : Byte) (charge : Charge) :
    returnFragment byte 1=some charge ↔ Window destinationId 0 1 byte ∧ charge=⟨.ret,.active⟩ := by
  classical
  constructor
  · intro found;exact (return_found found).2
  · rintro ⟨inside,rfl⟩;simp [returnFragment,inside]

theorem composable : Composable sourceFragment returnFragment := by
  classical
  refine ⟨?_,?_,?_,?_⟩
  · intro byte first second fc sc different left right
    exact False.elim (different ((source_found left).1.trans (source_found right).1.symm))
  · intro byte first second fc sc different left right
    exact False.elim (different ((return_found left).1.trans (return_found right).1.symm))
  · intro byte owner
    by_cases zero : owner=0
    · right;simp [returnFragment,zero]
    · left;simp [sourceFragment,zero]
  · intro byte first second fc sc left right
    have a := (source_found left).2.1.1
    have b := (return_found right).2.1.1
    have different : sourceId≠destinationId := by decide +kernel
    exact False.elim (different (a.symm.trans b))

theorem source_role_footprint (byte : Byte) (charge : Charge) :
    sourceFragment byte source.family.slot=some charge ↔
      Window source.backing.id 0 2 byte ∧ charge=⟨.mut,.active⟩ := source_footprint byte charge

theorem return_role_footprint (byte : Byte) (charge : Charge) :
    returnFragment byte ret.family.slot=some charge ↔
      Window ret.backing.id 0 1 byte ∧ charge=⟨.ret,.active⟩ := return_footprint byte charge

open Miri.Input CanonicalConfigFacts ActualReferenceContext CurrentCallTypedFnEntry
open CurrentCallSplitOriginTypedEntry (options remaining output finalFrame finalMachine)

/-- Actual positive spatial roles, composable Freeze fragments, physical
bindings, and the already proved Strong FnEntry operation coexist on the SAME
constructed packet. No general ordinary-domain implication is asserted. -/
theorem admission_test (span : PreparedContracts.FixedSpanQuery) (cmp : ProjectionMetadataFacts.NullComparator) :
    Nonempty (RoleCover machine tracker context .mut 0 2) ∧
    Nonempty (RoleCover machine tracker context .ret 0 1) ∧
    Composable sourceFragment returnFragment ∧
    source.family.value=sourcePointer ∧ ret.family.value=destinationPointer ∧
    OrdinaryPhysicalValidity.MutU8Slice sourceAllocation 0 2 ∧
    OrdinaryPhysicalValidity.BoolDestination destinationAllocation 0 ∧
    CandidateCallBindings.WindowBinding machine sourcePointer sourceId 0 2 ∧
    CandidateCallBindings.WindowBinding machine destinationPointer destinationId 0 1 ∧
    (¬∃ completion,ParentInterpretation sourceAllocation.extra completion ∧
      SpatialDelegation machine tracker sourceId sourceAllocation completion (ix 3) ∧
      ∀ byte,byte<2 → Embeds sourceAllocation tracker.global.protectedTags completion (ix 3) byte .exclusive) ∧
    output.global.protectedTags.get (tag 6)=some .StrongProtector ∧
    output.frame.protectedTags=#[(sourceId,tag 6)] ∧
    (∃ ctx : ActualReferenceContext.Context options remaining span,
      TypedRetag.retagPtrValue (adapted options remaining span ctx.pointers) options.limits.retag
        (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base sourcePointer 2 ActualReferenceMetadata.reference)
        ActualReferenceMetadata.reference.ty .FnEntry state =
        .ok (some (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
          (changedPointer sourcePointer sourceId (tag 6)) 2 ActualReferenceMetadata.reference))
          (Storage.withCurrent #[] finalFrame finalMachine) ∧
        finalMachine.borrowTracker=some ⟨output.global,tracker.retagMode⟩ ∧
        finalFrame.extra.borrowTracker=some output.frame ∧ finalFrame.returnPlace=.memory place) :=
  ⟨⟨source⟩,⟨ret⟩,composable,rfl,rfl,source_physical,destination_physical,source_binding,
    CurrentCallSplitOriginTypedInput.destination_binding,CurrentCallSplitOriginTypedSeparation.no_uniform_input,
    CurrentCallSplitOriginTypedEntry.actual_child.2.2.2.1,CurrentCallSplitOriginTypedEntry.actual_child.2.2.2.2.1,
    CurrentCallSplitOriginTypedEntry.typed_fnentry span cmp⟩

end
end DuplicatePrefix.CurrentCallSplitOriginSpatialPair
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallSplitOriginSpatialPair" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved split spatial-pair dependency {dependency}"
