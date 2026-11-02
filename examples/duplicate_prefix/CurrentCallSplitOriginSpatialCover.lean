import duplicate_prefix.CurrentCallSplitOriginSpatialGraph

namespace DuplicatePrefix.CurrentCallSplitOriginSpatialCover
open Miri Miri.ABI Miri.Memory Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization CurrentCallSpatialCover
open CurrentCallSplitOriginTrace CurrentCallSplitOriginSpatialGraph
open GeneralBorrowWildcardParentTagOrder GeneralBorrowExposedNonleafPrimaryPath
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option cbv.maxSteps 4000000
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail
noncomputable section

def record (n : Nat) : TreeNode :=
  if n=0 then ⟨tag 1,none,#[ix 1,ix 2],.Disabled,.None,false,none⟩
  else if n=1 then ⟨tag 2,some (ix 0),#[],.ReservedFrz false,.Read,true,none⟩
  else if n=2 then ⟨tag 3,some (ix 0),#[],.ReservedFrz false,.Read,true,none⟩
  else ⟨tag 4,none,#[],.ReservedFrz false,.Read,false,none⟩

theorem records : finalNode 0=record 0 ∧ finalNode 1=record 1 ∧ finalNode 2=record 2 ∧ finalNode 3=record 3 := by cbv <;> decide +kernel

theorem final_order : ParentTagOrder finalWrite.tree := by
  intro child childNode childAt parent parentNode edge parentAt
  rcases lookup_cases child childNode childAt with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals rcases lookup_cases parent parentNode parentAt with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals simp only [records.1,records.2.1,records.2.2.1,records.2.2.2,record] at edge ⊢
  all_goals first | contradiction | decide

def completion (origin : Nat) : Completion := ⟨#[none,some (ix 0),some (ix 0),some (ix origin)],#[0,1,1,2]⟩

theorem origin_path (n : Nat) (eligible : n=1 ∨ n=2) : Path finalWrite.tree (ix 0) (ix n) := by
  have rootAt : finalWrite.tree.nodes.get (ix 0)=some (finalNode 0) := by cbv
  rcases eligible with rfl | rfl
  · exact .step (.refl _ _ rootAt) _ node_endpoints.1 (by rw [records.2.1];rfl)
  · exact .step (.refl _ _ rootAt) _ node_endpoints.2.1 (by rw [records.2.2.1];rfl)

theorem parents (n : Nat) (eligible : n=1 ∨ n=2) :
    ParentInterpretation finalWrite.tree (completion n) := by
  have rootAt : finalWrite.tree.nodes.get (ix 0)=some (finalNode 0) := by cbv
  have originAt : finalWrite.tree.nodes.get (ix n)=some (finalNode n) := by
    rcases eligible with rfl | rfl
    · exact node_endpoints.1
    · exact node_endpoints.2.1
  refine ⟨final_graph,final_order,by rw [final_metadata.1];rfl,?_,?_,rfl,?_⟩
  · intro index node present parent edge
    rcases lookup_cases index node present with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    all_goals simp only [records.1,records.2.1,records.2.2.1,records.2.2.2,record] at edge
    all_goals first | contradiction | (have eq := Option.some.inj edge; subst parent; rfl)
  · intro child parent edge
    have bound : child.toNat<4 := (Array.getElem?_eq_some_iff.mp edge).1
    have alt : child.toNat=0 ∨ child.toNat=1 ∨ child.toNat=2 ∨ child.toNat=3 := by omega
    have indexAt (k : Nat) (small : k<4) (position : child.toNat=k) : child=ix k :=
      GeneralBorrowNodeUpdate.index_injective _ _ (by simpa [ix,UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega : k<4294967296)] using position)
    rcases alt with h | h | h | h
    · have eq := indexAt 0 (by decide) h; subst child; simp [completion,ix,UniIndex.toNat] at edge
    · have eq := indexAt 1 (by decide) h; subst child
      have eq : parent=ix 0 := by simpa [completion,ix,UniIndex.toNat] using edge.symm
      subst parent;exact ⟨⟨_,node_endpoints.1⟩,⟨_,rootAt⟩⟩
    · have eq := indexAt 2 (by decide) h; subst child
      have eq : parent=ix 0 := by simpa [completion,ix,UniIndex.toNat] using edge.symm
      subst parent;exact ⟨⟨_,node_endpoints.2.1⟩,⟨_,rootAt⟩⟩
    · have eq := indexAt 3 (by decide) h; subst child
      have eq : parent=ix n := by simpa [completion,ix,UniIndex.toNat] using edge.symm
      subst parent;exact ⟨⟨_,node_endpoints.2.2.1⟩,⟨_,originAt⟩⟩
  · intro position root slot origin edge
    have bound : position<2 := by rw [final_metadata.2.1] at slot; exact (Array.getElem?_eq_some_iff.mp slot).1
    have alt : position=0 ∨ position=1 := by omega
    rcases alt with rfl | rfl
    · have same : root=ix 0 := by simpa [final_metadata.2.1] using slot.symm
      subst root;simp [completion,ix,UniIndex.toNat] at edge
    · have same : root=ix 3 := by simpa [final_metadata.2.1] using slot.symm
      subst root
      have same : origin=ix n := by simpa [completion,ix,UniIndex.toNat] using edge.symm
      subst origin
      refine ⟨0,ix 0,finalNode 3,finalNode n,by decide,by rw [final_metadata.2.1];rfl,
        node_endpoints.2.2.1,originAt,?_,?_,origin_path n eligible⟩
      · rcases eligible with rfl | rfl
        · exact node_endpoints.2.2.2.1
        · exact node_endpoints.2.2.2.2.1
      · rcases eligible with rfl | rfl <;> rw [records.2.2.2]
        · rw [records.2.1];decide
        · rw [records.2.2.1];decide

theorem no_opposite_parent (n : Nat) (eligible : n=1 ∨ n=2) (child : UniIndex) :
    (completion n).parents[child.toNat]? ≠ some (some (ix (3-n))) := by
  intro edge
  have bound : child.toNat<4 := (Array.getElem?_eq_some_iff.mp edge).1
  have alt : child.toNat=0 ∨ child.toNat=1 ∨ child.toNat=2 ∨ child.toNat=3 := by omega
  rcases eligible with rfl | rfl
  all_goals rcases alt with h | h | h | h
  all_goals simp [completion,h,ix] at edge

theorem opposite_below (n : Nat) (eligible : n=1 ∨ n=2) {last : UniIndex}
    (below : Below (completion n) (ix (3-n)) last) : last=ix (3-n) := by
  induction below with
  | refl => rfl
  | @step parent child edge prior ih =>
    subst parent
    exact False.elim (no_opposite_parent n eligible child edge)

theorem opposite_not_below (n : Nat) (eligible : n=1 ∨ n=2) :
    ¬ Below (completion n) (ix (3-n)) (ix 3) := by
  intro below
  have impossible := opposite_below n eligible below
  rcases eligible with rfl | rfl <;> simp [ix] at impossible

theorem entries_eq : finalWrite.tree.locations.entries=#[leftSegment,rightSegment] := by
  apply Array.ext
  · rw [final_segment_count]; rfl
  · intro i first second
    have alt : i=0 ∨ i=1 := by rw [final_segment_count] at first; omega
    rcases alt with rfl | rfl <;> rfl

theorem segment_cases (segment : RangeMapSegment LocationTree)
    (member : segment ∈ finalWrite.tree.locations.entries.toList) :
    segment=leftSegment ∨ segment=rightSegment := by
  rw [entries_eq] at member
  simpa using member

private theorem no_clash (state : LocationState) :
    ¬ Clash (guard (denote state false)) .exclusive := by
  cases state.permission <;> simp [Clash,CandidateCurrentGrantResources.guard,denote]

theorem row_tokens :
    .exclusive ∈ tokens (denote (RawState leftSegment.data (ix 0) (finalNode 0)) false) ∧
    .exclusive ∈ tokens (denote (RawState leftSegment.data (ix 1) (finalNode 1)) false) ∧
    .exclusive ∈ tokens (denote (RawState leftSegment.data (ix 3) (finalNode 3)) false) ∧
    .exclusive ∈ tokens (denote (RawState rightSegment.data (ix 0) (finalNode 0)) false) ∧
    .exclusive ∈ tokens (denote (RawState rightSegment.data (ix 2) (finalNode 2)) false) ∧
    .exclusive ∈ tokens (denote (RawState rightSegment.data (ix 3) (finalNode 3)) false) := by
  cbv <;> simp
  exact .tail _ (.head _)

theorem embeds_left : Embeds CurrentCallSplitOriginTypedInput.sourceAllocation {} (completion 1) (ix 3) 0 .exclusive := by
  intro segment member lower upper index node present
  rcases segment_cases segment member with rfl | rfl
  · rcases lookup_cases index node present with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨fun _ => row_tokens.1,fun clash => False.elim (no_clash _ clash)⟩
    · exact ⟨fun _ => row_tokens.2.1,fun clash => False.elim (no_clash _ clash)⟩
    · exact ⟨fun below => False.elim (opposite_not_below 1 (.inl rfl) below),fun clash => False.elim (no_clash _ clash)⟩
    · exact ⟨fun _ => row_tokens.2.2.1,fun clash => False.elim (no_clash _ clash)⟩
  · rw [segment_endpoints.2.2.2.2.1] at lower
    change 1 ≤ 0 at lower
    omega

theorem embeds_right : Embeds CurrentCallSplitOriginTypedInput.sourceAllocation {} (completion 2) (ix 3) 1 .exclusive := by
  intro segment member lower upper index node present
  rcases segment_cases segment member with rfl | rfl
  · rw [segment_endpoints.2.2.2.1] at upper
    change 1 < 1 at upper
    omega
  · rcases lookup_cases index node present with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨fun _ => row_tokens.2.2.2.1,fun clash => False.elim (no_clash _ clash)⟩
    · exact ⟨fun below => False.elim (opposite_not_below 2 (.inr rfl) below),fun clash => False.elim (no_clash _ clash)⟩
    · exact ⟨fun _ => row_tokens.2.2.2.2.1,fun clash => False.elim (no_clash _ clash)⟩
    · exact ⟨fun _ => row_tokens.2.2.2.2.2,fun clash => False.elim (no_clash _ clash)⟩

open CurrentCallSplitOriginTypedInput (sourceId sourceAllocation sourceEntry machine tracker sourcePointer)

theorem source_live : Present (ActualWorld machine) sourceId sourceAllocation := by
  unfold Present ActualWorld
  rw [Array.toList_map]
  exact List.mem_map.mpr ⟨(sourceId,sourceEntry),
    Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some CurrentCallSplitOriginTypedInput.source_present),rfl⟩

theorem capability : AllocationCapability machine tracker sourceId sourceAllocation := by
  refine ⟨source_live,by cbv,by cbv,?_,?_⟩
  · change finalWrite.tree.roots[0]?=some allocationRoot
    rw [final_metadata.2.1]
    rfl
  · refine ⟨finalNode 0,?_,?_,?_,?_⟩
    · cbv
    · rw [records.1];rfl
    · rw [records.1];rfl
    · rw [records.1];rfl

theorem issued (n : Nat) (eligible : n=1 ∨ n=2) :
    SpatialDelegation machine tracker sourceId sourceAllocation (completion n) (ix 3) := by
  have originAt : finalWrite.tree.nodes.get (ix n)=some (finalNode n) := by
    rcases eligible with rfl | rfl
    · exact node_endpoints.1
    · exact node_endpoints.2.1
  apply SpatialDelegation.wildcard (finalNode n) (finalNode 3) 0 1 (ix 0)
  · exact .concrete (.allocated capability) (origin_path n eligible)
  · exact originAt
  · rcases eligible with rfl | rfl
    · exact node_endpoints.2.2.2.1
    · exact node_endpoints.2.2.2.2.1
  · exact node_endpoints.2.2.1
  · exact node_endpoints.2.2.2.2.2.1
  · rcases eligible with rfl | rfl <;> rw [records.2.2.2]
    · rw [records.2.1];decide
    · rw [records.2.2.1];decide
  · decide
  · change finalWrite.tree.roots[0]?=some (ix 0);rw [final_metadata.2.1];rfl
  · change finalWrite.tree.roots[1]?=some (ix 3);rw [final_metadata.2.1];rfl
  · exact origin_path n eligible
  · rfl

def family : Family := ⟨0,sourceId,sourcePointer⟩

theorem binding : PointerBinds sourceAllocation (family.at (ix 3)) := by
  refine ⟨finalNode 3,node_endpoints.2.2.1,?_,?_⟩
  · exact final_graph.allocator.nodeTags _ _ node_endpoints.2.2.1
  · change sourceId=sourceId ∧ tag 4=(finalNode 3).tag
    rw [records.2.2.2];exact ⟨rfl,rfl⟩

def backing : AllocationCover machine where
  id := sourceId
  allocation := sourceAllocation
  live := source_live
  cells := #[⟨0,1,completion 1,parents 1 (.inl rfl)⟩,⟨1,1,completion 2,parents 2 (.inr rfl)⟩]
  disjoint := by
    intro i j different byte first second
    have hi : i.val=0 ∨ i.val=1 := by have := i.isLt; change i.val<2 at this;omega
    have hj : j.val=0 ∨ j.val=1 := by have := j.isLt; change j.val<2 at this;omega
    rcases hi with hi | hi
    all_goals rcases hj with hj | hj
    all_goals
      cases i with
      | mk iv ib =>
        cases j with
        | mk jv jb =>
          dsimp only at hi hj
          subst iv
          subst jv
          dsimp [Window] at first second
          first | exact False.elim (different (Fin.ext rfl)) | omega

def context : Context machine where
  allocations := #[backing]
  unique := by simp

/-- The existing actual typed packet's SAME concrete V value has two fixed
spatial origin interpretations. Its actual interpreter rows are untouched. -/
def sourceRole : RoleCover machine tracker context .mut 0 2 where
  family := family
  backing := backing
  backingAt := by simp [context]
  id := rfl
  covered := by
    intro byte hit
    have alt : byte.2=0 ∨ byte.2=1 := by have := hit.2;omega
    rcases alt with h | h
    · refine ⟨⟨0,by decide⟩,?_⟩
      change Window sourceId 0 1 byte
      exact ⟨hit.1,by omega,by omega⟩
    · refine ⟨⟨1,by decide⟩,?_⟩
      change Window sourceId 1 1 byte
      exact ⟨hit.1,by omega,by omega⟩
  roles := fun i overlap =>
    if h : i.val=0 then by
      have eq : i=⟨0,by decide⟩ := Fin.ext h
      subst i
      refine ⟨ix 3,binding,issued 1 (.inl rfl),?_⟩
      intro byte request cell
      have pos : byte.2=0 := by have := cell.2;change 0 ≤ byte.2 ∧ byte.2<0+1 at this;omega
      refine ⟨?_,?_⟩
      · have len : sourceAllocation.len=2 := by cbv
        change byte.2<sourceAllocation.len
        rw [len,pos];decide
      · change Embeds sourceAllocation {} (completion 1) (ix 3) byte.2 .exclusive
        rw [pos];exact embeds_left
    else by
      have h : i.val=1 := by have := i.isLt;change i.val<2 at this;omega
      have eq : i=⟨1,by decide⟩ := Fin.ext h
      subst i
      refine ⟨ix 3,binding,issued 2 (.inr rfl),?_⟩
      intro byte request cell
      have pos : byte.2=1 := by have := cell.2;change 1 ≤ byte.2 ∧ byte.2<1+1 at this;omega
      refine ⟨?_,?_⟩
      · have len : sourceAllocation.len=2 := by cbv
        change byte.2<sourceAllocation.len
        rw [len,pos];decide
      · change Embeds sourceAllocation {} (completion 2) (ix 3) byte.2 .exclusive
        rw [pos];exact embeds_right

end
end DuplicatePrefix.CurrentCallSplitOriginSpatialCover
