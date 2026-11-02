import duplicate_prefix.CandidateCurrentJointCall
import duplicate_prefix.GeneralBorrowPrimaryWitnessVisibility

/-! Admission boundary: precise content ownership is invariant under replacing
raw location tables. This is a static independence result, not a permitted
machine transition, ordinary-input counterexample, or representation theorem. -/
namespace DuplicatePrefix.CandidateCurrentJointRawReplacement
open Miri Miri.Interpreter Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall
set_option autoImplicit false

def replaceAllocation (allocation : Allocation Provenance BorrowTree)
    (locations : DedupRangeMap LocationTree) : Allocation Provenance BorrowTree :=
  allocation.mapExtra (fun tree => {tree with locations := locations})

def replaceWorld (world : World)
    (locations : AllocId → Allocation Provenance BorrowTree → DedupRangeMap LocationTree) : World :=
  world.map fun (id,allocation) => (id,replaceAllocation allocation (locations id allocation))

theorem completes (tree : BorrowTree) (completion : Completion)
    (locations : DedupRangeMap LocationTree) (complete : Completes tree completion) :
    Completes {tree with locations := locations} completion := by
  refine ⟨complete.1,complete.2.1,complete.2.2.1,complete.2.2.2.1,complete.2.2.2.2.1,?_,complete.2.2.2.2.2.2⟩
  intro position root slot
  have original := complete.2.2.2.2.2.1 position root slot
  by_cases zero : position = 0
  · simpa only [zero,↓reduceIte] using original
  · simp only [zero,↓reduceIte] at original ⊢
    obtain ⟨earlier,originRoot,origin,rootNode,originNode,older,earlierSlot,rootHere,originHere,exposed,ordered,path,parent⟩ := original
    exact ⟨earlier,originRoot,origin,rootNode,originNode,older,earlierSlot,rootHere,originHere,exposed,ordered,
      GeneralBorrowPrimaryWitnessVisibility.path_nodes (before := {tree with locations := locations})
        (after := tree) rfl path,parent⟩

theorem present (world : World)
    (locations : AllocId → Allocation Provenance BorrowTree → DedupRangeMap LocationTree)
    (id : AllocId) (allocation : Allocation Provenance BorrowTree)
    (member : Present world id allocation) :
    Present (replaceWorld world locations) id (replaceAllocation allocation (locations id allocation)) := by
  simp only [Present,replaceWorld,Array.toList_map]
  exact List.mem_map.mpr ⟨(id,allocation),member,rfl⟩

/-- Neither active precise rights, finite loans nor joint content separation
observe raw permission/accessed/SIFA rows. Their validity therefore supplies no
constraint on the replacement locations. -/
theorem precise_joint (world : World) (held : ProtectedTags) (interpretation : Interpretation)
    (locations : AllocId → Allocation Provenance BorrowTree → DedupRangeMap LocationTree)
    (joint : PreciseJoint world held interpretation) :
    PreciseJoint (replaceWorld world locations) held interpretation := by
  refine ⟨⟨?_,joint.1.2.1,?_⟩,joint.2.1,joint.2.2.1,?_⟩
  · simpa only [replaceWorld,Array.toList_map,List.map_map,Function.comp_def] using joint.1.1
  · intro id precise member
    obtain ⟨allocation,live,complete,dimension,rows⟩ := joint.1.2.2 id precise member
    exact ⟨replaceAllocation allocation (locations id allocation),present world locations id allocation live,
      completes _ _ _ complete,dimension,rows⟩
  · intro byte owner charge found
    obtain ⟨loan,pointer,allocation,precise,loanAt,pointerAt,id,live,bound,preciseAt,rights,parent⟩ :=
      joint.2.2.2 byte owner charge found
    exact ⟨loan,pointer,replaceAllocation allocation (locations byte.1 allocation),precise,
      loanAt,pointerAt,id,present world locations byte.1 allocation live,bound,preciseAt,rights,parent⟩

/-- Replacement changes only the raw borrow-table rows of live allocations. -/
def replaceBefore (before : Before)
    (locations : AllocId → Allocation Provenance BorrowTree → DedupRangeMap LocationTree) : Before :=
  {before with memory := {before.memory with live := before.memory.live.map fun (id,entry) =>
    (id,{entry with allocation := replaceAllocation entry.allocation (locations id entry.allocation)})}}

theorem actual_world (before : Before)
    (locations : AllocId → Allocation Provenance BorrowTree → DedupRangeMap LocationTree) :
    ActualWorld (replaceBefore before locations) = replaceWorld (ActualWorld before) locations := by
  simp only [ActualWorld,replaceBefore,replaceWorld,Array.map_map,Function.comp_def]

theorem actual_bindings (before : Before) (argument : DuplicatePrefixSliceArgument.Argument)
    (len : UInt64) (place : MPlaceTy Provenance) (held : ProtectedTags)
    (call : CallLoans) (data : Identities)
    (locations : AllocId → Allocation Provenance BorrowTree → DedupRangeMap LocationTree)
    (bindings : ActualBindings before argument len place held call data) :
    ActualBindings (replaceBefore before locations) argument len place held call data := by
  refine ⟨bindings.1,bindings.2.1,bindings.2.2.1,?_,bindings.2.2.2.2.1,bindings.2.2.2.2.2⟩
  intro pointer member
  obtain ⟨allocation,live,bound⟩ := bindings.2.2.2.1 pointer member
  refine ⟨replaceAllocation allocation (locations pointer.allocation allocation),?_,bound⟩
  rw [actual_world]
  exact present _ _ _ _ live

end DuplicatePrefix.CandidateCurrentJointRawReplacement

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CandidateCurrentJointRawReplacement." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved raw-replacement dependency {dependency}"
