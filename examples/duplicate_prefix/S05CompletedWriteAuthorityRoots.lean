import duplicate_prefix.S05CompletedWriteAuthorityRoot
import duplicate_prefix.GeneralBorrowConcreteRowCutoffAccess

/-! The actual concrete-source root scan, with current authority obtained
from unchanged unvisited physical columns. Visited columns need no invariant.
This is one source operation, not preservation across later reborrows. -/
namespace DuplicatePrefix.S05CompletedWriteAuthorityRoots
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowExposedNonleafPrimaryPath OrdinaryBorrowAuthority
open GeneralBorrowWildcardParentTagOrder GeneralBorrowExposureCardinality
open GeneralBorrowConcreteRowCutoffAccess (State scan)
open DuplicatePrefix.BorrowRangeAccess
set_option autoImplicit false
set_option maxHeartbeats 4000000

private abbrev Good (tree : BorrowTree) (completion : Completion) (protections : ProtectedTags)
    (source : UniIndex) (state : State) : Prop :=
  state.2.1 = none ∧ LocationCoherent tree state.1 protections ∧
  GeneralBorrowLocationSifaConsistency.Profile tree state.1 protections ∧
  GeneralBorrowSnapshotReadRuntime.GlobalPossible tree state.1 ∧
  S05CompletedAncestryReadMutable.Authority tree completion protections source state.1

variable (tree : BorrowTree) (completion : Completion) (protections : ProtectedTags)
variable (complete : Completes tree completion) (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
variable (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
variable (selectedPosition : Nat) (selected source : UniIndex) (selectedNode : TreeNode)
variable (selectedSlot : tree.roots[selectedPosition]? = some selected)
variable (selectedPresent : tree.nodes.get selected = some selectedNode) (sourcePath : Path tree selected source)
variable (short : tree.nodes.size < 65536)
include complete formed depth order selectedSlot selectedPresent sourcePath short in
private theorem step (minimum : Option BorTag) (mode : ChildrenVisitMode) (range : ByteRange)
    (position : Nat) (valid : position < tree.roots.size) (state : State)
    (good : Good tree completion protections source state) :
    ∃ next, scan tree selected (some selectedNode.tag) minimum .Write protections mode range position state = .yield next ∧
      Good tree completion protections source next := by
  rcases state with ⟨location,status,stop⟩
  have statusEq := good.1
  dsimp only at statusEq
  subst status
  have lookup := Array.getElem?_eq_getElem valid
  by_cases stopped : stop = true
  · subst stop
    exact ⟨(location,none,true),by simp [scan],good⟩
  have stopFalse : stop = false := by cases stop <;> simp_all
  subst stop
  by_cases early : (mode == .SkipChildrenOfAccessed &&
      (match (tree.nodes.get tree.roots[position]).map TreeNode.tag, minimum with
      | some tag, some minimum => tag.value > minimum.value | _, _ => false)) = true
  · refine ⟨(location,none,true),?_,good⟩
    cases tagLookup : (tree.nodes.get tree.roots[position]).map TreeNode.tag <;>
      cases minimum <;> cases mode <;>
      simp only [scan,Id.run,pure,Option.isNone_none,Bool.not_false,Bool.true_and,ite_true,lookup,
        tagLookup, Bool.and_false,Bool.false_eq_true] at early ⊢ <;> simp_all <;> (intro impossible; exact False.elim ((UInt64.not_lt.mpr early) impossible))
  by_cases same : selected = tree.roots[position]
  · refine ⟨(location,none,false),?_,good⟩
    cases tagLookup : (tree.nodes.get tree.roots[position]).map TreeNode.tag <;>
      cases minimum <;> cases mode <;>
      simp only [scan,Id.run,pure,Option.isNone_none,Bool.not_false,Bool.true_and,ite_true,lookup,
        tagLookup, Bool.and_false,Bool.false_eq_true] at early ⊢ <;> simp_all <;> (intro impossible; exact False.elim ((UInt64.not_lt.mpr early) impossible))
  have different : tree.roots[position] ≠ selected := Ne.symm same
  have callback := S05CompletedWriteAuthorityRoot.access tree completion location protections complete depth order
    position selectedPosition tree.roots[position] selected source selectedNode lookup selectedSlot selectedPresent different
    sourcePath good.2.2.2.2 formed good.2.1 short good.2.2.1 good.2.2.2.1
  obtain ⟨done,removed,legal,matching,coherent,outside,profile,possible,vacant,authority⟩ := callback
  refine ⟨((tree.performWildcardAccessAt location tree.roots[position] (some selectedNode.tag) .Write protections (position != 0)).location,none,false),
    ?_,rfl,coherent,profile,possible,authority⟩
  · cases tagLookup : (tree.nodes.get tree.roots[position]).map TreeNode.tag <;>
      cases minimum <;> cases mode <;>
      simp only [scan,Id.run,pure,Option.isNone_none,Bool.not_false,Bool.true_and,ite_true,lookup,
        tagLookup,Bool.and_false,Bool.false_eq_true] at early ⊢ <;> simp_all <;> (intro impossible; exact False.elim ((UInt64.not_lt.mpr early) impossible))
include complete formed depth order selectedSlot selectedPresent sourcePath short in
private theorem roots_from (minimum : Option BorTag) (mode : ChildrenVisitMode) (range : ByteRange)
    (start count : Nat) (bound : start+count ≤ tree.roots.size) (state : State)
    (good : Good tree completion protections source state) :
    Good tree completion protections source
      (forIn (List.range' start count) state
        (scan tree selected (some selectedNode.tag) minimum .Write protections mode range) : Id State) := by
  induction count generalizing start state with
  | zero => simpa only [List.range'_zero,List.forIn_nil,pure,Nat.add_zero] using good
  | succ count ih =>
    rw [List.range'_succ,List.forIn_cons]
    obtain ⟨next,actual,nextGood⟩ := step tree completion protections complete formed depth order
      selectedPosition selected source selectedNode selectedSlot selectedPresent sourcePath short minimum mode range start (by omega) state good
    simp only [actual,bind]
    have rest := ih (start+1) (by omega) next nextGood
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using rest

include complete formed depth order selectedSlot selectedPresent sourcePath short in
theorem roots (minimum : Option BorTag) (mode : ChildrenVisitMode) (range : ByteRange)
    (current : LocationTree) (coherent : LocationCoherent tree current protections)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree current protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree current)
    (authority : S05CompletedAncestryReadMutable.Authority tree completion protections source current) :
    let final := (forIn (List.range' 0 tree.roots.size) (current,none,false)
      (scan tree selected (some selectedNode.tag) minimum .Write protections mode range) : Id State)
    final.2.1 = none ∧ LocationCoherent tree final.1 protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree final.1 protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree final.1 ∧
      S05CompletedAncestryReadMutable.Authority tree completion protections source final.1 := by
  exact roots_from tree completion protections complete formed depth order selectedPosition selected source selectedNode
    selectedSlot selectedPresent sourcePath short minimum mode range 0 tree.roots.size (by omega) (current,none,false)
    ⟨rfl,coherent,profile,possible,authority⟩

end DuplicatePrefix.S05CompletedWriteAuthorityRoots
