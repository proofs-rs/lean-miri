import duplicate_prefix.S05CompletedAncestryWriteAccess
import duplicate_prefix.GeneralBorrowConcreteRowCutoffAccess

/-! The actual concrete-source root scan, with current authority obtained
from unchanged unvisited physical columns. Visited columns need no invariant.
This is one source operation, not preservation across later reborrows. -/
namespace DuplicatePrefix.S05CompletedAncestryWriteRoots
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowExposedNonleafPrimaryPath OrdinaryBorrowAuthority
open GeneralBorrowWildcardParentTagOrder GeneralBorrowExposureCardinality
open GeneralBorrowConcreteRowCutoffAccess (State scan)
open DuplicatePrefix.BorrowRangeAccess
set_option autoImplicit false
set_option maxHeartbeats 4000000

private abbrev Good (tree : BorrowTree) (initial selectedInitial : LocationTree) (protections : ProtectedTags)
    (selected : UniIndex) (next : Nat) (state : State) : Prop :=
  state.2.1 = none ∧ LocationCoherent tree state.1 protections ∧
  GeneralBorrowLocationSifaConsistency.Profile tree state.1 protections ∧
  GeneralBorrowSnapshotReadRuntime.GlobalPossible tree state.1 ∧
  (∀ position root, next ≤ position → tree.roots[position]? = some root → root ≠ selected →
    ∀ index node, tree.nodes.get index = some node → Path tree root index →
      state.1.perms.get index = initial.perms.get index) ∧
  ∀ index node, tree.nodes.get index = some node → Path tree selected index →
    state.1.perms.get index = selectedInitial.perms.get index

private theorem advance {tree initial selectedInitial protections selected next state}
    (good : Good tree initial selectedInitial protections selected next state) :
    Good tree initial selectedInitial protections selected (next+1) state := by
  refine ⟨good.1,good.2.1,good.2.2.1,good.2.2.2.1,?_,good.2.2.2.2.2⟩
  intro position root later slot different index node present path
  exact good.2.2.2.2.1 position root (by omega) slot different index node present path

variable (tree : BorrowTree) (completion : Completion) (initial selectedInitial : LocationTree) (protections : ProtectedTags)
variable (complete : Completes tree completion) (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
variable (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
variable (selectedPosition : Nat) (selected source : UniIndex) (selectedNode : TreeNode)
variable (selectedSlot : tree.roots[selectedPosition]? = some selected)
variable (selectedPresent : tree.nodes.get selected = some selectedNode) (sourcePath : Path tree selected source)
variable (localRights : ∀ (position : Nat) (root : UniIndex), tree.roots[position]? = some root → root ≠ selected →
  ∀ index node, tree.nodes.get index = some node → Path tree root index → Below completion index source →
  LocalWrite ((initial.perms.get index).getD node.defaultLocationState) (protections.contains node.tag))
variable (foreignRights : ∀ (position : Nat) (root : UniIndex), tree.roots[position]? = some root → root ≠ selected →
  ∀ index node, tree.nodes.get index = some node → Path tree root index → ¬Below completion index source →
  ForeignWrite ((initial.perms.get index).getD node.defaultLocationState) (protections.contains node.tag))
variable (short : tree.nodes.size < 65536)

include complete formed depth order selectedSlot selectedPresent sourcePath localRights foreignRights short in
private theorem step (minimum : Option BorTag) (mode : ChildrenVisitMode) (range : ByteRange)
    (position : Nat) (valid : position < tree.roots.size) (state : State)
    (good : Good tree initial selectedInitial protections selected position state) :
    ∃ next, scan tree selected (some selectedNode.tag) minimum .Write protections mode range position state = .yield next ∧
      Good tree initial selectedInitial protections selected (position+1) next := by
  rcases state with ⟨location,status,stop⟩
  have statusEq := good.1
  dsimp only at statusEq
  subst status
  have lookup := Array.getElem?_eq_getElem valid
  by_cases stopped : stop = true
  · subst stop
    exact ⟨(location,none,true),by simp [scan],advance good⟩
  have stopFalse : stop = false := by cases stop <;> simp_all
  subst stop
  by_cases early : (mode == .SkipChildrenOfAccessed &&
      (match (tree.nodes.get tree.roots[position]).map TreeNode.tag, minimum with
      | some tag, some minimum => tag.value > minimum.value | _, _ => false)) = true
  · refine ⟨(location,none,true),?_,advance good⟩
    cases tagLookup : (tree.nodes.get tree.roots[position]).map TreeNode.tag <;>
      cases minimum <;> cases mode <;>
      simp only [scan,Id.run,pure,Option.isNone_none,Bool.not_false,Bool.true_and,ite_true,lookup,
        tagLookup, Bool.and_false,Bool.false_eq_true] at early ⊢ <;> simp_all <;> (intro impossible; exact False.elim ((UInt64.not_lt.mpr early) impossible))
  by_cases same : selected = tree.roots[position]
  · refine ⟨(location,none,false),?_,advance good⟩
    cases tagLookup : (tree.nodes.get tree.roots[position]).map TreeNode.tag <;>
      cases minimum <;> cases mode <;>
      simp only [scan,Id.run,pure,Option.isNone_none,Bool.not_false,Bool.true_and,ite_true,lookup,
        tagLookup, Bool.and_false,Bool.false_eq_true] at early ⊢ <;> simp_all <;> (intro impossible; exact False.elim ((UInt64.not_lt.mpr early) impossible))
  have different : tree.roots[position] ≠ selected := Ne.symm same
  have currentFrame := good.2.2.2.2.1 position tree.roots[position] (Nat.le_refl _) lookup different
  have callback := S05CompletedAncestryWriteAccess.access tree completion location protections complete depth order
    position selectedPosition tree.roots[position] selected source selectedNode lookup selectedSlot selectedPresent different
    sourcePath
    (fun index node present path below => by rw [currentFrame index node present path];exact localRights position tree.roots[position] lookup different index node present path below)
    (fun index node present path outside => by rw [currentFrame index node present path];exact foreignRights position tree.roots[position] lookup different index node present path outside)
    (fun index node present _ => good.2.2.1.present index node present)
    formed good.2.1 short good.2.2.1 good.2.2.2.1
  obtain ⟨done,removed,legal,matching,coherent,outside,profile,possible,vacant⟩ := callback
  refine ⟨((tree.performWildcardAccessAt location tree.roots[position] (some selectedNode.tag) .Write protections (position != 0)).location,none,false),
    ?_,rfl,coherent,profile,possible,?_,?_⟩
  · cases tagLookup : (tree.nodes.get tree.roots[position]).map TreeNode.tag <;>
      cases minimum <;> cases mode <;>
      simp only [scan,Id.run,pure,Option.isNone_none,Bool.not_false,Bool.true_and,ite_true,lookup,
        tagLookup,Bool.and_false,Bool.false_eq_true] at early ⊢ <;> simp_all <;> (intro impossible; exact False.elim ((UInt64.not_lt.mpr early) impossible))
  · intro future other later otherSlot otherDifferent index node present otherPath
    have notCurrent : ¬Path tree tree.roots[position] index := by
      intro currentPath
      obtain ⟨currentNode,currentPresent,currentParentless⟩ := complete.2.2.2.1 position tree.roots[position] lookup
      obtain ⟨otherNode,otherPresent,otherParentless⟩ := complete.2.2.2.1 future other otherSlot
      have equal := CompletedBorrowAncestry.physical_roots_unique currentPresent currentParentless
        otherPresent otherParentless currentPath otherPath
      have futureData := Array.getElem?_eq_some_iff.mp otherSlot
      have futureValid : future < tree.roots.size := futureData.1
      have positionEq : position = future := by
        apply complete.2.2.1.getElem_inj.mp
        change tree.roots[position] = tree.roots[future]
        exact equal.trans futureData.2.symm
      omega
    rw [outside index notCurrent]
    exact good.2.2.2.2.1 future other (by omega) otherSlot otherDifferent index node present otherPath
  · intro index node present selectedPath
    have notCurrent : ¬Path tree tree.roots[position] index := by
      intro currentPath
      obtain ⟨currentNode,currentPresent,currentParentless⟩ := complete.2.2.2.1 position tree.roots[position] lookup
      obtain ⟨selectedFound,selectedLookup,selectedParentless⟩ := complete.2.2.2.1 selectedPosition selected selectedSlot
      exact different (CompletedBorrowAncestry.physical_roots_unique currentPresent currentParentless
        selectedLookup selectedParentless currentPath selectedPath)
    rw [outside index notCurrent]
    exact good.2.2.2.2.2 index node present selectedPath

include complete formed depth order selectedSlot selectedPresent sourcePath localRights foreignRights short in
private theorem roots_from (minimum : Option BorTag) (mode : ChildrenVisitMode) (range : ByteRange)
    (start count : Nat) (bound : start+count ≤ tree.roots.size) (state : State)
    (good : Good tree initial selectedInitial protections selected start state) :
    Good tree initial selectedInitial protections selected (start+count)
      (forIn (List.range' start count) state
        (scan tree selected (some selectedNode.tag) minimum .Write protections mode range) : Id State) := by
  induction count generalizing start state with
  | zero => simpa only [List.range'_zero,List.forIn_nil,pure,Nat.add_zero] using good
  | succ count ih =>
    rw [List.range'_succ,List.forIn_cons]
    obtain ⟨next,actual,nextGood⟩ := step tree completion initial selectedInitial protections complete formed depth order
      selectedPosition selected source selectedNode selectedSlot selectedPresent sourcePath localRights foreignRights
      short minimum mode range start (by omega) state good
    simp only [actual,bind]
    have rest := ih (start+1) (by omega) next nextGood
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using rest

include complete formed depth order selectedSlot selectedPresent sourcePath localRights foreignRights short in
/-- The actual source root loop completes. Each future callback receives its
current scalar rights from its unchanged initial physical column; the selected
normal component remains fixed relative to the loop's actual starting row. -/
theorem roots (minimum : Option BorTag) (mode : ChildrenVisitMode) (range : ByteRange)
    (current : LocationTree) (coherent : LocationCoherent tree current protections)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree current protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree current)
    (frame : ∀ (position : Nat) (root : UniIndex), tree.roots[position]? = some root → root ≠ selected →
      ∀ index node, tree.nodes.get index = some node → Path tree root index →
        current.perms.get index = initial.perms.get index) :
    let final := (forIn (List.range' 0 tree.roots.size) (current,none,false)
      (scan tree selected (some selectedNode.tag) minimum .Write protections mode range) : Id State)
    final.2.1 = none ∧ LocationCoherent tree final.1 protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree final.1 protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree final.1 ∧
      (∀ index node, tree.nodes.get index = some node → Path tree selected index →
        final.1.perms.get index = current.perms.get index) := by
  have good : Good tree initial current protections selected 0 (current,none,false) := by
    refine ⟨rfl,coherent,profile,possible,?_,?_⟩
    · intro position root _ slot different index node present path
      exact frame position root slot different index node present path
    · intros;rfl
  have final := roots_from tree completion initial current protections complete formed depth order
    selectedPosition selected source selectedNode selectedSlot selectedPresent sourcePath localRights foreignRights short
    minimum mode range 0 tree.roots.size (by omega) (current,none,false) good
  exact ⟨final.1,final.2.1,final.2.2.1,final.2.2.2.1,final.2.2.2.2.2⟩

end DuplicatePrefix.S05CompletedAncestryWriteRoots

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05CompletedAncestryWriteRoots." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved actual root-scan dependency {dependency}"
