import duplicate_prefix.S05CompletedAncestryReadQueries
import duplicate_prefix.GeneralBorrowConcreteRowCutoffAccess

/-! The production concrete Read root scan retains raw authority in every
other physical root, including roots it has already visited. The existing
Read DFS supplies callback completion and preservation. -/
namespace DuplicatePrefix.S05CompletedAncestryReadRoots
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowExposedNonleafPrimaryPath OrdinaryBorrowAuthority
open GeneralBorrowWildcardParentTagOrder GeneralBorrowExposureCardinality
open GeneralBorrowConcreteRowCutoffAccess (State scan)
set_option autoImplicit false
set_option maxHeartbeats 4000000

private def Rights (tree : BorrowTree) (completion : Completion) (location : LocationTree)
    (protections : ProtectedTags) (selected source : UniIndex) : Prop :=
  (∀ (position : Nat) (root : UniIndex), tree.roots[position]? = some root → root ≠ selected →
    ∀ index node, tree.nodes.get index = some node → Path tree root index → Below completion index source →
      LocalWrite ((location.perms.get index).getD node.defaultLocationState) (protections.contains node.tag)) ∧
  (∀ (position : Nat) (root : UniIndex), tree.roots[position]? = some root → root ≠ selected →
    ∀ index node, tree.nodes.get index = some node → Path tree root index → ¬Below completion index source →
      ForeignWrite ((location.perms.get index).getD node.defaultLocationState) (protections.contains node.tag))

private abbrev Good (tree : BorrowTree) (completion : Completion) (selectedInitial : LocationTree)
    (protections : ProtectedTags) (selected source : UniIndex) (state : State) : Prop :=
  state.2.1 = none ∧ LocationCoherent tree state.1 protections ∧
  GeneralBorrowLocationSifaConsistency.Profile tree state.1 protections ∧
  GeneralBorrowSnapshotReadRuntime.GlobalPossible tree state.1 ∧
  Rights tree completion state.1 protections selected source ∧
  ∀ index node, tree.nodes.get index = some node → Path tree selected index →
    state.1.perms.get index = selectedInitial.perms.get index

variable (tree : BorrowTree) (completion : Completion) (selectedInitial : LocationTree) (protections : ProtectedTags)
variable (complete : Completes tree completion) (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
variable (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
variable (selectedPosition : Nat) (selected source : UniIndex) (selectedNode : TreeNode)
variable (selectedSlot : tree.roots[selectedPosition]? = some selected)
variable (selectedPresent : tree.nodes.get selected = some selectedNode) (sourcePath : Path tree selected source)
variable (short : tree.nodes.size < 65536)

include complete formed depth order selectedSlot selectedPresent sourcePath short in
private theorem step (minimum : Option BorTag) (mode : ChildrenVisitMode) (range : ByteRange)
    (position : Nat) (valid : position < tree.roots.size) (state : State)
    (good : Good tree completion selectedInitial protections selected source state) :
    Good tree completion selectedInitial protections selected source
      (scan tree selected (some selectedNode.tag) minimum .Read protections mode range position state).value := by
  rcases state with ⟨location,status,stop⟩
  have statusEq := good.1
  dsimp only at statusEq
  subst status
  have lookup := Array.getElem?_eq_getElem valid
  by_cases stopped : stop = true
  · subst stop
    simpa [scan] using good
  have stopFalse : stop = false := by cases stop <;> simp_all
  subst stop
  by_cases early : (mode == .SkipChildrenOfAccessed &&
      (match (tree.nodes.get tree.roots[position]).map TreeNode.tag, minimum with
      | some tag, some minimum => tag.value > minimum.value | _, _ => false)) = true
  · have actual : scan tree selected (some selectedNode.tag) minimum .Read protections mode range position (location,none,false) = .yield (location,none,true) := by
      cases tagLookup : (tree.nodes.get tree.roots[position]).map TreeNode.tag <;>
        cases minimum <;> cases mode <;>
        simp only [scan,Id.run,pure,Option.isNone_none,Bool.not_false,Bool.true_and,ite_true,lookup,
        tagLookup, Bool.and_false,Bool.false_eq_true] at early ⊢ <;> simp_all <;> (intro impossible; exact False.elim ((UInt64.not_lt.mpr early) impossible))
    simpa only [actual,ForInStep.value] using good
  by_cases same : selected = tree.roots[position]
  · have actual : scan tree selected (some selectedNode.tag) minimum .Read protections mode range position (location,none,false) = .yield (location,none,false) := by
      cases tagLookup : (tree.nodes.get tree.roots[position]).map TreeNode.tag <;>
        cases minimum <;> cases mode <;>
        simp only [scan,Id.run,pure,Option.isNone_none,Bool.not_false,Bool.true_and,ite_true,lookup,
        tagLookup, Bool.and_false,Bool.false_eq_true] at early ⊢ <;> simp_all <;> (intro impossible; exact False.elim ((UInt64.not_lt.mpr early) impossible))
    simpa only [actual,ForInStep.value] using good
  have different : tree.roots[position] ≠ selected := Ne.symm same
  have callback := S05CompletedAncestryReadQueries.access_root_preserves tree completion location protections
    complete depth order position selectedPosition tree.roots[position] selected source selectedNode lookup
    selectedSlot selectedPresent different sourcePath
    (good.2.2.2.2.1.1 position tree.roots[position] lookup different)
    (good.2.2.2.2.1.2 position tree.roots[position] lookup different)
    formed good.2.1 short good.2.2.1 good.2.2.2.1
  obtain ⟨done,_,coherent,profile,possible,_,outside,localRight,foreignRight⟩ := callback
  let after := (tree.performWildcardAccessAt location tree.roots[position] (some selectedNode.tag) .Read protections (position != 0)).location
  have actual : scan tree selected (some selectedNode.tag) minimum .Read protections mode range position
      (location,none,false) = .yield (after,none,false) := by
    dsimp only [after]
    cases tagLookup : (tree.nodes.get tree.roots[position]).map TreeNode.tag <;>
      cases minimum <;> cases mode <;>
      simp only [scan,Id.run,pure,Option.isNone_none,Bool.not_false,Bool.true_and,ite_true,lookup,
        tagLookup,Bool.and_false,Bool.false_eq_true] at early ⊢ <;> simp_all <;> (intro impossible; exact False.elim ((UInt64.not_lt.mpr early) impossible))
  rw [actual]
  change Good tree completion selectedInitial protections selected source (after,none,false)
  dsimp only [after]
  refine ⟨rfl,coherent,profile,possible,⟨?_,?_⟩,?_⟩
  · intro otherPosition other slot differentOther index node present path below
    by_cases sameRoot : other = tree.roots[position]
    · subst other
      exact localRight index node present path below
    · have notCurrent : ¬Path tree tree.roots[position] index := by
        intro currentPath
        obtain ⟨currentNode,currentPresent,currentParentless⟩ := complete.2.2.2.1 position tree.roots[position] lookup
        obtain ⟨otherNode,otherPresent,otherParentless⟩ := complete.2.2.2.1 otherPosition other slot
        exact sameRoot (CompletedBorrowAncestry.physical_roots_unique currentPresent currentParentless
          otherPresent otherParentless currentPath path).symm
      rw [outside index notCurrent]
      exact good.2.2.2.2.1.1 otherPosition other slot differentOther index node present path below
  · intro otherPosition other slot differentOther index node present path below
    by_cases sameRoot : other = tree.roots[position]
    · subst other
      exact foreignRight index node present path below
    · have notCurrent : ¬Path tree tree.roots[position] index := by
        intro currentPath
        obtain ⟨currentNode,currentPresent,currentParentless⟩ := complete.2.2.2.1 position tree.roots[position] lookup
        obtain ⟨otherNode,otherPresent,otherParentless⟩ := complete.2.2.2.1 otherPosition other slot
        exact sameRoot (CompletedBorrowAncestry.physical_roots_unique currentPresent currentParentless
          otherPresent otherParentless currentPath path).symm
      rw [outside index notCurrent]
      exact good.2.2.2.2.1.2 otherPosition other slot differentOther index node present path below
  · intro index node present path
    have notCurrent : ¬Path tree tree.roots[position] index := by
      intro currentPath
      obtain ⟨currentNode,currentPresent,currentParentless⟩ := complete.2.2.2.1 position tree.roots[position] lookup
      obtain ⟨otherNode,otherPresent,otherParentless⟩ := complete.2.2.2.1 selectedPosition selected selectedSlot
      exact different (CompletedBorrowAncestry.physical_roots_unique currentPresent currentParentless
        otherPresent otherParentless currentPath path)
    rw [outside index notCurrent]
    exact good.2.2.2.2.2 index node present path

include complete formed depth order selectedSlot selectedPresent sourcePath short in
/-- Actual root-array Read scan, preserving both visited and future root tables. -/
theorem roots (minimum : Option BorTag) (mode : ChildrenVisitMode) (range : ByteRange)
    (coherent : LocationCoherent tree selectedInitial protections)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree selectedInitial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree selectedInitial)
    (localRights : ∀ (position : Nat) (root : UniIndex), tree.roots[position]? = some root → root ≠ selected →
      ∀ index node, tree.nodes.get index = some node → Path tree root index → Below completion index source →
        LocalWrite ((selectedInitial.perms.get index).getD node.defaultLocationState) (protections.contains node.tag))
    (foreignRights : ∀ (position : Nat) (root : UniIndex), tree.roots[position]? = some root → root ≠ selected →
      ∀ index node, tree.nodes.get index = some node → Path tree root index → ¬Below completion index source →
        ForeignWrite ((selectedInitial.perms.get index).getD node.defaultLocationState) (protections.contains node.tag)) :
    let final := (forIn (List.range' 0 tree.roots.size) (selectedInitial,none,false)
      (scan tree selected (some selectedNode.tag) minimum .Read protections mode range) : Id State)
    final.2.1 = none ∧ LocationCoherent tree final.1 protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree final.1 protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree final.1 ∧
      Rights tree completion final.1 protections selected source ∧
      (∀ index node, tree.nodes.get index = some node → Path tree selected index →
        final.1.perms.get index = selectedInitial.perms.get index) := by
  apply GeneralBorrowLoop.list_invariant _ _ (Good tree completion selectedInitial protections selected source)
  · intro position member state good
    apply step tree completion selectedInitial protections complete formed depth order selectedPosition selected source
      selectedNode selectedSlot selectedPresent sourcePath short minimum mode range position _ state good
    have bounded := List.mem_range'_1.mp member
    omega
  · exact ⟨rfl,coherent,profile,possible,⟨localRights,foreignRights⟩,by intros;rfl⟩

end DuplicatePrefix.S05CompletedAncestryReadRoots
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05CompletedAncestryReadRoots." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved Read root-scan dependency {dependency}"
