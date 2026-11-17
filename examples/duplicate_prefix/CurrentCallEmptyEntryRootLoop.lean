import duplicate_prefix.CompletedBorrowAncestry
import duplicate_prefix.S05CompletedAncestryConcreteWrite
import duplicate_prefix.S04ZeroRootObserverCallbacks
import duplicate_prefix.DuplicatePrefixResidualWriteRepaired
import duplicate_prefix.GeneralBorrowConcreteRowCutoffAccess

/-! Proof-only factoring of the actual root scan for empty-entry Bool access.
The callback premise is internal operational composition: the empty-effect
consumer must derive it from original ancestry and its exact dormant-node frame.
GraphState supplies liveness/disjointness; no post-effect Completes is assumed. -/
namespace DuplicatePrefix.CurrentCallEmptyEntryRootLoop
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowExposedNonleafPrimaryPath OrdinaryBorrowAuthority
open GeneralBorrowWildcardParentTagOrder GeneralBorrowExposureCardinality GeneralBorrowProjection
open GeneralBorrowConcreteRowCutoffAccess (State scan)
open DuplicatePrefix.BorrowRangeAccess
set_option autoImplicit false
set_option maxHeartbeats 4000000

private abbrev Good (tree : BorrowTree) (initial selectedInitial : LocationTree) (protections : ProtectedTags)
    (selected : UniIndex) (retained : LocationTree → Prop) (next : Nat) (state : State) : Prop :=
  state.2.1 = none ∧ LocationCoherent tree state.1 protections ∧
  GeneralBorrowLocationSifaConsistency.Profile tree state.1 protections ∧
  GeneralBorrowSnapshotReadRuntime.GlobalPossible tree state.1 ∧
  (∀ position root, next ≤ position → tree.roots[position]? = some root → root ≠ selected →
    ∀ index node, tree.nodes.get index = some node → Path tree root index →
      state.1.perms.get index = initial.perms.get index) ∧
  (∀ index node, tree.nodes.get index = some node → Path tree selected index →
    state.1.perms.get index = selectedInitial.perms.get index) ∧ retained state.1

private theorem advance {tree initial selectedInitial protections selected retained next state}
    (good : Good tree initial selectedInitial protections selected retained next state) :
    Good tree initial selectedInitial protections selected retained (next+1) state := by
  refine ⟨good.1,good.2.1,good.2.2.1,good.2.2.2.1,?_,good.2.2.2.2.2⟩
  intro position root later slot different index node present path
  exact good.2.2.2.2.1 position root (by omega) slot different index node present path

variable (tree : BorrowTree) (initial selectedInitial : LocationTree) (protections : ProtectedTags)
variable (formed : GeneralBorrowStructuralHistoryState.GraphState tree) (distinct : tree.roots.toList.Nodup)
variable (selectedPosition : Nat) (selected : UniIndex)
variable (selectedSlot : tree.roots[selectedPosition]? = some selected)
variable (retained : LocationTree → Prop)
variable (maximum : Option BorTag) (kind : AccessKind)
variable (callback : ∀ (position : Nat) (root : UniIndex), tree.roots[position]? = some root → root ≠ selected →
  ∀ current : LocationTree, retained current →
  LocationCoherent tree current protections →
  GeneralBorrowLocationSifaConsistency.Profile tree current protections →
  GeneralBorrowSnapshotReadRuntime.GlobalPossible tree current →
  (∀ index node, tree.nodes.get index = some node → Path tree root index → current.perms.get index = initial.perms.get index) →
  let result := tree.performWildcardAccessAt current root maximum kind protections (position != 0)
  result.status = .Completed ∧ LocationCoherent tree result.location protections ∧
  GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
  GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
  (∀ query, ¬Path tree root query → result.location.perms.get query = current.perms.get query) ∧ retained result.location)

include formed distinct selectedSlot callback in
private theorem step (minimum : Option BorTag) (mode : ChildrenVisitMode) (range : ByteRange)
    (position : Nat) (valid : position < tree.roots.size) (state : State)
    (good : Good tree initial selectedInitial protections selected retained position state) :
    ∃ next, scan tree selected maximum minimum kind protections mode range position state = .yield next ∧
      Good tree initial selectedInitial protections selected retained (position+1) next := by
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
  obtain ⟨done,coherent,outProfile,possible,outside,nextRetained⟩ := callback position tree.roots[position] lookup different
    location good.2.2.2.2.2.2 good.2.1 good.2.2.1 good.2.2.2.1 currentFrame
  refine ⟨((tree.performWildcardAccessAt location tree.roots[position] maximum kind protections (position != 0)).location,none,false),
    ?_,rfl,coherent,outProfile,possible,?_,?_,nextRetained⟩
  · cases tagLookup : (tree.nodes.get tree.roots[position]).map TreeNode.tag <;>
      cases minimum <;> cases mode <;>
      simp only [scan,Id.run,pure,Option.isNone_none,Bool.not_false,Bool.true_and,ite_true,lookup,
        tagLookup,Bool.and_false,Bool.false_eq_true] at early ⊢ <;> simp_all <;> (intro impossible; exact False.elim ((UInt64.not_lt.mpr early) impossible))
  · intro future other later otherSlot otherDifferent index node present otherPath
    have notCurrent : ¬Path tree tree.roots[position] index := by
      intro currentPath
      obtain ⟨currentNode,currentPresent,currentParentless⟩ := formed.rootNodes tree.roots[position]
        (Array.mem_toList_iff.mpr (Array.mem_of_getElem? lookup))
      obtain ⟨otherNode,otherPresent,otherParentless⟩ := formed.rootNodes other
        (Array.mem_toList_iff.mpr (Array.mem_of_getElem? otherSlot))
      have equal := CompletedBorrowAncestry.physical_roots_unique currentPresent currentParentless
        otherPresent otherParentless currentPath otherPath
      have futureData := Array.getElem?_eq_some_iff.mp otherSlot
      have futureValid : future < tree.roots.size := futureData.1
      have positionEq : position = future := by
        apply distinct.getElem_inj.mp
        change tree.roots[position] = tree.roots[future]
        exact equal.trans futureData.2.symm
      omega
    rw [outside index notCurrent]
    exact good.2.2.2.2.1 future other (by omega) otherSlot otherDifferent index node present otherPath
  · intro index node present selectedPath
    have notCurrent : ¬Path tree tree.roots[position] index := by
      intro currentPath
      obtain ⟨currentNode,currentPresent,currentParentless⟩ := formed.rootNodes tree.roots[position]
        (Array.mem_toList_iff.mpr (Array.mem_of_getElem? lookup))
      obtain ⟨selectedFound,selectedLookup,selectedParentless⟩ := formed.rootNodes selected
        (Array.mem_toList_iff.mpr (Array.mem_of_getElem? selectedSlot))
      exact different (CompletedBorrowAncestry.physical_roots_unique currentPresent currentParentless
        selectedLookup selectedParentless currentPath selectedPath)
    rw [outside index notCurrent]
    exact good.2.2.2.2.2.1 index node present selectedPath

include formed distinct selectedSlot callback in
private theorem roots_from (minimum : Option BorTag) (mode : ChildrenVisitMode) (range : ByteRange)
    (start count : Nat) (bound : start+count ≤ tree.roots.size) (state : State)
    (good : Good tree initial selectedInitial protections selected retained start state) :
    Good tree initial selectedInitial protections selected retained (start+count)
      (forIn (List.range' start count) state
        (scan tree selected maximum minimum kind protections mode range) : Id State) := by
  induction count generalizing start state with
  | zero => simpa only [List.range'_zero,List.forIn_nil,pure,Nat.add_zero] using good
  | succ count ih =>
    rw [List.range'_succ,List.forIn_cons]
    obtain ⟨next,actual,nextGood⟩ := step tree initial selectedInitial protections formed distinct selectedPosition selected selectedSlot retained maximum kind callback minimum mode range start (by omega) state good
    simp only [actual,bind]
    have rest := ih (start+1) (by omega) next nextGood
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using rest

include formed distinct selectedSlot callback in
/-- The unchanged interpreter root loop consumes internal callback steps and
retains the selected component. This is an operation-composition lemma, not a
caller validity or ownership interface. -/
theorem roots (minimum : Option BorTag) (mode : ChildrenVisitMode) (range : ByteRange)
    (current : LocationTree) (currentRetained : retained current) (coherent : LocationCoherent tree current protections)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree current protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree current)
    (frame : ∀ (position : Nat) (root : UniIndex), tree.roots[position]? = some root → root ≠ selected →
      ∀ index node, tree.nodes.get index = some node → Path tree root index →
        current.perms.get index = initial.perms.get index) :
    let final := (forIn (List.range' 0 tree.roots.size) (current,none,false)
      (scan tree selected maximum minimum kind protections mode range) : Id State)
    final.2.1 = none ∧ LocationCoherent tree final.1 protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree final.1 protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree final.1 ∧
      (∀ index node, tree.nodes.get index = some node → Path tree selected index →
        final.1.perms.get index = current.perms.get index) ∧ retained final.1 := by
  have good : Good tree initial current protections selected retained 0 (current,none,false) := by
    refine ⟨rfl,coherent,profile,possible,?_,?_,currentRetained⟩
    · intro position root _ slot different index node present path
      exact frame position root slot different index node present path
    · intros;rfl
  have final := roots_from tree initial current protections formed distinct selectedPosition selected selectedSlot retained maximum kind callback
    minimum mode range 0 tree.roots.size (by omega) (current,none,false) good
  exact ⟨final.1,final.2.1,final.2.2.1,final.2.2.2.1,final.2.2.2.2.2⟩


/-- Actual concrete Write composition. The exact empty-effect caller derives
the callback factory; no completion of newly inserted dormant roots is needed. -/
theorem write (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree) (distinct : tree.roots.toList.Nodup)
    (selectedPosition : Nat) (selected source : UniIndex) (selectedNode sourceNode : TreeNode)
    (selectedSlot : tree.roots[selectedPosition]? = some selected)
    (selectedPresent : tree.nodes.get selected = some selectedNode) (sourcePresent : tree.nodes.get source = some sourceNode)
    (sourcePath : Path tree selected source)
    (normal : DuplicatePrefixBorrowAuthorization.Normal tree initial protections source)
    (coherent : LocationCoherent tree initial protections)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial)
    (callback : ∀ (position : Nat) (root : UniIndex), tree.roots[position]? = some root → root ≠ selected →
      ∀ current : LocationTree,LocationCoherent tree current protections →
      GeneralBorrowLocationSifaConsistency.Profile tree current protections →
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree current →
      (∀ index node,tree.nodes.get index = some node → Path tree root index → current.perms.get index = initial.perms.get index) →
      let result := tree.performWildcardAccessAt current root (some selectedNode.tag) .Write protections (position != 0)
      result.status = .Completed ∧ LocationCoherent tree result.location protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
      ∀ query,¬Path tree root query → result.location.perms.get query = current.perms.get query)
    (mode : ChildrenVisitMode) (range : ByteRange) :
    let result := source_tree_access_at tree initial (some source) .Write protections mode range
    source_access_status result = none ∧ LocationCoherent tree (source_access_location result) protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree (source_access_location result) protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree (source_access_location result) := by
  obtain ⟨depth⟩ := formed.depth
  obtain ⟨forest⟩ := formed.forest initial protections
  obtain ⟨actual,actualAt,parentless⟩ := formed.rootNodes selected (Array.mem_toList_iff.mpr (Array.mem_of_getElem? selectedSlot))
  have actualEq : actual = selectedNode := Option.some.inj (actualAt.symm.trans selectedPresent)
  subst actual
  have rootPath := S05CompletedAncestryNormal.root_path tree initial protections formed selected source selectedNode selectedPresent parentless sourcePath
  have normalDone := DuplicatePrefixNormalKind.access tree initial protections source .Write mode
    (DuplicatePrefixNormalKind.of_normal tree initial protections source normal .Write) formed sourceNode sourcePresent coherent
  have fits : tree.nodes.data.size ≤ 4294967296 := formed.fits
  have owned : GeneralBorrowCompatibleScopedNormal.Owned (source_normal_projection tree initial protections) source.toNat .Write normal.component := by
    intro index inside valid
    have sizes : (source_normal_projection tree initial protections).topology.nodes.size = tree.nodes.data.size := by
      unfold_general_projection;unfold_general_topology;simp only [Array.size_map]
    exact normal.permissions .Write index inside (by rw [←sizes];exact valid)
  have afterProfile := (GeneralBorrowCompatibleLocationSifaConsistency.normal tree initial protections source .Write mode
    fits depth formed.children sourceNode sourcePresent forest normal.component owned profile).2.2
  have afterPossible := GeneralBorrowCompatibleNormalPossible.normal tree initial protections source .Write mode fits forest
    (GeneralBorrowExposedScopedNormalMetadata.valid_aligned tree initial protections source sourceNode sourcePresent).1 normal possible
  have frame : ∀ (position : Nat) (root : UniIndex),tree.roots[position]? = some root → root ≠ selected →
      ∀ index node,tree.nodes.get index = some node → Path tree root index →
      (tree.performNormalAccessAt initial source .Write protections mode).location.perms.get index = initial.perms.get index := by
    intro position root rootAt different index node present path
    have member := Array.mem_toList_iff.mpr (Array.mem_of_getElem? rootAt)
    exact (GeneralBorrowNormalOtherRootFrame.access tree initial protections formed source selected root sourceNode sourcePresent normal rootPath member
      (Ne.symm different) .Write coherent mode).2.2.2 index node present path
  have final := roots tree initial protections formed distinct selectedPosition selected selectedSlot (fun _ => True) (some selectedNode.tag) .Write
    (fun position root rootAt different current _ cache sifa gp currentFrame => by
      obtain ⟨done,outCache,outProfile,outPossible,outside⟩ := callback position root rootAt different current cache sifa gp currentFrame
      exact ⟨done,outCache,outProfile,outPossible,outside,trivial⟩)
    (if mode == .SkipChildrenOfAccessed then source_min_exposed tree source else none) mode range
    (tree.performNormalAccessAt initial source .Write protections mode).location trivial normalDone.2.2 afterProfile afterPossible frame
  have ending : ((source_normal_projection tree initial protections).topology.ancestorPath source.toNat).getLast! = selected.toNat := by
    rw [List.getLast!_eq_getLast?_getD,rootPath];rfl
  have rootEq : (tree.performNormalAccessAt initial source .Write protections mode).access.root = selected.toNat :=
    (GeneralBorrowStorage.events_root _ _ .Write (source_normal_projection tree initial protections)).trans ending
  dsimp only
  simp_tree_helpers
  simp only [normalDone.1,normalDone.2.1,rootEq,GeneralBorrowProjection.index_self,Option.bind_some,selectedPresent,Option.map_some]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  simpa only [GeneralBorrowConcreteRowCutoffAccess.scan,Id.run,bind,pure] using
    (show _ from ⟨final.1,final.2.1,final.2.2.1,final.2.2.2.1⟩)

end DuplicatePrefix.CurrentCallEmptyEntryRootLoop

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CurrentCallEmptyEntryRootLoop." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved actual root-scan dependency {dependency}"
