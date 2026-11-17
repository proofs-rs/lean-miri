import duplicate_prefix.CurrentCallParentInsertion
import duplicate_prefix.S04ZeroWildcardRuntime
import duplicate_prefix.WildcardHitPoolRoot

/-! A real zero-extent wildcard borrow adds an unassigned dormant root.
No source content family or virtual origin is issued by this frame. -/
namespace DuplicatePrefix.CurrentCallResourceZeroRoot
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentGrantResources CurrentCallResourceNormalization
open GeneralBorrowWildcardParentTagOrder GeneralBorrowExposedNonleafPrimaryPath
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
attribute [local irreducible] UniValMap.insert
noncomputable section

/-- Pad the old parent map with NONE. Every old entry remains identical;
the actual vacant allocator slot has no old edge by edgeLive. -/
def unassigned (C : Completion) (child : UniIndex) : Completion :=
  ⟨Array.ofFn (n:=max C.parents.size (child.toNat+1)) fun index => (C.parents[index.val]?).getD none,
   Array.ofFn (n:=max C.depths.size (child.toNat+1)) fun index => (C.depths[index.val]?).getD 0⟩

theorem old_parent (C : Completion) (child query : UniIndex) (bound : query.toNat<C.parents.size) :
    (unassigned C child).parents[query.toNat]?=C.parents[query.toNat]? := by
  simp [unassigned,show query.toNat<max C.parents.size (child.toNat+1) by omega,
    Array.getElem?_eq_getElem bound]

theorem edge_iff (C : Completion) (child query parent : UniIndex) :
    (unassigned C child).parents[query.toNat]?=some (some parent) ↔ C.parents[query.toNat]?=some (some parent) := by
  by_cases bound : query.toNat<C.parents.size
  · rw [old_parent C child query bound]
  · have missing : C.parents[query.toNat]?=none := Array.getElem?_eq_none (by omega)
    by_cases inside : query.toNat<max C.parents.size (child.toNat+1)
    · simp [unassigned,inside,missing]
    · simp [unassigned,inside,missing]

theorem below_iff (C : Completion) (child ancestor target : UniIndex) :
    Below (unassigned C child) ancestor target ↔ Below C ancestor target := by
  constructor <;> intro path
  · induction path with
    | refl => exact .refl _
    | @step parent target edge path ih => exact .step ((edge_iff C child target parent).mp edge) ih
  · induction path with
    | refl => exact .refl _
    | @step parent target edge path ih => exact .step ((edge_iff C child target parent).mpr edge) ih

theorem new_none (tree : BorrowTree) (C : Completion) (model : ParentInterpretation tree C)
    (child : UniIndex) (vacant : tree.nodes.get child=none) :
    (unassigned C child).parents[child.toNat]?=some none := by
  have noParent : (C.parents[child.toNat]?).getD none=none := by
    cases found : C.parents[child.toNat]? with
    | none => rfl
    | some value =>
      cases value with
      | none => rfl
      | some parent =>
        obtain ⟨node,present⟩ := (model.edgeLive child parent found).1
        rw [vacant] at present
        cases present
  simp [unassigned,show child.toNat<max C.parents.size (child.toNat+1) by omega,noParent]

theorem old_nodes (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index=some node) :
    (slot.after tag).nodes.get index=some node := by
  have different : index≠slot.index := by intro same;rw [same,slot.vacant] at present;cases present
  exact (GeneralBorrowFreshLocation.get_other _ _ _ _ different).trans present

theorem old_root (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (position : Nat) (root : UniIndex) (present : tree.roots[position]?=some root) :
    (slot.after tag).roots[position]?=some root := by
  have bound := (Array.getElem?_eq_some_iff.mp present).1
  simpa only [WildcardHitPoolRoot.Slot.after,WildcardHitZeroConstructor.installed,Array.getElem?_push,
    show position≠tree.roots.size by omega,↓reduceIte] using present

private theorem inserted_size (nodes : UniValMap TreeNode) (index : UniIndex) (node : TreeNode) :
    (nodes.insert index node).data.size=max nodes.data.size (index.toNat+1) := by
  simp only [UniValMap.insert,Id.run,pure]
  split <;> simp only [Array.size_set,UniValMap.extendTo,Array.size_append,Array.size_replicate] <;> omega

private theorem order_after (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (C : Completion) (model : ParentInterpretation tree C) : ParentTagOrder (slot.after tag) := by
  intro child childNode present parent parentNode edge parentAt
  change (tree.nodes.insert slot.index (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None)).get child=some childNode at present
  change (tree.nodes.insert slot.index (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None)).get parent=some parentNode at parentAt
  by_cases fresh : child=slot.index
  · subst child
    rw [GeneralBorrowFreshLocation.get_same] at present
    cases present
    cases edge
  · rw [GeneralBorrowFreshLocation.get_other _ _ _ _ fresh] at present
    have parentDifferent : parent≠slot.index := by
      intro same
      obtain ⟨oldParent,oldAt⟩ := (model.edgeLive child parent (model.physical child childNode present parent edge)).2
      rw [same,slot.vacant] at oldAt
      cases oldAt
    rw [GeneralBorrowFreshLocation.get_other _ _ _ _ parentDifferent] at parentAt
    exact model.order child childNode present parent parentNode edge parentAt

/-- The actual appended/reused root has no chosen logical parent. Old
virtual edges retain their exact origins; the new virtual obligation is empty. -/
theorem of_unassigned_root (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (C : Completion) (model : ParentInterpretation tree C)
    (primaryLive : ∃ node,tree.nodes.get allocationRoot=some node)
    (graph : GeneralBorrowStructuralHistoryState.GraphState (slot.after tag)) :
    ParentInterpretation (slot.after tag) (unassigned C slot.index) := by
  refine ⟨graph,order_after tree slot tag C model,?_,?_,?_,?_,?_⟩
  · simp only [unassigned,Array.size_ofFn,model.dimension,WildcardHitPoolRoot.Slot.after,
      WildcardHitZeroConstructor.installed,inserted_size]
  · intro index node present parent edge
    change (tree.nodes.insert slot.index (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None)).get index=some node at present
    by_cases fresh : index=slot.index
    · subst index
      rw [GeneralBorrowFreshLocation.get_same] at present
      cases present
      cases edge
    · rw [GeneralBorrowFreshLocation.get_other _ _ _ _ fresh] at present
      exact (edge_iff C slot.index index parent).mpr (model.physical index node present parent edge)
  · intro query parent edge
    obtain ⟨⟨node,present⟩,⟨parentNode,parentAt⟩⟩ := model.edgeLive query parent ((edge_iff C slot.index query parent).mp edge)
    exact ⟨⟨node,old_nodes tree slot tag query node present⟩,⟨parentNode,old_nodes tree slot tag parent parentNode parentAt⟩⟩
  · obtain ⟨primary,present⟩ := primaryLive
    have bound : allocationRoot.toNat<C.parents.size := by
      rw [model.dimension]
      exact GeneralBorrowNodeUpdate.lookup_valid _ _ _ present
    exact (old_parent C slot.index allocationRoot bound).trans model.primaryNone
  · intro position root rootAt origin edge
    have oldEdge := (edge_iff C slot.index root origin).mp edge
    obtain ⟨rootNode,rootPresent⟩ := (model.edgeLive root origin oldEdge).1
    have different : root≠slot.index := by intro same;rw [same,slot.vacant] at rootPresent;cases rootPresent
    have oldSlot : tree.roots[position]?=some root := by
      by_cases last : position=tree.roots.size
      · have same : root=slot.index := by
          simpa only [WildcardHitPoolRoot.Slot.after,WildcardHitZeroConstructor.installed,Array.getElem?_push,last,ite_true,Option.some.injEq] using rootAt.symm
        exact False.elim (different same)
      · simpa only [WildcardHitPoolRoot.Slot.after,WildcardHitZeroConstructor.installed,Array.getElem?_push,last,↓reduceIte] using rootAt
    obtain ⟨earlier,originRoot,oldRoot,oldOrigin,less,originSlot,oldRootAt,oldOriginAt,exposed,older,path⟩ :=
      model.virtual position root oldSlot origin oldEdge
    refine ⟨earlier,originRoot,oldRoot,oldOrigin,less,old_root tree slot tag earlier originRoot originSlot,
      old_nodes tree slot tag root oldRoot oldRootAt,old_nodes tree slot tag origin oldOrigin oldOriginAt,exposed,older,?_⟩
    apply GeneralBorrowSharedAuthorizationGeometry.path_extension tree (slot.after tag) _ originRoot origin path
    intro index node present
    exact ⟨node,old_nodes tree slot tag index node present,rfl⟩

private theorem vacant_not_below (tree : BorrowTree) (C : Completion) (model : ParentInterpretation tree C)
    (child target : UniIndex) (vacant : tree.nodes.get child=none)
    (live : ∃ node,tree.nodes.get target=some node) (path : Below C child target) : False := by
  induction path with
  | refl => obtain ⟨node,present⟩ := live;rw [vacant] at present;cases present
  | @step parent target edge path ih => exact ih ((model.edgeLive target parent edge).2)

/-- Every ACTUAL row is framed, including reused slots. Runtime supplies
stored-none at the vacant index; node vacancy alone is not used as cleanliness. -/
theorem embeds (allocation : Allocation Provenance BorrowTree) (global : GlobalState) (C : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts allocation.extra global)
    (model : ParentInterpretation allocation.extra C)
    (slot : WildcardHitPoolRoot.Slot allocation.extra) (tag : BorTag)
    (grant : UniIndex) (grantNode : TreeNode) (grantAt : allocation.extra.nodes.get grant=some grantNode)
    (byte : Nat) (demand : Demand) (owned : Embeds allocation global.protectedTags C grant byte demand) :
    Embeds (allocation.setExtra (slot.after tag)) global.protectedTags (unassigned C slot.index) grant byte demand := by
  intro segment member lower upper index node present
  change segment ∈ allocation.extra.locations.entries.toList at member
  change (slot.after tag).nodes.get index=some node at present
  by_cases fresh : index=slot.index
  · subst index
    change (allocation.extra.nodes.insert slot.index (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None)).get slot.index=some node at present
    rw [GeneralBorrowFreshLocation.get_same] at present
    cases present
    have clean : segment.data.perms.get slot.index=none := by
      obtain ⟨position,valid,same⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
      rw [←same]
      exact DuplicatePrefixBorrowContract.vacant_clean runtime slot.index slot.vacant position valid
    constructor
    · intro below
      exact False.elim (vacant_not_below allocation.extra C model slot.index grant slot.vacant ⟨grantNode,grantAt⟩
        ((below_iff C slot.index slot.index grant).mp below))
    · intro clash
      cases flag : global.protectedTags.contains tag <;> cases demand <;>
        simp [RawState,clean,WildcardHitZeroConstructor.rootNode,TreeNode.defaultLocationState,
          denote,CandidateCurrentGrantResources.guard,Clash,flag] at clash
  · change (allocation.extra.nodes.insert slot.index (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None)).get index=some node at present
    rw [GeneralBorrowFreshLocation.get_other _ _ _ _ fresh] at present
    obtain ⟨localToken,noClash⟩ := owned segment member lower upper index node present
    exact ⟨fun below=>localToken ((below_iff C slot.index index grant).mp below),
      fun clash=>(below_iff C slot.index index grant).mpr (noClash clash)⟩

/-- An actual empty wildcard FnEntry root is unassigned and dormant at every
byte. The offset is unrestricted; no source content loan or origin is chosen. -/
theorem construct (allocation : Allocation Provenance BorrowTree) (global : GlobalState) (C : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts allocation.extra global)
    (model : ParentInterpretation allocation.extra C)
    (primaryLive : ∃ node,allocation.extra.nodes.get allocationRoot=some node)
    (slot : WildcardHitPoolRoot.Slot allocation.extra) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh allocation.extra.tagMapping tag)
    (room : allocation.extra.nodes.size+1≤4294967295)
    (tagBound : tag.value.toNat<global.nextPointerTag.value.toNat)
    (held : global.protectedTags.contains tag=true) (offset : UInt64) :
    allocation.extra.newChild (Size.ofBytes offset) .wildcard tag
      (DedupRangeMap.new Size.ZERO ChildBorrow.fnEntryLocation) (.ReservedFrz false) true=⟨slot.after tag,.ok ()⟩ ∧
    DuplicatePrefixBorrowContract.RuntimeFacts (slot.after tag) global ∧
    ParentInterpretation (slot.after tag) (unassigned C slot.index) ∧
    (unassigned C slot.index).parents[slot.index.toNat]?=some none ∧
    (slot.after tag).locations=allocation.extra.locations ∧
    (slot.after tag).nodes.size≤allocation.extra.nodes.size+1 ∧
    (slot.after tag).indexOfTag tag=some slot.index ∧
    (∀ grant grantNode,allocation.extra.nodes.get grant=some grantNode → ∀ byte demand,
      Embeds allocation global.protectedTags C grant byte demand →
      Embeds (allocation.setExtra (slot.after tag)) global.protectedTags (unassigned C slot.index) grant byte demand) := by
  have actual := slot.child tag fresh offset
  have facts := S04ZeroWildcardRuntime.construct allocation.extra global runtime tag fresh room tagBound held offset
  rw [actual] at facts
  have newAt : (slot.after tag).nodes.get slot.index=some (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None) :=
    GeneralBorrowFreshLocation.get_same _ _ _
  refine ⟨actual,facts.2.1,of_unassigned_root allocation.extra slot tag C model primaryLive facts.2.1.formed.toGraphState,
    new_none allocation.extra C model slot.index slot.vacant,rfl,facts.2.2.2,?_,?_⟩
  · exact facts.2.1.formed.allocator.nodeTags slot.index _ newAt
  · intro grant grantNode grantAt byte demand owned
    exact embeds allocation global C runtime model slot tag grant grantNode grantAt byte demand owned

end
end DuplicatePrefix.CurrentCallResourceZeroRoot

open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceZeroRoot" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved empty unassigned-root resource dependency {dependency}"
