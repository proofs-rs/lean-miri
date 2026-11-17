import duplicate_prefix.S04ZeroReadSharedPositive
import duplicate_prefix.EmptyForestSharedPoolNext
import duplicate_prefix.GeneralBorrowFreshActiveWithin
import duplicate_prefix.S04ReturnReleaseInactive

namespace DuplicatePrefix.S03EmptySharedFrame
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowView GeneralRangeMapState
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
attribute [local irreducible] UniValMap.insert

/-- The old real-call allocator packet is the same initial data used by the
observer-preservation proof. No constructor success is included. -/
def observerInput {tree : BorrowTree} {parentTag tag : BorTag}
    (input : EmptyForestSharedPool.Input tree parentTag tag) :
    S04ZeroReadSharedEntry.Input tree parentTag tag :=
  ⟨input.parent,input.parentNode,input.depth,input.tagged,input.present,input.fresh,input.slot,input.clean⟩

private theorem lookup_shape (location : LocationTree) (index : UniIndex) :
    (⟨locationShape location⟩ : UniValMap StateShape).get index = (location.perms.get index).map stateShape := by
  unfold locationShape UniValMap.get
  simp only [Array.getElem?_map]
  cases location.perms.data[index.toNat]? <;> rfl

/-- Quiescence depends only on stored permission/accessed data, so the actual
SIFA loop preserves it even after the original zero tag gains descendants. -/
theorem quiescent_shape (before after : BorrowTree)
    (shape : after.locations.entries.map (fun row => (row.range,locationShape row.data)) =
      before.locations.entries.map (fun row => (row.range,locationShape row.data)))
    (index : UniIndex) (quiet : S04ReturnReleaseInactive.Quiescent before index) :
    S04ReturnReleaseInactive.Quiescent after index := by
  have sizes := congrArg Array.size shape
  simp only [Array.size_map] at sizes
  intro position valid state stored
  have oldValid : position < before.locations.entries.size := by omega
  have point := congrArg (fun rows => rows[position]?) shape
  simp only [Array.getElem?_map,Array.getElem?_eq_getElem valid,
    Array.getElem?_eq_getElem oldValid,Option.map_some] at point
  have same := congrArg (fun pair => (⟨pair.2⟩ : UniValMap StateShape).get index) (Option.some.inj point)
  rw [lookup_shape,lookup_shape,stored] at same
  cases previous : before.locations.entries[position].data.perms.get index with
  | none => simp only [previous,Option.map_none,Option.map_some] at same;cases same
  | some old =>
    have pair : stateShape state = stateShape old := by simpa only [previous,Option.map_some,Option.some.injEq] using same
    have perm := congrArg Prod.fst pair
    have active := congrArg Prod.snd pair
    rcases quiet position oldValid old previous with inactive | noAccess
    · exact .inl (active.trans inactive)
    · exact .inr (congrArg Permission.associatedAccess perm |>.trans noAccess)

theorem quiescent {tree : BorrowTree} {parentTag tag : BorTag}
    (input : EmptyForestSharedPool.Input tree parentTag tag) (index : UniIndex)
    (quiet : S04ReturnReleaseInactive.Quiescent tree index) :
    S04ReturnReleaseInactive.Quiescent input.after index := by
  apply quiescent_shape tree input.after _ index quiet
  exact congrArg (fun value => value.2.2.1) (GeneralBorrowSifaView.preserves input.stage input.parent .Read)

theorem activity {tree : BorrowTree} {parentTag tag : BorTag}
    (input : EmptyForestSharedPool.Input tree parentTag tag) (index : UniIndex) (kind : AccessKind)
    (lower upper : UInt64) (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree index kind lower upper) :
    GeneralBorrowFreshActiveWithin.ActiveWithin input.after index kind lower upper :=
  GeneralBorrowFreshActiveWithin.sifa_preserves input.stage input.parent .Read index kind lower upper active

/-- All old nodes keep their tag, parent and exposure bit. The constructor
parent's child list may grow; no obsolete leaf hypothesis is transported. -/
theorem old_node {tree : BorrowTree} {parentTag tag : BorTag}
    (input : EmptyForestSharedPool.Input tree parentTag tag) (index : UniIndex)
    (node : TreeNode) (present : tree.nodeAt index = some node) :
    ∃ next, input.after.nodeAt index = some next ∧ next.tag = node.tag ∧
      next.parent = node.parent ∧ next.isExposed = node.isExposed := by
  let staged := S04ZeroReadSharedAttach.liftNode input.parent input.index index node
  have stagePresent : input.stage.nodeAt index = some staged :=
    S04ZeroReadSharedAttach.old_lookup tree input.index input.parent input.parentNode
      (GeneralBorrowFreshAnchor.sharedNode tag input.parent) input.vacant input.present index node present
  obtain ⟨next,found,tagEq,parentEq,children,permission,exposed⟩ :=
    GeneralBorrowFreshMetadataChildSifa.node_fields input.stage input.parent .Read index staged stagePresent
  have fields : staged.tag = node.tag ∧ staged.parent = node.parent ∧ staged.isExposed = node.isExposed := by
    by_cases same : index = input.parent <;> simp only [staged,S04ZeroReadSharedAttach.liftNode,same,ite_true,ite_false,and_self]
  exact ⟨next,found,tagEq.trans fields.1,parentEq.trans fields.2.1,exposed.trans fields.2.2⟩

theorem tagged {tree : BorrowTree} {parentTag tag : BorTag}
    (input : EmptyForestSharedPool.Input tree parentTag tag) (oldTag : BorTag) (index : UniIndex)
    (known : tree.indexOfTag oldTag = some index) : input.after.indexOfTag oldTag = some index := by
  have different : tag ≠ oldTag := by
    intro same
    have fresh : tree.tagMapping.get tag = none := by
      simp only [UniKeyMap.get,GeneralBorrowTagMap.fresh_find tree.tagMapping tag input.fresh,Option.map_none]
    rw [same] at fresh
    change tree.tagMapping.get oldTag = none at fresh
    change tree.tagMapping.get oldTag = some index at known
    rw [fresh] at known
    cases known
  unfold BorrowTree.indexOfTag
  rw [input.mapping_after]
  exact (GeneralBorrowTagMap.pushed_get_old tree.tagMapping tag oldTag different input.index input.free).trans known

/-- The real zero shared constructor preserves the existing return-child
capability, activity and original zero-tag quiescence on the same tree. -/
theorem construct (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag tag : BorTag) (input : EmptyForestSharedPool.Input tree parentTag tag)
    (offset : UInt64) (isProtected : Bool)
    (source selected : Option UniIndex) (maximum : Option BorTag) (lower upper : UInt64)
    (positive : DuplicatePrefixBorrowAuthorization.Positive tree global.protectedTags source selected maximum lower upper)
    (observer : UniIndex) (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree observer .Write lower (lower+upper))
    (zero : UniIndex) (quiet : S04ReturnReleaseInactive.Quiescent tree zero) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) tag
      (DedupRangeMap.new (Size.ofBytes 0) GeneralBorrowFreshAnchor.sharedState) .Frozen isProtected
    actual = ⟨input.after,.ok ()⟩ ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive input.after global.protectedTags source selected maximum lower upper) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin input.after observer .Write lower (lower+upper) ∧
      S04ReturnReleaseInactive.Quiescent input.after zero := by
  have kept := S04ZeroReadSharedPositive.construct tree global runtime parentTag tag (observerInput input)
    runtime.formed.fits offset isProtected source selected maximum lower upper positive
  rw [input.child offset isProtected] at kept
  exact ⟨input.child offset isProtected,kept.2,activity input observer .Write lower (lower+upper) active,quiescent input zero quiet⟩

end DuplicatePrefix.S03EmptySharedFrame
