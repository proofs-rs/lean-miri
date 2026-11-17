import duplicate_prefix.S03EmptyPopFactsRange
import duplicate_prefix.GeneralBorrowFreshFutureClean

namespace DuplicatePrefix.S03EmptyTagState
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralRangeMapState GeneralBorrowView GeneralBorrowProjection
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
attribute [local irreducible] UniValMap.insert

def Inactive (tree : BorrowTree) (index : UniIndex) : Prop :=
  Every (fun location => ∀ state, location.perms.get index = some state → state.accessed = false) tree.locations

structure Data (tree : BorrowTree) (tag : BorTag) (index : UniIndex) where
  node : TreeNode
  tagged : tree.indexOfTag tag = some index
  present : tree.nodeAt index = some node
  sameTag : node.tag = tag
  leaf : node.children = #[]
  hidden : node.isExposed = false
  inactive : Inactive tree index

theorem effective (tree : BorrowTree) (index : UniIndex) (node : TreeNode)
    (inactive : Inactive tree index) :
    Every (fun location => (GeneralBorrowWildcardVirtualLeaf.effective location index node).accessed = false) tree.locations := by
  intro position valid
  cases stored : tree.locations.entries[position].data.perms.get index with
  | none => simp only [GeneralBorrowWildcardVirtualLeaf.effective,stored,Option.getD_none,TreeNode.defaultLocationState]
  | some state => simpa only [GeneralBorrowWildcardVirtualLeaf.effective,stored,Option.getD_some] using inactive position valid state stored

theorem clean (tree : BorrowTree) (index : UniIndex) (clean : GeneralBorrowFreshFutureClean.Clean tree index) :
    Inactive tree index := by
  intro position valid state stored
  rw [clean position valid] at stored
  contradiction

private theorem get_map (map : UniValMap LocationState) (index : UniIndex) :
    (⟨map.data.map (Option.map stateShape)⟩ : UniValMap StateShape).get index = (map.get index).map stateShape := by
  unfold UniValMap.get
  simp only [Array.getElem?_map]
  cases cell : map.data[index.toNat]? with
  | none => rfl
  | some value => cases value <;> rfl

/-- Metadata/SIFA changes preserve the actual stored inactive bit. -/
theorem shape (before after : BorrowTree) (same : treeShape after = treeShape before)
    (index : UniIndex) (initial : Inactive before index) : Inactive after index := by
  have ranges := congrArg (fun row => row.2.2.1) same
  change after.locations.entries.map (fun s => (s.range,locationShape s.data)) =
    before.locations.entries.map (fun s => (s.range,locationShape s.data)) at ranges
  have sizes : after.locations.entries.size = before.locations.entries.size := by
    simpa only [Array.size_map] using congrArg Array.size ranges
  intro position valid state stored
  have oldValid : position < before.locations.entries.size := by rw [←sizes];exact valid
  have point := congrArg (fun rows => rows[position]?) ranges
  simp only [Array.getElem?_map,Array.getElem?_eq_getElem valid,Array.getElem?_eq_getElem oldValid,Option.map_some] at point
  have shapes := congrArg Prod.snd (Option.some.inj point)
  have lookup := congrArg (fun data => (⟨data⟩ : UniValMap StateShape).get index) shapes
  change (⟨(after.locations.entries[position].data.perms.data.map (Option.map stateShape))⟩ : UniValMap StateShape).get index =
    (⟨(before.locations.entries[position].data.perms.data.map (Option.map stateShape))⟩ : UniValMap StateShape).get index at lookup
  rw [get_map,get_map,stored] at lookup
  cases old : before.locations.entries[position].data.perms.get index with
  | none => simp only [old,Option.map_none,Option.map_some] at lookup;cases lookup
  | some previous =>
    have equal : stateShape state = stateShape previous := by simpa only [old,Option.map_some,Option.some.injEq] using lookup
    exact (congrArg Prod.snd equal).trans (initial position oldValid previous old)

/-- Real range materialization at another fresh slot retains all old inactive rows. -/
theorem modified (tree : BorrowTree) (index query : UniIndex) (offset len : Size) (state : LocationState)
    (different : query ≠ index) (well : tree.locations.WellFormed)
    (bounds : offset.bytes.toNat+len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (inactive : Inactive tree query) :
    Inactive {tree with locations := (tree.locations.modifyRange offset len
      (fun _ location => GeneralBorrowFreshMaterialization.materialized location index state)).state} query := by
  let predicate := fun location : LocationTree => ∀ value, location.perms.get query = some value → value.accessed = false
  have prepared := GeneralRangeMapSafety.iter_mut predicate tree.locations offset len well inactive bounds
  rw [GeneralBorrowFreshModify.state_exact tree.locations offset len _ well bounds]
  have fold : ∀ (positions : List Nat) (current : DedupRangeMap LocationTree), Every predicate current →
      Every predicate (positions.foldl (fun current position => GeneralBorrowFreshModify.atPosition current position
        (fun _ location => GeneralBorrowFreshMaterialization.materialized location index state)) current) := by
    intro positions
    induction positions with
    | nil => intro current all;exact all
    | cons position rest ih =>
      intro current all
      apply ih
      dsimp only [GeneralBorrowFreshModify.atPosition]
      split
      · rename_i valid
        apply replaced_every _ current position valid _ all
        intro value stored
        dsimp only [GeneralBorrowFreshMaterialization.materialized] at stored
        rw [GeneralBorrowFreshLocation.get_other _ index query state different] at stored
        exact all position valid value stored
      · exact all
  exact fold _ _ prepared.every

/-- The fixed-index empty tag survives a real ranged access from another source. -/
noncomputable def access (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (tag sourceTag : BorTag) (query source selected : UniIndex) (maximum : Option BorTag)
    (data : Data tree tag query) (different : query ≠ source)
    (offset len : UInt64)
    (positive : DuplicatePrefixBorrowAuthorization.Positive tree global.protectedTags (some source) (some selected) maximum offset len)
    (sourceTagged : tree.indexOfTag sourceTag = some source) (kind : AccessKind) (mode : ChildrenVisitMode) :
    Data (tree.performBorrowAccessRange (.concrete sourceTag) (Size.ofBytes offset) (Size.ofBytes len) kind global.protectedTags mode).tree tag query := by
  let result := tree.performBorrowAccessRange (.concrete sourceTag) (Size.ofBytes offset) (Size.ofBytes len) kind global.protectedTags mode
  have frame := GeneralBorrowFreshReadFrame.frame tree (.concrete sourceTag) (Size.ofBytes offset) (Size.ofBytes len) kind global.protectedTags mode
  have kept := S03EmptyPopFactsRange.concrete tree global runtime sourceTag source selected query maximum offset len positive
    sourceTagged data.node data.present data.leaf data.hidden different (effective tree query data.node data.inactive) kind mode
  refine ⟨data.node,?_,?_,data.sameTag,data.leaf,data.hidden,?_⟩
  · unfold BorrowTree.indexOfTag
    rw [congrArg BorrowTree.tagMapping frame]
    exact data.tagged
  · change result.tree.nodes.get query = some data.node
    rw [congrArg BorrowTree.nodes frame]
    exact data.present
  · intro position valid state stored
    have here := kept position valid
    simpa only [GeneralBorrowWildcardVirtualLeaf.effective,stored,Option.getD_some] using here

end DuplicatePrefix.S03EmptyTagState
