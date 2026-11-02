import duplicate_prefix.GeneralBorrowFreshMetadataChildDefaultSlot
import duplicate_prefix.GeneralBorrowFreshInstallation
import duplicate_prefix.GeneralRangeMapCoverage

namespace DuplicatePrefix.GeneralBorrowDefaultReservationSlice
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralRangeMapOrigins
open GeneralBorrowFreshReborrowStages (Slot)
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def Reserved (query : UniIndex) (location : LocationTree) : Prop :=
  ∃ state, location.perms.get query = some state ∧ state.permission = .ReservedFrz false

/-- Real selected materialization overwrites every location on the requested
slice, regardless of stale permissions in the otherwise vacant slot. No global
Clean or reservation-typing premise is necessary for this inside-slice fact. -/
theorem modified (map : DedupRangeMap LocationTree) (index : UniIndex) (offset len : Size)
    (well : map.WellFormed) (bounds : offset.bytes.toNat+len.bytes.toNat ≤ map.size.bytes.toNat) :
    OwnedOn (Reserved index) offset.bytes (offset.bytes+len.bytes)
      (map.modifyRange offset len (fun _ location => GeneralBorrowFreshMaterialization.materialized location index GeneralBorrowFreshDefaultChild.inside)).state := by
  let modify := fun (_ : ByteRange) (location : LocationTree) => GeneralBorrowFreshMaterialization.materialized location index GeneralBorrowFreshDefaultChild.inside
  let prepared := map.iterMut offset len
  let changed := map.modifyRange offset len modify
  have sizes : changed.state.entries.size = prepared.state.entries.size := by
    rw [GeneralBorrowFreshModify.state_exact map offset len modify well bounds,GeneralBorrowFreshModify.fold_size]
  intro position valid positive start stop
  have oldValid : position < prepared.state.entries.size := by rw [←sizes];exact valid
  obtain ⟨outputValid,entryEq⟩ := GeneralBorrowFreshModify.entry_exact map offset len modify
    (fun _ location => GeneralBorrowFreshInstallation.materialized_idempotent location index GeneralBorrowFreshDefaultChild.inside) well bounds position oldValid
  have rangeEq : (changed.state.entries[position]'valid).range = (prepared.state.entries[position]'oldValid).range := by
    rw [entryEq]
    split <;> rfl
  rw [rangeEq] at start stop
  obtain ⟨cursor,bounded,same⟩ := GeneralRangeMapCoverage.overlap_selected map offset len well bounds positive position oldValid start stop
  have member : position ∈ prepared.positions.toList := by
    rw [←same]
    exact Array.mem_def.mp (Array.mem_iff_getElem.mpr ⟨cursor,bounded,rfl⟩)
  rw [entryEq,if_pos member]
  exact ⟨GeneralBorrowFreshDefaultChild.inside,GeneralBorrowFreshLocation.get_same _ _ _,rfl⟩

private theorem get_map {α β : Type} (shape : α → β) (nodes : UniValMap α) (query : UniIndex) :
    (⟨nodes.data.map (Option.map shape)⟩ : UniValMap β).get query = (nodes.get query).map shape := by
  unfold UniValMap.get
  simp only [Array.getElem?_map]
  cases cell : nodes.data[query.toNat]? with
  | none => rfl
  | some entry => cases entry <;> rfl

/-- The actual SIFA shape frame preserves stored reservation permission and
range-local existence, even though it can weaken the state's SIFA field. -/
theorem shape_preserves (before after : BorrowTree) (same : GeneralBorrowView.treeShape after = GeneralBorrowView.treeShape before)
    (index : UniIndex) (lower upper : UInt64) (typed : OwnedOn (Reserved index) lower upper before.locations) :
    OwnedOn (Reserved index) lower upper after.locations := by
  have ranges := congrArg (fun row => row.2.2.1) same
  change after.locations.entries.map (fun segment => (segment.range,GeneralBorrowView.locationShape segment.data)) =
    before.locations.entries.map (fun segment => (segment.range,GeneralBorrowView.locationShape segment.data)) at ranges
  have sizes : after.locations.entries.size = before.locations.entries.size := by
    have known := congrArg Array.size ranges
    simpa only [Array.size_map] using known
  intro position valid positive lowerBound upperBound
  have oldValid : position < before.locations.entries.size := by rw [←sizes];exact valid
  have fields : (after.locations.entries[position]'valid).range = (before.locations.entries[position]'oldValid).range ∧
      GeneralBorrowView.locationShape (after.locations.entries[position]'valid).data = GeneralBorrowView.locationShape (before.locations.entries[position]'oldValid).data := by
    have known := congrArg (fun rows => rows[position]?) ranges
    simp only [Array.getElem?_map,Array.getElem?_eq_getElem valid,Array.getElem?_eq_getElem oldValid,Option.map_some] at known
    exact Prod.mk.inj (Option.some.inj known)
  rw [fields.1] at lowerBound upperBound
  obtain ⟨oldState,stored,reserved⟩ := typed position oldValid positive lowerBound upperBound
  have states := congrArg (fun rows => (⟨rows⟩ : UniValMap GeneralBorrowView.StateShape).get index) fields.2
  dsimp only [GeneralBorrowView.locationShape] at states
  rw [get_map,get_map,stored] at states
  cases present : after.locations.entries[position].data.perms.get index with
  | none => rw [present] at states;cases states
  | some state =>
    have stateEq : GeneralBorrowView.stateShape state = GeneralBorrowView.stateShape oldState := by
      simpa only [present,Option.map_some,Option.some.injEq] using states
    exact ⟨state,present,(congrArg Prod.fst stateEq).trans reserved⟩

/-- Actual Default append/reuse forms exact stored reservations everywhere on
its selected slice. Outside-slot Clean is neither needed nor asserted. -/
theorem formed (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (children : GeneralBorrowGraph.ChildNodes tree) (covered : GeneralBorrowGraph.RootsCover tree)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (parentTagPresent : tree.indexOfTag parentTag = some parent) (parentPresent : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (slot : Slot tree depth parent)
    (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) :
    OwnedOn (Reserved (GeneralBorrowFreshMetadataChildDefaultSlot.index slot)) offset (offset+len)
      (GeneralBorrowFreshMetadataChildDefaultSlot.result tree parentTag newTag offset len).locations := by
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildDefault.Input :=
      ⟨tree,depth,children,covered,parentTag,newTag,parent,parentNode,parentTagPresent,parentPresent,fresh,
        noFree,aligned,fits,offset,len,nonzero,well,bounds⟩
    exact shape_preserves _ _ (GeneralBorrowFreshMetadataChildDefault.shape input) _ _ _
      (modified tree.locations (GeneralBorrowFreshMetadataChildDefault.index input) (Size.ofBytes offset) (Size.ofBytes len) well bounds)
  | reuse index available bounded vacant slack =>
    let input : GeneralBorrowFreshMetadataChildDefaultReuse.Input :=
      ⟨tree,depth,children,covered,parentTag,newTag,parent,parentNode,parentTagPresent,parentPresent,fresh,
        index,available,bounded,vacant,slack,offset,len,nonzero,well,bounds⟩
    exact shape_preserves _ _ (GeneralBorrowFreshMetadataChildDefaultReuse.shape input) _ _ _
      (modified tree.locations index (Size.ofBytes offset) (Size.ofBytes len) well bounds)

end DuplicatePrefix.GeneralBorrowDefaultReservationSlice
