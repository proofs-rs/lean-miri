import duplicate_prefix.GeneralBorrowForestGeneratedCacheHistory
namespace DuplicatePrefix.GeneralBorrowForestGeneratedWriteStep
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestGeneratedTagHistoryData GeneralBorrowForestGeneratedHiddenCache GeneralRangeMapState GeneralRangeMapOrigins
open GeneralBorrowForestGeneratedCacheHistoryStep (Formed)
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- Current raw Write ownership and bounds. This admits mutable activation;
no universal Readable predicate or operation-success certificate is required. -/
structure WriteData (state : Snapshot) (tag : BorTag) (offset len : Size) where
  anchor : UniIndex
  node : TreeNode
  root : UniIndex
  tagged : state.tree.indexOfTag tag=some anchor
  present : state.tree.nodeAt anchor=some node
  roots : state.tree.roots=#[root]
  lower : UInt64
  upper : UInt64
  owned : OwnedOn (GeneralBorrowRange.LocationOwned state.tree state.global.protectedTags anchor .Write) lower upper state.tree.locations
  requestLower : lower.toNat≤offset.bytes.toNat
  requestUpper : (offset.bytes+len.bytes).toNat≤upper.toNat

def Applicable (state : Snapshot) (event : Event) : Prop :=
  GeneralBorrowForestGeneratedCacheHistoryStep.Applicable state event ∨
  (GeneralBorrowForestGeneratedTagHistoryData.Applicable state event ∧ match event with
  | .access (.concrete tag) offset len .Write _ => Nonempty (WriteData state tag offset len)
  | _ => False)

theorem base (state : Snapshot) (event : Event) (allowed : Applicable state event) :
    GeneralBorrowForestGeneratedTagHistoryData.Applicable state event := by
  rcases allowed with old|extra
  · exact GeneralBorrowForestGeneratedCacheHistoryStep.base state event old
  · exact extra.1

/-- Actual ranged Write can change permission/accessed bits, but derives
completion, physical SIFA and exact hidden-cache formation internally.
Activity is handled by the full-allocation envelope in the history theorem;
this theorem does not keep an earlier strict birth window or Readable class. -/
theorem write (id : AllocId) (state : Snapshot) (formed : Formed state)
    (tag : BorTag) (offset len : Size) (mode : ChildrenVisitMode)
    (bounds : offset.bytes.toNat+len.bytes.toNat≤state.tree.locations.size.bytes.toNat)
    (data : WriteData state tag offset len) :
    (step id state (.access (.concrete tag) offset len .Write mode)).completed=true ∧
      Formed (step id state (.access (.concrete tag) offset len .Write mode)).state := by
  obtain ⟨depth⟩ := formed.sifa.generated.structural.depth
  have physical := GeneralBorrowRangeSifaConsistency.ranged state.tree state.global.protectedTags tag data.anchor data.root offset len .Write mode
    formed.sifa.generated.structural.fits depth formed.sifa.generated.structural.children data.node data.present data.roots formed.sifa.generated.structural.covered
    data.tagged formed.sifa.generated.structural.well formed.sifa.profile data.lower data.upper data.owned data.requestLower data.requestUpper bounds
  have cached := GeneralBorrowNormalRangeExposureCache.ranged state.tree state.global.protectedTags tag data.anchor data.root offset len .Write mode
    depth formed.sifa.generated.structural.children data.node data.present data.roots formed.sifa.generated.structural.covered data.tagged
    formed.sifa.generated.structural.well (coherent _ _ formed.empty) data.lower data.upper data.owned data.requestLower data.requestUpper bounds
  have hidden : Hidden (state.tree.performNormalAccessRange tag offset len .Write state.global.protectedTags mode).tree := by
    intro index node present
    change (state.tree.performNormalAccessRange tag offset len .Write state.global.protectedTags mode).tree.nodes.get index=some node at present
    rw[cached.2.2.2.2.1] at present
    exact formed.empty.hidden index node present
  have empty := zero_of_coherent _ state.global.protectedTags hidden cached.2.1
  have status : (state.tree.performBorrowAccessRange (.concrete tag) offset len .Write state.global.protectedTags mode).status=.Completed := physical.1
  have generated := (GeneralBorrowForestGeneratedTagHistoryStep.preserves id state formed.sifa.generated (.access (.concrete tag) offset len .Write mode) bounds).1
  refine ⟨?_,⟨generated,physical.2.1⟩,empty⟩
  simp only [step,status,beq_self_eq_true]

theorem preserves (id : AllocId) (state : Snapshot) (formed : Formed state) (event : Event) (allowed : Applicable state event) :
    (step id state event).completed=true ∧ Formed (step id state event).state := by
  rcases allowed with old|extra
  · exact GeneralBorrowForestGeneratedCacheHistoryStep.preserves id state formed event old
  · cases event with
    | allocate => exact False.elim extra.2
    | constructor parent base inside outside held => exact False.elim extra.2
    | gc live => exact False.elim extra.2
    | release => exact False.elim extra.2
    | access source offset len kind mode =>
      cases source with
      | wildcard => exact False.elim extra.2
      | concrete tag =>
        cases kind with
        | Read => exact False.elim extra.2
        | Write => obtain ⟨data⟩ := extra.2;exact write id state formed tag offset len mode extra.1 data
end DuplicatePrefix.GeneralBorrowForestGeneratedWriteStep
