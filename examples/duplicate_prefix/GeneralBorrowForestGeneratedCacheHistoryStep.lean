import duplicate_prefix.GeneralBorrowForestGeneratedHiddenOperations
namespace DuplicatePrefix.GeneralBorrowForestGeneratedCacheHistoryStep
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestGeneratedTagHistoryData GeneralBorrowForestGeneratedHiddenCache GeneralRangeMapState GeneralRangeMapOrigins
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

structure Formed (state : Snapshot) : Prop where
  sifa : GeneralBorrowForestGeneratedSifaHistory.Formed state
  empty : Empty state.tree

/-- Cache coherence is absent from these raw protected-Read data: the actual
allocation/constructor/Read/release/GC history derives it internally. -/
structure ReadData (state : Snapshot) (tag : BorTag) (offset len : Size) where
  anchor : UniIndex
  node : TreeNode
  root : UniIndex
  tagged : state.tree.indexOfTag tag=some anchor
  present : state.tree.nodeAt anchor=some node
  roots : state.tree.roots=#[root]
  lower : UInt64
  upper : UInt64
  readable : OwnedOn (GeneralBorrowProtectedReadInvariantLocation.Data state.tree state.global.protectedTags) lower upper state.tree.locations
  requestLower : lower.toNat≤offset.bytes.toNat
  requestUpper : (offset.bytes+len.bytes).toNat≤upper.toNat

def ReadData.checked (state : Snapshot) (formed : Formed state) (tag : BorTag) (offset len : Size) (data : ReadData state tag offset len) :
    GeneralBorrowForestGeneratedProtectedReadStep.ReadData state tag offset len :=
  ⟨data.anchor,data.node,data.root,data.tagged,data.present,data.roots,coherent _ _ formed.empty,data.lower,data.upper,data.readable,data.requestLower,data.requestUpper⟩

def Applicable (state : Snapshot) (event : Event) : Prop :=
  GeneralBorrowForestGeneratedReadReleaseData.Applicable state event ∨
  (GeneralBorrowForestGeneratedTagHistoryData.Applicable state event ∧ match event with
  | .access (.concrete tag) offset len .Read _ => Nonempty (ReadData state tag offset len)
  | _ => False)

theorem base (state : Snapshot) (event : Event) (allowed : Applicable state event) :
    GeneralBorrowForestGeneratedTagHistoryData.Applicable state event := by
  rcases allowed with old|extra
  · exact old.1
  · exact extra.1

private theorem constructor_empty (id : AllocId) (state : Snapshot) (formed : Formed state)
    (parent : ProvenanceExtra) (base : Size) (inside : DedupRangeMap LocationState) (outside : Permission) (held : Bool)
    (allowed : GeneralBorrowForestGeneratedTagHistoryData.Applicable state (.constructor parent base inside outside held)) :
    Empty (step id state (.constructor parent base inside outside held)).state.tree := by
  obtain ⟨room,nodeRoom,parentData,initialOutside,notUnique,⟨sifa,foreign⟩,bounded,insideInitial⟩ := allowed
  have flags := GeneralBorrowForestGeneratedTagHistoryFlags.generated id state formed.sifa.generated room held
  have fresh := GeneralBorrowForestGeneratedTagHistoryData.fresh state formed.sifa.generated
  have actual : Empty (state.tree.newChild base parent state.global.nextPointerTag inside outside held).tree := by
    cases parent with
    | wildcard => exact GeneralBorrowForestGeneratedHiddenWildcard.profile state.tree formed.sifa.generated.structural formed.empty state.global.nextPointerTag fresh nodeRoom outside sifa held initialOutside notUnique foreign base inside bounded
    | concrete parentTag =>
      obtain ⟨parent,node,tagged,present⟩ := parentData
      exact GeneralBorrowForestGeneratedHiddenConcrete.profile state.tree formed.sifa.generated.structural formed.empty parentTag parent node tagged present state.global.nextPointerTag fresh nodeRoom outside sifa held initialOutside notUnique foreign base inside bounded
  simpa only[step,flags.1] using actual

private theorem old_empty (id : AllocId) (state : Snapshot) (formed : Formed state) (event : Event)
    (allowed : GeneralBorrowForestGeneratedReadReleaseData.Applicable state event) : Empty (step id state event).state.tree := by
  cases event with
  | allocate => simpa only[step,TypedRetagEmpty.allocate_tag state.global allowed.1] using formed.empty
  | constructor parent base inside outside held => exact constructor_empty id state formed parent base inside outside held allowed.1
  | gc live => exact GeneralBorrowForestGeneratedHiddenOperations.collect state.tree formed.sifa.generated.structural formed.empty live
  | release => obtain ⟨data⟩ := allowed.2;exact GeneralBorrowForestGeneratedHiddenOperations.release id state formed.sifa formed.empty data
  | access source offset len kind mode =>
    cases source with
    | wildcard => exact False.elim allowed.2
    | concrete tag =>
      cases kind with
      | Write => exact False.elim allowed.2
      | Read => obtain ⟨data⟩ := allowed.2;exact GeneralBorrowForestGeneratedHiddenOperations.owned_read id state formed.sifa formed.empty tag offset len mode allowed.1 data

private theorem read_empty (id : AllocId) (state : Snapshot) (formed : Formed state) (tag : BorTag) (offset len : Size) (mode : ChildrenVisitMode)
    (bounds : offset.bytes.toNat+len.bytes.toNat≤state.tree.locations.size.bytes.toNat) (data : ReadData state tag offset len) :
    Empty (step id state (.access (.concrete tag) offset len .Read mode)).state.tree := by
  obtain ⟨depth⟩ := formed.sifa.generated.structural.depth
  have owned : OwnedOn (GeneralBorrowProtectedReadRelease.Profile state.tree state.global.protectedTags) data.lower data.upper state.tree.locations := by
    intro position valid positive before after
    exact ⟨formed.sifa.generated.structural.forest _ _,data.readable position valid positive before after⟩
  have actual := GeneralBorrowProtectedReadRangeExposureCache.ranged state.tree state.global.protectedTags tag data.anchor data.root offset len mode depth
    formed.sifa.generated.structural.children data.node data.present data.roots formed.sifa.generated.structural.covered data.tagged
    formed.sifa.generated.structural.well (coherent _ _ formed.empty) data.lower data.upper owned data.requestLower data.requestUpper bounds
  have hidden : Hidden (state.tree.performNormalAccessRange tag offset len .Read state.global.protectedTags mode).tree := by
    intro index node present
    change (state.tree.performNormalAccessRange tag offset len .Read state.global.protectedTags mode).tree.nodes.get index=some node at present
    rw[actual.2.2.2.2.1] at present
    exact formed.empty.hidden index node present
  exact zero_of_coherent _ state.global.protectedTags hidden actual.2.1

theorem preserves (id : AllocId) (state : Snapshot) (formed : Formed state) (event : Event) (allowed : Applicable state event) :
    (step id state event).completed=true ∧ Formed (step id state event).state := by
  rcases allowed with old|extra
  · exact ⟨GeneralBorrowForestGeneratedReadReleaseHistory.step_completed id state formed.sifa event old,
      GeneralBorrowForestGeneratedReadReleaseStep.formed id state formed.sifa event old,old_empty id state formed event old⟩
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
        | Write => exact False.elim extra.2
        | Read =>
          obtain ⟨data⟩ := extra.2
          have good := GeneralBorrowForestGeneratedProtectedReadStep.read id state formed.sifa tag offset len mode extra.1 (ReadData.checked state formed tag offset len data)
          exact ⟨good.1,good.2,read_empty id state formed tag offset len mode extra.1 data⟩
end DuplicatePrefix.GeneralBorrowForestGeneratedCacheHistoryStep
