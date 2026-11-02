import duplicate_prefix.GeneralBorrowForestDefaultReserved
import duplicate_prefix.GeneralBorrowForestMutableUnique
import duplicate_prefix.GeneralBorrowForestForeignSliceRepeated

namespace DuplicatePrefix.GeneralBorrowForestDefaultActivation
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open GeneralBorrowForestMutableAccess (Data)
open GeneralBorrowForestAccessData (Context)
open GeneralBorrowFreshReborrowStages (Slot)
open GeneralBorrowForestDefault (read child)
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def reserved (tree : BorrowTree) (protections : ProtectedTags) (parentTag newTag : BorTag)
    (offset len : UInt64) (mode : ChildrenVisitMode) := (child tree protections parentTag newTag offset len mode).tree

def write (tree : BorrowTree) (protections : ProtectedTags) (parentTag newTag : BorTag)
    (offset len : UInt64) (readMode writeMode : ChildrenVisitMode) :=
  (reserved tree protections parentTag newTag offset len readMode).performBorrowAccessRange
    (.concrete newTag) (Size.ofBytes offset) (Size.ofBytes len) .Write protections writeMode

/-- Actual parent Read, actual Default mutable reservation, then actual child
Write on a general multiple-root forest. Each operation completes and the child
retains ALL mutable next-input data. Every exact per-location callback selected
by the actual ranged Write establishes stored Unique; its initial non-Cell
state follows from real inside-slice materialization, without global Clean.
This is not yet a MIR invocation or a final-array Unique lookup theorem. -/
theorem activate (tree : BorrowTree) (protections : ProtectedTags) (parentTag newTag : BorTag)
    (parent primary : UniIndex) (extras : List UniIndex) (offset len : UInt64)
    (readMode writeMode : ChildrenVisitMode)
    (context : Context tree parent primary extras) (covered : GeneralBorrowGraph.RootsCover tree)
    (parentTagPresent : tree.indexOfTag parentTag = some parent)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (slot : Slot tree context.depth parent)
    (fits : tree.nodes.data.size ≤ 4294967296) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (before : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (Data tree location protections parent primary extras))
      offset (offset+len) tree.locations) :
    (read tree protections parentTag offset len readMode).status = .Completed ∧
    (child tree protections parentTag newTag offset len readMode).outcome = .ok () ∧
    (write tree protections parentTag newTag offset len readMode writeMode).status = .Completed ∧
    Nonempty (Context (write tree protections parentTag newTag offset len readMode writeMode).tree
      (GeneralBorrowFreshMetadataChildDefaultSlot.index slot) primary extras) ∧
    GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (Data (write tree protections parentTag newTag offset len readMode writeMode).tree
        location protections (GeneralBorrowFreshMetadataChildDefaultSlot.index slot) primary extras))
      offset (offset+len) (write tree protections parentTag newTag offset len readMode writeMode).tree.locations ∧
    (write tree protections parentTag newTag offset len readMode writeMode).tree.locations.WellFormed ∧
    (write tree protections parentTag newTag offset len readMode writeMode).tree.locations.size = tree.locations.size ∧
    let initial := reserved tree protections parentTag newTag offset len readMode
    let prepared := initial.locations.iterMut (Size.ofBytes offset) (Size.ofBytes len)
    ∀ cursor (valid : cursor < prepared.segments.size), ∃ state,
      (source_access_location (source_tree_access_at initial prepared.segments[cursor].data
        (some (GeneralBorrowFreshMetadataChildDefaultSlot.index slot)) .Write protections writeMode prepared.segments[cursor].range)).perms.get
          (GeneralBorrowFreshMetadataChildDefaultSlot.index slot) = some state ∧ state.permission = .Unique := by
  have constructed := GeneralBorrowForestDefault.run tree protections parentTag newTag parent primary extras offset len readMode
    context covered parentTagPresent fresh slot fits nonzero well bounds before
  obtain ⟨childContext⟩ := constructed.2.2.1
  have typed := GeneralBorrowForestDefaultReserved.formed tree protections parentTag newTag parent primary extras offset len readMode
    context covered parentTagPresent fresh slot fits nonzero well bounds before
  let initial := reserved tree protections parentTag newTag offset len readMode
  let index := GeneralBorrowFreshMetadataChildDefaultSlot.index slot
  have initialWell : initial.locations.WellFormed := constructed.2.2.2.2.2.1
  have initialCapacity : initial.locations.size = tree.locations.size := constructed.2.2.2.2.2.2.1
  have initialFits : initial.nodes.data.size ≤ 4294967296 := constructed.2.2.2.2.2.2.2.1
  have initialTag : initial.indexOfTag newTag = some index := constructed.2.2.2.2.1
  have initialOwners : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (Data initial location protections index primary extras)) offset (offset+len) initial.locations := constructed.2.2.2.1
  have initialBounds : offset.toNat+len.toNat ≤ initial.locations.size.bytes.toNat := by rw [initialCapacity];exact bounds
  have activated := GeneralBorrowForestMutableSlice.access initial protections newTag index primary extras (Size.ofBytes offset) (Size.ofBytes len) .Write writeMode
    childContext initialTag initialWell initialFits offset (offset+len) initialOwners initialBounds (Nat.le_refl _) (Nat.le_refl _)
  let final := write tree protections parentTag newTag offset len readMode writeMode
  change final.status = .Completed ∧ GeneralRangeMapOrigins.OwnedOn
    (fun location => Nonempty (Data final.tree location protections index primary extras)) offset (offset+len) final.tree.locations ∧
    final.tree.locations.WellFormed ∧ final.tree.locations.size = initial.locations.size at activated
  have nextContext : Nonempty (Context final.tree index primary extras) := by
    have frame := GeneralBorrowFreshReadFrame.frame initial (.concrete newTag) (Size.ofBytes offset) (Size.ofBytes len) .Write protections writeMode
    change final.tree = {initial with locations := final.tree.locations} at frame
    rw [frame]
    exact ⟨GeneralBorrowForestForeignSliceRepeated.context_on_map initial _ index primary extras childContext⟩
  refine ⟨constructed.1,constructed.2.1,activated.1,nextContext,activated.2.1,activated.2.2.1,
    activated.2.2.2.trans initialCapacity,?_⟩
  let predicate := fun location => Nonempty (Data initial location protections index primary extras) ∧
    GeneralBorrowDefaultReservationSlice.Reserved index location
  have all : GeneralRangeMapOrigins.OwnedOn predicate offset (offset+len) initial.locations := by
    intro position valid positive lower upper
    exact ⟨initialOwners position valid positive lower upper,typed position valid positive lower upper⟩
  have selected := GeneralRangeMapOriginPrepare.selected_owned_on initial.locations (Size.ofBytes offset) (Size.ofBytes len)
    initialWell initialBounds predicate offset (offset+len) all (Nat.le_refl _) (Nat.le_refl _)
  dsimp only
  intro cursor valid
  obtain ⟨⟨data⟩,oldState,stored,reservedPermission⟩ := selected.2.2 cursor valid
  have notCell : ∀ state, (source_normal_projection initial
      ((initial.locations.iterMut (Size.ofBytes offset) (Size.ofBytes len)).segments[cursor]'valid).data protections).stateAt index.toNat = some state →
      state.permission ≠ .Cell := by
    intro state found
    rw [projection_state initial _ protections index.toNat index childContext.anchorNode (index_self index) rfl childContext.anchorPresent] at found
    rw [stored,Option.getD_some] at found
    have equal : oldState = state := Option.some.inj found
    rw [←equal,reservedPermission]
    decide
  exact (GeneralBorrowForestMutableUnique.access initial _ protections index primary extras writeMode _ childContext data initialFits notCell).2

end DuplicatePrefix.GeneralBorrowForestDefaultActivation
