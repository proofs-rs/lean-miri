import duplicate_prefix.GeneralBorrowForestDefaultActivation
import duplicate_prefix.GeneralBorrowRangeCallbackOutput

namespace DuplicatePrefix.GeneralBorrowForestDefaultUnique
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess
open GeneralBorrowForestMutableAccess (Data)
open GeneralBorrowForestAccessData (Context)
open GeneralBorrowFreshReborrowStages (Slot)
open GeneralBorrowForestDefault (read child)
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Exact FINAL-array Unique formation after the REAL parent Read, Default
reservation and child ranged Write, including all actual extra-root visits.
The requested slice's final stored entries all contain a Unique child state.
Only initial mutable/foreign/cache/allocator data is supplied; no successful
operation, intermediate reservation typing or final permission is assumed. -/
theorem final_unique (tree : BorrowTree) (protections : ProtectedTags) (parentTag newTag : BorTag)
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
    GeneralRangeMapOrigins.OwnedOn
      (fun location => ∃ state, location.perms.get (GeneralBorrowFreshMetadataChildDefaultSlot.index slot) = some state ∧ state.permission = .Unique)
      offset (offset+len) (GeneralBorrowForestDefaultActivation.write tree protections parentTag newTag offset len readMode writeMode).tree.locations := by
  have activated := GeneralBorrowForestDefaultActivation.activate tree protections parentTag newTag parent primary extras offset len readMode writeMode
    context covered parentTagPresent fresh slot fits nonzero well bounds before
  have constructed := GeneralBorrowForestDefault.run tree protections parentTag newTag parent primary extras offset len readMode
    context covered parentTagPresent fresh slot fits nonzero well bounds before
  obtain ⟨childContext⟩ := constructed.2.2.1
  let initial := GeneralBorrowForestDefaultActivation.reserved tree protections parentTag newTag offset len readMode
  let index := GeneralBorrowFreshMetadataChildDefaultSlot.index slot
  have initialWell : initial.locations.WellFormed := constructed.2.2.2.2.2.1
  have initialCapacity : initial.locations.size = tree.locations.size := constructed.2.2.2.2.2.2.1
  have initialFits : initial.nodes.data.size ≤ 4294967296 := constructed.2.2.2.2.2.2.2.1
  have initialTag : initial.indexOfTag newTag = some index := constructed.2.2.2.2.1
  have initialOwners : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (Data initial location protections index primary extras)) offset (offset+len) initial.locations := constructed.2.2.2.1
  have initialBounds : offset.toNat+len.toNat ≤ initial.locations.size.bytes.toNat := by rw [initialCapacity];exact bounds
  have selected := GeneralRangeMapOriginPrepare.selected_owned_on initial.locations (Size.ofBytes offset) (Size.ofBytes len)
    initialWell initialBounds (fun location => Nonempty (Data initial location protections index primary extras))
    offset (offset+len) initialOwners (Nat.le_refl _) (Nat.le_refl _)
  change GeneralRangeMapOrigins.OwnedOn
    (fun location => ∃ state, location.perms.get index = some state ∧ state.permission = .Unique)
    offset (offset+len) (initial.performBorrowAccessRange (.concrete newTag) (Size.ofBytes offset) (Size.ofBytes len) .Write protections writeMode).tree.locations
  apply GeneralBorrowRangeCallbackOutput.outputs initial protections newTag index (Size.ofBytes offset) (Size.ofBytes len)
    .Write writeMode (fun location => ∃ state, location.perms.get index = some state ∧ state.permission = .Unique)
    initialTag initialWell initialBounds
  intro cursor valid
  obtain ⟨data⟩ := selected.2.2 cursor valid
  have localGood := GeneralBorrowForestMutableAccess.access initial _ protections index primary extras .Write writeMode
    ((initial.locations.iterMut (Size.ofBytes offset) (Size.ofBytes len)).segments[cursor]'valid).range childContext data initialFits
  exact ⟨localGood.1,activated.2.2.2.2.2.2.2 cursor valid⟩

end DuplicatePrefix.GeneralBorrowForestDefaultUnique
