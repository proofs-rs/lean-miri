import duplicate_prefix.S02FnEntryOldLookup
import duplicate_prefix.DuplicatePrefixReferenceInput

namespace DuplicatePrefix.S02FnEntryBinding
open Miri Miri.Memory Miri.ABI Miri.DataStructures Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Every preexisting mapped tag keeps its exact source index on the typed
FnEntry tree; runtime freshness excludes collision with the new tag. -/
theorem mapped (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (frame : FrameState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowRawFnEntry.Input tree tracker.global)
    (tag : BorTag) (index : UniIndex) (tagged : tree.indexOfTag tag = some index) :
    (GeneralBorrowRawFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len).indexOfTag tag = some index := by
  obtain ⟨_,_,_,_,_,fresh⟩ := GeneralBorrowFnEntryRegistration.prepare tree tracker.global frame allocation input.tagRoom runtime
    input.parent input.selected input.maximum input.offset input.len input.positive
  have missing : tree.indexOfTag tracker.global.nextPointerTag = none := by
    simp [BorrowTree.indexOfTag,UniKeyMap.get,GeneralBorrowTagMap.fresh_find tree.tagMapping tracker.global.nextPointerTag fresh]
  have different : tracker.global.nextPointerTag ≠ tag := by
    intro same
    rw [←same,missing] at tagged
    cases tagged
  rw [S02FnEntryOldLookup.preserved tree tracker frame allocation runtime input tag different]
  exact tagged

/-- The normalized concrete/wildcard destination Binding survives the actual
source argument's tree replacement. Physical address metadata is unchanged. -/
theorem binding (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (frame : FrameState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowRawFnEntry.Input tree tracker.global)
    (addresses : AllocAddresses.GlobalAddressState) (pointer : Pointer Provenance)
    (id : AllocId) (base : UInt64) (size : Size) (source : Option UniIndex)
    (old : DuplicatePrefixReferenceInput.Binding addresses pointer id base size tree source) :
    DuplicatePrefixReferenceInput.Binding addresses pointer id base size
      (GeneralBorrowRawFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len) source := by
  cases provenance : pointer.provenance with
  | wildcard => simpa only [DuplicatePrefixReferenceInput.Binding,provenance] using old
  | concrete supplied tag =>
    simp only [DuplicatePrefixReferenceInput.Binding,provenance] at old ⊢
    obtain ⟨same,anchor,selected,tagged⟩ := old
    exact ⟨same,anchor,selected,mapped tree tracker frame allocation runtime input tag anchor tagged⟩

end DuplicatePrefix.S02FnEntryBinding

open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S02FnEntryBinding.mapped,``DuplicatePrefix.S02FnEntryBinding.binding] do
    for ax in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "unapproved axiom {ax}"
