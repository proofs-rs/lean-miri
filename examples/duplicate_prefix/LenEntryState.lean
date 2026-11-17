import duplicate_prefix.LenPositiveEntry
import duplicate_prefix.SliceCarrier
import duplicate_prefix.MemoryCopyBridge
namespace DuplicatePrefix.LenEntryState
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem contains_self (protections : ProtectedTags) (tag : BorTag) (kind : ProtectorKind) :
    (protections.insert tag kind).contains tag = true := by
  have noMatch : protections.entries.find? (fun _ => false) = none := by simp [Array.find?_eq_none]
  simp [ProtectedTags.contains,ProtectedTags.get,ProtectedTags.insert,Array.find?_push,Array.find?_filter,noMatch]

theorem registered_mask (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (tracker : MachineHooks.BorrowState) (tag : BorTag) (nextTag : tag = tags 3)
    (mask : ProtectedStages.StageMask tags tracker.global.protectedTags 3 false) :
    ProtectedStages.StageMask tags (TypedBorrowSteps.registeredGlobal tracker tag).protectedTags 4 true := by
  intro index inside
  by_cases same : index = 3
  · subst index
    simpa [TypedBorrowSteps.registeredGlobal,nextTag] using contains_self tracker.global.protectedTags (tags 3) .StrongProtector
  · have smaller : index.val < 3 := by
      have not3 : index.val ≠ 3 := fun eq => same (Fin.ext eq)
      omega
    have different : tags index ≠ tags 3 := fun eq => same (distinct eq)
    have before := mask index smaller
    change (tracker.global.protectedTags.insert tag .StrongProtector).contains (tags index) = _
    rw [nextTag,ProtectorInsertion.contains_other _ _ _ _ different]
    have beq3 : (index == 3) = false := Bool.eq_false_iff.mpr (fun eq => same (beq_iff_eq.mp eq))
    simpa [beq3] using before

theorem positive_carrier
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (tree : BorrowTree)
    (base offset len : UInt64)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat) :
    let result := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine machine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory machine.memory id entry tree}
    SliceCarrier.Valid result
      (.inl (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset)))) len := by
  apply SliceCarrier.Valid.positive id tracker.global.nextPointerTag base offset len
    {entry with allocation := entry.allocation.setExtra tree}
  · exact cached
  · exact MemoryCopyBridge.live_lookup_replaced machine.memory id {entry with allocation := entry.allocation.setExtra tree}
  · exact positive
  · exact nonzero
  · exact signedFits
  · exact bounds

open Lean Elab Command in
run_cmd do
  for declaration in [``contains_self, ``registered_mask, ``positive_carrier] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved len entry state {dependency}"
end DuplicatePrefix.LenEntryState
