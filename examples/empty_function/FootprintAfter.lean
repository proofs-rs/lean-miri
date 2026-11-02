import empty_function.OrderedIndirectProjection
import empty_function.RawResources
import empty_function.Preservation
import empty_function.ProjectionZero
import empty_function.ProjectedIndirectPreflight
namespace EmptyFunction.FootprintAfter
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.Input
open EmptyFunction.WholeCall EmptyFunction.InputDraft
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- Geometry metadata is observed before installing the selected lazy source;
its actual final address table has already been constructed. -/
def Geometry (before after : State) : Prop :=
  ∃ snapshot : State, snapshot.machine.memory = before.machine.memory ∧
    snapshot.machine.user.addresses = after.machine.user.addresses ∧ AddressTables snapshot

theorem transport (before after : State) (pointer : Pointer (Option Provenance)) (length : Size)
    (foot : IndirectFootprint before pointer length) (positive : length.bytes ≠ 0)
    (oldLive : Preservation.OriginalLiveAllocations before after)
    (kept : Preservation.ExistingAddressFacts before after) (geometry : Geometry before after) :
    Nonempty (IndirectFootprint after pointer length) := by
  obtain ⟨entry,live,kind,physical,rights⟩ := oldLive foot.id foot.entry foot.live
  have size : entry.allocation.byteSize = foot.entry.allocation.byteSize :=
    congrArg (fun allocation : Allocation Provenance Unit => allocation.byteSize) physical
  obtain ⟨snapshot,memory,addresses,tables⟩ := geometry
  refine ⟨⟨foot.id,entry,live,foot.base,foot.relative,kept.2.2.1 foot.id _ foot.cached,
    foot.address,?_,?_,?_⟩⟩
  · rw [size];exact foot.addressFits
  · rw [size];exact foot.extent
  · cases encoding : pointer.provenance with
    | none => simpa only [encoding] using foot.attribution
    | some provenance =>
      cases provenance with
      | concrete id tag => simpa only [encoding] using foot.attribution
      | wildcard =>
        obtain ⟨mode,exposed,⟨row,member,rowId,rowBase⟩,_nearest⟩ :=
          (show before.machine.user.addresses.provenanceMode ≠ .strict ∧
            before.machine.user.addresses.exposed.contains foot.id = true ∧
            (∃ row ∈ before.machine.user.addresses.intToPtrMap,row.allocId=foot.id ∧ row.address=foot.base) ∧
            (∀ row ∈ before.machine.user.addresses.intToPtrMap,row.address≤pointer.offset.bytes → row.address≤foot.base) by
            simpa only [encoding] using foot.attribution)
        obtain ⟨parent,parentMember,parentId,parentBase⟩ := kept.2.2.2.1 row member
        have parentId : parent.allocId = foot.id := parentId.trans rowId
        have parentBase : parent.address = foot.base := parentBase.trans rowBase
        change _ ∧ _ ∧ _ ∧ _
        refine ⟨?_,?_,⟨parent,parentMember,parentId,parentBase⟩,?_⟩
        · rw [kept.2.1];exact mode
        · apply Array.contains_eq_true_of_mem
          exact Array.mem_of_contains_eq_true (kept.2.2.2.2 foot.id (Array.mem_of_contains_eq_true exposed))
        · intro other otherMember belowPointer
          by_cases lower : other.address ≤ foot.base
          · exact lower
          have parentMemberS : parent ∈ snapshot.machine.user.addresses.intToPtrMap := by simpa only [addresses] using parentMember
          have otherMemberS : other ∈ snapshot.machine.user.addresses.intToPtrMap := by simpa only [addresses] using otherMember
          have different : other.allocId ≠ parent.allocId := by
            intro same
            have queryParent := tables.bases parent parentMemberS
            have queryOther := tables.bases other otherMemberS
            rw [same] at queryOther
            have addressEq : other.address = parent.address := congrArg (fun value => value.address) (Option.some.inj (queryOther.symm.trans queryParent))
            exact lower (by rw [addressEq,parentBase];exact UInt64.le_iff_toNat_le.mpr (Nat.le_refl _))
          have parentInfo : snapshot.machine.memory.getAllocInfo parent.allocId =
              .ok ⟨foot.entry.allocation.byteSize,foot.entry.allocation.align,.liveData,foot.entry.allocation.mutability⟩ := by
            rw [memory,parentId]
            simp [MemoryState.getAllocInfo,foot.live,Except.pure]
            rfl
          obtain ⟨otherInfo,otherInfoEq⟩ := RawResources.backing_info snapshot other.allocId (tables.suppliers other otherMemberS)
          have separated := tables.separated parent parentMemberS other otherMemberS (Ne.symm different) _ _ parentInfo otherInfoEq
          rw [parentBase] at separated
          have beforeEnd : pointer.offset.bytes.toNat < foot.base.toNat + foot.entry.allocation.byteSize.bytes.toNat := by
            have lenPositive : 0 < length.bytes.toNat := by
              have ne : length.bytes.toNat ≠ 0 := by intro zero;apply positive;exact UInt64.toNat_inj.mp zero
              omega
            have extent := foot.extent
            have address := foot.address
            omega
          have lowerN : foot.base.toNat < other.address.toNat := by
            exact Nat.lt_of_not_ge (by intro bad;exact lower (UInt64.le_iff_toNat_le.mpr bad))
          have bounded := UInt64.le_iff_toNat_le.mp belowPointer
          change foot.base.toNat + max foot.entry.allocation.byteSize.bytes.toNat 1 ≤ other.address.toNat ∨
            other.address.toNat + max otherInfo.size.bytes.toNat 1 ≤ foot.base.toNat at separated
          rcases separated with left | right
          · omega
          · omega

theorem offset (s : Static) (metadata : EmptyFunction.Specification.Metadata s) (before after : State)
    (place : MemPlace Provenance) (length amount : Size)
    (foot : IndirectFootprint before place.ptr length) (positive : amount.bytes ≠ 0)
    (within : amount.bytes.toNat ≤ length.bytes.toNat) (signed : length.bytes.toNat < 2^63)
    (oldLive : Preservation.OriginalLiveAllocations before after)
    (kept : Preservation.ExistingAddressFacts before after) (geometry : Geometry before after) :
    EvalProjectionMachine.memoryOffset (EmptyFunction.ConcreteProtection.source s).pointers after place amount .inbounds .none =
      .ok (EmptyFunction.ProjectedIndirectPreflight.shifted place amount) := by
  have parentPositive : length.bytes ≠ 0 := by
    intro zero
    have amountPositive : 0 < amount.bytes.toNat := by
      have ne : amount.bytes.toNat ≠ 0 := by intro z;apply positive;exact UInt64.toNat_inj.mp z
      omega
    rw [zero] at within
    simp only [UInt64.toNat_zero] at within
    omega
  obtain ⟨current⟩ := transport before after place.ptr length foot parentPositive oldLive kept geometry
  obtain ⟨snapshot,memory,addresses,tables⟩ := geometry
  apply EmptyFunction.OrderedIndirectProjection.positive s metadata after place length amount current _ positive within signed
  intro wild
  have ordered := EmptyFunction.WildcardResolution.ordered snapshot tables
  simpa only [addresses] using ordered

end EmptyFunction.FootprintAfter
