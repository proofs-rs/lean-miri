import empty_function.WildcardResolution
namespace EmptyFunction.OrderedWildcardFootprint
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
open EmptyFunction.WholeCall EmptyFunction.InputDraft EmptyFunction.WildcardSearch
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

theorem selected (before : State) (pointer : Pointer (Option Provenance)) (length : Size)
    (foot : IndirectFootprint before pointer length) (positive : length.bytes ≠ 0)
    (wild : pointer.provenance = some .wildcard) (ordered : Ordered before.machine.user.addresses.intToPtrMap) :
    before.machine.user.addresses.allocIdFromAddr pointer.offset.bytes 0 (WildcardResolution.lookup before) =
      .ok (some foot.id) := by
  obtain ⟨mode,exposed,⟨row,member,rowId,rowBase⟩,nearest⟩ :=
    (show before.machine.user.addresses.provenanceMode ≠ .strict ∧
      before.machine.user.addresses.exposed.contains foot.id = true ∧
      (∃ row ∈ before.machine.user.addresses.intToPtrMap, row.allocId = foot.id ∧ row.address = foot.base) ∧
      (∀ row ∈ before.machine.user.addresses.intToPtrMap,
        row.address ≤ pointer.offset.bytes → row.address ≤ foot.base) by simpa only [wild] using foot.attribution)
  obtain ⟨position,valid,actual⟩ := Array.mem_iff_getElem.mp member
  have shape : row = ⟨foot.base,foot.id⟩ := by
    cases row with
    | mk address id => simp only at rowId rowBase;cases rowId;cases rowBase;rfl
  have atRow : before.machine.user.addresses.intToPtrMap[position]? = some ⟨foot.base,foot.id⟩ :=
    (Array.getElem?_eq_getElem valid).trans (congrArg some (actual.trans shape))
  have atAddress : before.machine.user.addresses.intToPtrMap[position].address = foot.base := by
    rw [actual,shape]
  have info : before.machine.memory.getAllocInfo foot.id =
      .ok ⟨foot.entry.allocation.byteSize,foot.entry.allocation.align,.liveData,foot.entry.allocation.mutability⟩ := by
    simp [MemoryState.getAllocInfo,foot.live,Except.pure]
    rfl
  have size : (WildcardResolution.lookup before).sizeOf foot.id = some foot.entry.allocation.byteSize := by
    simp only [WildcardResolution.lookup,info,Except.toOption,Option.map_some]
  have live : (WildcardResolution.lookup before).isLive foot.id = some true := by
    have present : before.machine.memory.live.any (fun entry => entry.1 == foot.id) = true :=
      Array.any_eq_true'.mpr ⟨(foot.id,foot.entry),Array.mem_of_find?_eq_some foot.live,by simp⟩
    simp only [WildcardResolution.lookup,MemoryState.isAllocLive,present,Bool.true_or]
  have lower : foot.base ≤ pointer.offset.bytes := UInt64.le_iff_toNat_le.mpr (by have h := foot.address;omega)
  have inside : pointer.offset.bytes-foot.base < foot.entry.allocation.byteSize.bytes := by
    apply UInt64.lt_iff_toNat_lt.mpr
    rw [UInt64.toNat_sub_of_le _ _ lower]
    have extent := foot.extent
    have address := foot.address
    have pos : 0 < length.bytes.toNat := by
      have : length.bytes.toNat ≠ 0 := by intro zero;apply positive;exact UInt64.toNat_inj.mp zero
      omega
    omega
  by_cases base : pointer.offset.bytes = foot.base
  · have search := inverse_hit before.machine.user.addresses.intToPtrMap foot.base foot.id position valid ordered atRow
    rw [base]
    exact GlobalAddressState.allocation_base_zero before.machine.user.addresses foot.base foot.id
      (WildcardResolution.lookup before) position mode search atRow exposed live
  · have afterBase : foot.base < pointer.offset.bytes := UInt64.lt_iff_toNat_lt.mpr (by
      have le := UInt64.le_iff_toNat_le.mp lower
      have ne : pointer.offset.bytes.toNat ≠ foot.base.toNat := by intro eq;exact base (UInt64.toNat_inj.mp eq)
      omega)
    have geometry : Cut before.machine.user.addresses.intToPtrMap pointer.offset.bytes (position+1) := by
      refine ⟨by omega,?_,?_⟩
      · intro i bounded beforeCut
        by_cases same : i = position
        · subst i;rw [atAddress];exact afterBase
        · have earlier := ordered i position (by omega) valid
          rw [atAddress] at earlier
          apply UInt64.lt_iff_toNat_lt.mpr
          have a := UInt64.lt_iff_toNat_lt.mp earlier
          have b := UInt64.lt_iff_toNat_lt.mp afterBase
          omega
      · intro i bounded afterCut
        have later := ordered position i (by omega) bounded
        rw [atAddress] at later
        apply UInt64.lt_iff_toNat_lt.mpr
        apply Nat.lt_of_not_ge
        intro outside
        have below : before.machine.user.addresses.intToPtrMap[i].address ≤ pointer.offset.bytes :=
          UInt64.le_iff_toNat_le.mpr (by omega)
        have restricted := nearest before.machine.user.addresses.intToPtrMap[i]
          (Array.getElem_mem bounded) below
        have strict := UInt64.lt_iff_toNat_lt.mp later
        have le := UInt64.le_iff_toNat_le.mp restricted
        omega
    have different : ∀ row ∈ before.machine.user.addresses.intToPtrMap, row.address ≠ pointer.offset.bytes := by
      intro other member same
      obtain ⟨i,bounded,atElement⟩ := Array.mem_iff_getElem.mp member
      by_cases beforeCut : i < position+1
      · have below := geometry.2.1 i bounded beforeCut
        rw [atElement,same] at below
        exact (UInt64.lt_irrefl _ below)
      · have above := geometry.2.2 i bounded (by omega)
        rw [atElement,same] at above
        exact (UInt64.lt_irrefl _ above)
    obtain ⟨cut,search,partition⟩ := inverse_cut before.machine.user.addresses.intToPtrMap pointer.offset.bytes ordered different
    have equalCut : cut = position+1 := by
      rcases Nat.lt_trichotomy cut (position+1) with earlier | same | later
      · have bounded : cut < before.machine.user.addresses.intToPtrMap.size := by have h := geometry.1;omega
        have a := UInt64.lt_iff_toNat_lt.mp (geometry.2.1 cut bounded earlier)
        have b := UInt64.lt_iff_toNat_lt.mp (partition.2.2 cut bounded (Nat.le_refl _))
        omega
      · exact same
      · have bounded : position+1 < before.machine.user.addresses.intToPtrMap.size := by have h := partition.1;omega
        have a := UInt64.lt_iff_toNat_lt.mp (partition.2.1 (position+1) bounded later)
        have b := UInt64.lt_iff_toNat_lt.mp (geometry.2.2 (position+1) bounded (Nat.le_refl _))
        omega
    rw [equalCut] at search
    exact GlobalAddressState.allocation_interior_zero before.machine.user.addresses pointer.offset.bytes foot.base foot.id
      (WildcardResolution.lookup before) foot.entry.allocation.byteSize position mode search atRow size inside exposed live

theorem nonnegative_query (state : GlobalAddressState) (address : UInt64) (count : Int64)
    (hooks : AddressLookupHooks) (nonnegative : 0 ≤ count.toInt) :
    state.allocIdFromAddr address count hooks = state.allocIdFromAddr address 0 hooks := by
  unfold GlobalAddressState.allocIdFromAddr
  simp only [show ¬ count.toInt < 0 from by omega,show Int64.toInt 0 = (0 : Int) from rfl,
    show ¬ (0 : Int) < 0 from by omega,↓reduceIte]

theorem pointer (before : State) (place : Pointer (Option Provenance)) (length : Size)
    (foot : IndirectFootprint before place length) (positive : length.bytes ≠ 0)
    (provenance : Provenance) (encoding : place.provenance = some provenance)
    (tables : place.provenance = some .wildcard → Ordered before.machine.user.addresses.intToPtrMap) (arithmetic : PointerArithmetic)
    (truncate : ∀ value, arithmetic.truncateToTargetUsize value = .ok value)
    (count : Int64) (nonnegative : 0 ≤ count.toInt) :
    before.machine.user.addresses.ptrGetAlloc (Pointer.new provenance place.offset) count
      (WildcardResolution.lookup before) arithmetic = .ok (some (foot.id,Size.ofBytes foot.relative)) := by
  have lower : foot.base ≤ place.offset.bytes := UInt64.le_iff_toNat_le.mpr (by have h := foot.address;omega)
  have relative : place.offset.bytes-foot.base = foot.relative := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_sub_of_le _ _ lower]
    have h := foot.address
    omega
  have chosen : (match provenance with
      | .concrete id _ => (Except.ok (some id) : Except AddressStateError (Option AllocId))
      | .wildcard => before.machine.user.addresses.allocIdFromAddr place.offset.bytes count (WildcardResolution.lookup before)) =
      .ok (some foot.id) := by
    cases provenance with
    | concrete supplied tag =>
      have same : supplied = foot.id := by simpa only [encoding] using foot.attribution
      simp only [same]
    | wildcard =>
      rw [nonnegative_query _ _ _ _ nonnegative]
      exact selected before place length foot positive encoding (tables encoding)
  apply GlobalAddressState.pointer_from_selection before.machine.user.addresses (Pointer.new provenance place.offset)
    count (WildcardResolution.lookup before) arithmetic foot.id foot.base foot.relative chosen foot.cached
  simpa only [Pointer.new,relative] using truncate foot.relative

end EmptyFunction.OrderedWildcardFootprint
