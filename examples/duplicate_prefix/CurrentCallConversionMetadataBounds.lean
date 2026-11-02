import duplicate_prefix.CurrentCallConversionTargetAdequacy
import duplicate_prefix.GlobalAddressAlignedBumpFormation

namespace DuplicatePrefix.CurrentCallConversionMetadataBounds
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open Miri.Memory.AllocAddresses
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallOrdinaryInput
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

private theorem member_max (values : List Nat) (n : Nat) (member : n∈values) : n≤values.foldr max 1 := by
  induction values with
  | nil => simp at member
  | cons a rest ih =>
    rcases List.mem_cons.mp member with equal | member
    · subst n;exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih member) (Nat.le_max_right _ _)

private theorem one_max (values : List Nat) : 1≤values.foldr max 1 := by
  induction values with
  | nil => exact Nat.le_refl _
  | cons a rest ih => exact Nat.le_trans ih (Nat.le_max_right _ _)

private theorem local_size {before : Before} {id : AllocId} {entry : LocalAllocation Provenance BorrowTree MiriMemoryKind}
    (present : before.memory.live.find? (fun row=>row.1==id)=some (id,entry)) :
    entry.allocation.byteSize.bytes.toNat≤maximumMetadataSize before := by
  apply member_max
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨(id,entry),Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some present),rfl⟩

private theorem local_alignment {before : Before} {id : AllocId} {entry : LocalAllocation Provenance BorrowTree MiriMemoryKind}
    (present : before.memory.live.find? (fun row=>row.1==id)=some (id,entry)) :
    2^entry.allocation.align.pow2≤maximumMetadataAlignment before := by
  apply member_max
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨(id,entry),Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some present),rfl⟩

private theorem global_size {before : Before} {id : AllocId} {entry : GlobalAllocation}
    (present : before.memory.findGlobal? id=some entry) : entry.size.bytes.toNat≤maximumMetadataSize before := by
  apply member_max
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨entry,CurrentCallConversionTargetAdequacy.global_member present,rfl⟩

private theorem global_alignment {before : Before} {id : AllocId} {entry : GlobalAllocation}
    (present : before.memory.findGlobal? id=some entry) : 2^entry.align.pow2≤maximumMetadataAlignment before := by
  apply member_max
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨entry,CurrentCallConversionTargetAdequacy.global_member present,rfl⟩

/-- Every nondead supplier branch uses actual CURRENT metadata. Function and
va-list precedence is preserved; their zero-size/unit-alignment cases are
bounded by the same conservative maxima. -/
theorem queried {before : Before} {id : AllocId} (supplier : GlobalAddressLiveErrorExclusion.Supplier before.memory id)
    (info : AllocationInfo) (actual : before.memory.getAllocInfo id=.ok info) :
    info.size.bytes.toNat≤maximumMetadataSize before ∧2^info.align.pow2≤maximumMetadataAlignment before := by
  have one : 1≤maximumMetadataAlignment before:=one_max _
  cases supplier with
  | localRow entry present =>
    simp only [MemoryState.getAllocInfo,present] at actual
    cases Except.ok.inj actual
    exact ⟨local_size present,local_alignment present⟩
  | functionRow absent present =>
    simp only [MemoryState.getAllocInfo,absent,present,↓reduceIte] at actual
    cases Except.ok.inj actual
    exact ⟨Nat.zero_le _,one⟩
  | vaListRow absent noFunction present =>
    unfold MemoryState.hasVaListId at present
    simp only [MemoryState.getAllocInfo,absent,noFunction,present,Bool.false_eq_true,↓reduceIte] at actual
    cases Except.ok.inj actual
    exact ⟨Nat.zero_le _,one⟩
  | globalRow descriptor absent noFunction noVaList present =>
    unfold MemoryState.hasVaListId at noVaList
    simp only [MemoryState.getAllocInfo,absent,noFunction,noVaList,present,Bool.false_eq_true,↓reduceIte] at actual
    have size:=global_size present
    have alignment:=global_alignment present
    cases kind : descriptor.kind <;> simp only [kind] at actual <;> cases Except.ok.inj actual
    all_goals first | exact ⟨size,alignment⟩ | exact ⟨Nat.zero_le _,alignment⟩ | exact ⟨Nat.zero_le _,one⟩

/-- Metadata existence and bounds are derived from the declarative target
supplier; no successful query is a caller premise. -/
theorem metadata {before : Before} {id : AllocId} (target : RelocationTargetMetadata before id) :
    ∃ info,before.memory.getAllocInfo id=.ok info ∧info.kind≠.dead ∧
      info.size.bytes.toNat≤maximumMetadataSize before ∧2^info.align.pow2≤maximumMetadataAlignment before := by
  obtain ⟨info,actual,live⟩:=GlobalAddressLiveErrorExclusion.metadata_of_supplier before.memory id target.1
  exact ⟨info,actual,live,queried target.1 info actual⟩

/-- The generated bump uses max(size,1); the domain's floor-one size maximum
therefore covers zero-size uniqueness bumps as well. -/
theorem charge {before : Before} {id : AllocId} (supplier : GlobalAddressLiveErrorExclusion.Supplier before.memory id)
    (info : AllocationInfo) (actual : before.memory.getAllocInfo id=.ok info) :
    15+2^info.align.pow2+max 1 info.size.bytes.toNat≤addressCharge before := by
  have bounded:=queried supplier info actual
  have one : 1≤maximumMetadataSize before:=one_max _
  unfold addressCharge
  have length : max 1 info.size.bytes.toNat≤maximumMetadataSize before:=Nat.max_le.mpr ⟨one,bounded.1⟩
  omega

/-- The domain's raw alignment clauses follow the same lookup priority as the
actual query, including function and va-list unit alignment. -/
theorem valid_alignment {before : Before} {id : AllocId} (target : RelocationTargetMetadata before id)
    (uncached : before.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=none)
    (info : AllocationInfo) (actual : before.memory.getAllocInfo id=.ok info) : info.align.pow2≤29 := by
  have bounds:=target.2.2 uncached
  cases target.1 with
  | localRow entry present =>
    simp only [MemoryState.getAllocInfo,present] at actual
    cases Except.ok.inj actual
    exact bounds.1 entry present
  | functionRow absent present =>
    simp only [MemoryState.getAllocInfo,absent,present,↓reduceIte] at actual
    cases Except.ok.inj actual
    exact Nat.zero_le _
  | vaListRow absent noFunction present =>
    unfold MemoryState.hasVaListId at present
    simp only [MemoryState.getAllocInfo,absent,noFunction,present,Bool.false_eq_true,↓reduceIte] at actual
    cases Except.ok.inj actual
    exact Nat.zero_le _
  | globalRow descriptor absent noFunction noVaList present =>
    unfold MemoryState.hasVaListId at noVaList
    simp only [MemoryState.getAllocInfo,absent,noFunction,noVaList,present,Bool.false_eq_true,↓reduceIte] at actual
    have bounded:=bounds.2 descriptor present
    cases kind : descriptor.kind <;> simp only [kind] at actual <;> cases Except.ok.inj actual
    all_goals first | exact bounded | exact Nat.zero_le _

private theorem alignment_nat (align : Align) (valid : align.pow2≤29) :
    (GlobalAddressAlignedBumpFormation.alignment align).toNat=2^align.pow2 := by
  cases align with
  | mk power =>
    change power≤29 at valid
    have possibilities : power=0 ∨ power=1 ∨ power=2 ∨ power=3 ∨ power=4 ∨ power=5 ∨ power=6 ∨ power=7 ∨ power=8 ∨ power=9 ∨ power=10 ∨ power=11 ∨ power=12 ∨ power=13 ∨ power=14 ∨ power=15 ∨ power=16 ∨ power=17 ∨ power=18 ∨ power=19 ∨ power=20 ∨ power=21 ∨ power=22 ∨ power=23 ∨ power=24 ∨ power=25 ∨ power=26 ∨ power=27 ∨ power=28 ∨ power=29 := by omega
    rcases possibilities with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide

/-- One REAL uncached-target address-generation step is covered by the
initial metadata charge, independently of relocation count or cache hits.
The fold can consume this leaf while retaining its remaining-charge invariant. -/
theorem generated {before : Before} {id : AllocId} (target : RelocationTargetMetadata before id)
    (uncached : before.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=none)
    (generator : AddressGenerator) (slack : Fin 16)
    (room : generator.nextBaseAddr.toNat+addressCharge before<2^64 ∧
      generator.nextBaseAddr.toNat+addressCharge before≤generator.endAddr.toNat) :
    ∃info,before.memory.getAllocInfo id=.ok info ∧
      generator.generate info.size info.align slack=⟨GlobalAddressAlignedBumpFormation.next generator info.size info.align slack,
        .ok (GlobalAddressAlignedBumpFormation.base generator info.align slack)⟩ ∧
      (GlobalAddressAlignedBumpFormation.next generator info.size info.align slack).nextBaseAddr.toNat≤
        generator.nextBaseAddr.toNat+addressCharge before := by
  obtain ⟨info,actual,_,_⟩:=metadata target
  have valid:=valid_alignment target uncached info actual
  have bounded:=charge target.1 info actual
  have alignNat:=alignment_nat info.align valid
  have slackBound:=slack.isLt
  have rawRoom : GlobalAddressAlignedBumpFormation.Room generator info.size info.align slack:=by
    unfold GlobalAddressAlignedBumpFormation.Room
    rw [GlobalAddressBumpRangeFormation.length_nat,alignNat]
    constructor <;> omega
  refine ⟨info,actual,GlobalAddressAlignedBumpFormation.generated generator info.size info.align valid slack rawRoom,?_⟩
  rw [GlobalAddressAlignedBumpFormation.next_nat generator info.size info.align valid slack rawRoom]
  have baseBound:=(GlobalAddressAlignedBumpFormation.base_bounds generator info.size info.align valid slack rawRoom).2
  rw [alignNat] at baseBound
  omega

end DuplicatePrefix.CurrentCallConversionMetadataBounds
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallConversionMetadataBounds" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved conversion metadata-bound dependency {dependency}"
