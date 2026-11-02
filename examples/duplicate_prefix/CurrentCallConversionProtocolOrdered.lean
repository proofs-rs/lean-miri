import duplicate_prefix.CurrentCallConversionFiniteFold

/-! Sorted inverse addresses through the SAME selected protocol and its
existing checked allocator resources. No converter or traversal is repeated. -/
namespace DuplicatePrefix.CurrentCallConversionProtocolOrdered
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open Miri.Memory.AllocAddresses
open CandidateCurrentJointCall CurrentCallOrdinaryInput CurrentCallConversionChoiceProtocol
open WildcardInteriorHitAddress
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/- Reuse only the uniquely named existing kernel theorem. This exposes no
new axiom and fails if the exact source namespace is absent or ambiguous. -/
open Lean Elab Tactic in
elab "conversion_ordered_rule " suffix:str : term => do
  let found:=(←getEnv).constants.toList.filter (fun (name,_)=>name.toString.endsWith suffix.getString)
  match found with
  | [(name,_)]=>return mkConst name
  | _=>throwError "expected unique checked converter rule {suffix.getString}"

private theorem missing_before (before after : GlobalAddressState) (id : AllocId)
    (hits : ∀query base,before.baseAddr.find? (fun row=>row.allocId==query)=some base→
      after.baseAddr.find? (fun row=>row.allocId==query)=some base)
    (missing : after.baseAddr.find? (fun row=>row.allocId==id)=none) :
    before.baseAddr.find? (fun row=>row.allocId==id)=none := by
  cases old : before.baseAddr.find? (fun row=>row.allocId==id) with
  | none=>rfl
  | some base=>rw [hits id base old] at missing;cases missing

/-- Generic proof on the existing protocol, carrying only its existing budget,
source metadata and current ordered vector. -/
theorem properties (memory : MemoryState Provenance BorrowTree MiriMemoryKind)
    (thread : AddressThreadId) (before after : GlobalAddressState)
    (tape nextTape : ExecutionChoices.Tape) (ids : List AllocId) (charge : Nat)
    (steps : AddressProtocol memory thread before tape ids after nextTape)
    (budget : CurrentCallConversionFiniteFold.Resources memory before ids charge)
    (initial : Ordered before.intToPtrMap)
    (metadata : ∀id∈ids,GlobalAddressLiveErrorExclusion.Supplier memory id)
    (formation : ∀id∈ids,before.baseAddr.find? (fun row=>row.allocId==id)=none→
      ∀info,memory.getAllocInfo id=.ok info→info.kind≠.dead ∧info.align.pow2≤29 ∧
        15+(GlobalAddressAlignedBumpFormation.alignment info.align).toNat+
          (GlobalAddressBumpRangeFormation.length info.size).toNat≤charge) :
    Ordered after.intToPtrMap ∧
      (CurrentCallConversionInfoRows.InfoRows memory before.intToPtrMap (CurrentCallConversionInfoRows.sizes memory)→
       CurrentCallConversionInfoRows.InfoRows memory after.intToPtrMap (CurrentCallConversionInfoRows.sizes memory)) := by
  induction steps with
  | nil addresses tape=>exact ⟨initial,fun rows=>rows⟩
  | cached addresses tape id rest base cached final after tail ih=>
    have nextBudget:=(conversion_ordered_rule ".CurrentCallConversionFiniteFold.cached_budget") memory addresses id rest charge budget base cached
    exact ih nextBudget initial (fun query member=>metadata query (List.mem_cons_of_mem id member))
      (fun query member missing info actual=>formation query (List.mem_cons_of_mem id member) missing info actual)
  | typeId addresses tape id rest info uncached actual kind final after tail ih=>
    have nextBudget:=(conversion_ordered_rule ".CurrentCallConversionFiniteFold.zero_budget") memory addresses id rest charge budget uncached
    have hits:=(conversion_ordered_rule ".CurrentCallConversionFiniteFold.cacheData_old") addresses id 0 uncached
    have nextOrdered : Ordered (cacheData addresses id 0).intToPtrMap := initial
    exact ih nextBudget nextOrdered (fun query member=>metadata query (List.mem_cons_of_mem id member))
      (fun query member missing info actual=>formation query (List.mem_cons_of_mem id member)
        (missing_before addresses _ query hits missing) info actual)
  | managed addresses tape id rest info uncached actual kind generation generationEq block final after tail ih=>
    obtain ⟨_,valid,charged⟩:=formation id (by simp) uncached info actual
    obtain ⟨initialRows,aligned,room,nextBudget⟩:=(conversion_ordered_rule ".CurrentCallConversionFiniteFold.managed_budget")
      memory addresses id rest charge budget (metadata id (by simp)) info actual kind uncached generation generationEq
      valid charged thread tape block
    obtain ⟨nextGeneration,nextRows⟩:=(conversion_ordered_rule ".CurrentCallConversionFiniteFold.advance_rows")
      memory addresses generation initialRows id (metadata id (by simp)) info actual uncached valid aligned thread tape block room
    have nextProperties : Ordered (advance addresses generation id info thread tape block).intToPtrMap ∧
        CurrentCallConversionInfoRows.InfoRows memory (advance addresses generation id info thread tape block).intToPtrMap
          (CurrentCallConversionInfoRows.sizes memory) := by
      rcases nextRows with ⟨ordered,_,rows,_,_,_,_,_,_,_⟩
      exact ⟨ordered,rows⟩
    obtain ⟨_,hits⟩:=(conversion_ordered_rule ".CurrentCallConversionFiniteFold.advance_hits")
      addresses generation id info thread tape block valid aligned uncached
    have finalProperties:=ih nextBudget nextProperties.1 (fun query member=>metadata query (List.mem_cons_of_mem id member))
      (fun query member missing info actual=>formation query (List.mem_cons_of_mem id member)
        (missing_before addresses _ query hits missing) info actual)
    exact ⟨finalProperties.1,fun _=>finalProperties.2 nextProperties.2⟩

theorem ordered (memory : MemoryState Provenance BorrowTree MiriMemoryKind)
    (thread : AddressThreadId) (before after : GlobalAddressState)
    (tape nextTape : ExecutionChoices.Tape) (ids : List AllocId) (charge : Nat)
    (steps : AddressProtocol memory thread before tape ids after nextTape)
    (budget : CurrentCallConversionFiniteFold.Resources memory before ids charge)
    (initial : Ordered before.intToPtrMap)
    (metadata : ∀id∈ids,GlobalAddressLiveErrorExclusion.Supplier memory id)
    (formation : ∀id∈ids,before.baseAddr.find? (fun row=>row.allocId==id)=none→
      ∀info,memory.getAllocInfo id=.ok info→info.kind≠.dead ∧info.align.pow2≤29 ∧
        15+(GlobalAddressAlignedBumpFormation.alignment info.align).toNat+
          (GlobalAddressBumpRangeFormation.length info.size).toNat≤charge) :
    Ordered after.intToPtrMap :=
  (properties memory thread before after tape nextTape ids charge steps budget initial metadata formation).1

theorem protocol {charge : Nat} (initial : Before) (ids : List AllocId) (thread : AddressThreadId)
    (tape : ExecutionChoices.Tape) (finalAddresses : GlobalAddressState) (finalTape : ExecutionChoices.Tape)
    (steps : AddressProtocol initial.memory thread initial.user.addresses tape ids finalAddresses finalTape)
    (budget : CurrentCallConversionFiniteFold.Resources initial.memory initial.user.addresses ids charge)
    (initialOrdered : Ordered initial.user.addresses.intToPtrMap)
    (metadata : ∀id∈ids,RelocationTargetMetadata initial id)
    (formation : ∀id∈ids,initial.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=none→
      ∀info,initial.memory.getAllocInfo id=.ok info→info.kind≠.dead ∧info.align.pow2≤29 ∧
        15+(GlobalAddressAlignedBumpFormation.alignment info.align).toNat+
          (GlobalAddressBumpRangeFormation.length info.size).toNat≤charge) :
    Ordered finalAddresses.intToPtrMap :=
  ordered initial.memory thread initial.user.addresses finalAddresses tape finalTape ids charge steps budget initialOrdered
    (fun id member=>(metadata id member).1) formation

/-- Size suppliers for every final inverse row, including unexposed rows
whose size is queried before the exposure guard. -/
theorem protocol_info_rows {charge : Nat} (initial : Before) (ids : List AllocId) (thread : AddressThreadId)
    (tape : ExecutionChoices.Tape) (finalAddresses : GlobalAddressState) (finalTape : ExecutionChoices.Tape)
    (steps : AddressProtocol initial.memory thread initial.user.addresses tape ids finalAddresses finalTape)
    (budget : CurrentCallConversionFiniteFold.Resources initial.memory initial.user.addresses ids charge)
    (initialOrdered : Ordered initial.user.addresses.intToPtrMap)
    (initialRows : CurrentCallConversionInfoRows.InfoRows initial.memory initial.user.addresses.intToPtrMap
      (CurrentCallConversionInfoRows.sizes initial.memory))
    (metadata : ∀id∈ids,RelocationTargetMetadata initial id)
    (formation : ∀id∈ids,initial.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=none→
      ∀info,initial.memory.getAllocInfo id=.ok info→info.kind≠.dead ∧info.align.pow2≤29 ∧
        15+(GlobalAddressAlignedBumpFormation.alignment info.align).toNat+
          (GlobalAddressBumpRangeFormation.length info.size).toNat≤charge) :
    CurrentCallConversionInfoRows.InfoRows initial.memory finalAddresses.intToPtrMap (CurrentCallConversionInfoRows.sizes initial.memory) :=
  (properties initial.memory thread initial.user.addresses finalAddresses tape finalTape ids charge steps budget initialOrdered
    (fun id member=>(metadata id member).1) formation).2 initialRows

end
end DuplicatePrefix.CurrentCallConversionProtocolOrdered
