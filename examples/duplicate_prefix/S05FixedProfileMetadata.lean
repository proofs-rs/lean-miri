import duplicate_prefix.DuplicatePrefixCallSpecification
import duplicate_prefix.DuplicatePrefixTypeCacheOrigins

namespace DuplicatePrefix.S05FixedProfileMetadata
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter
set_option autoImplicit false

/-- Explicit initial metadata compatibility candidate for the fixed managed
`DuplicatePrefix.Machine` profile. This is independent of Contract/Target and
is not a definition of all valid inputs or complete runtime consistency.

Source rationale: Machine.rootConfig uses EvalConfigurationCore.make, whose
foreign builder is absent; Machine.leaves also supplies foreign=none and a
sync callback that reports Unsupported. The inspected sync insertion sites
are the LinuxFutexMachine and TypedSyncObjectMachine object providers, which
that generic profile does not install. Stack/global allocation initializes
sync metadata empty. These source observations motivate the static condition;
no theorem that all histories establish it is asserted here.

Every selected live extras row exists, contains no unsupported synchronization
metadata, and has no weak buffer when global race clocks are absent. The
existing array-cache Origins condition permits populated compiler/runtime
array caches and excludes compiler non-array shadowing. Array layout/key/alias,
next-ID and other runtime consistency obligations are not defined here.
No operation outcome, future state, return capability or NoUB is a field. -/
structure Compatible (before : DuplicatePrefixCallSpecification.Before) : Prop where
  liveExtras : ∀ row ∈ before.memory.live.toList, ∃ extra,
    before.user.payload.payload.user.runtime.extras.allocations.find? (fun item => item.1 == row.1) =
      some (row.1,extra) ∧
    extra.sync = #[] ∧
    (before.dataRace = none → extra.weakMemory = none)
  cacheOrigins : DuplicatePrefixTypeCacheOrigins.Origins before.user.payload.payload.user.types

/-- A real live lookup selects the initial extras row. The synchronization
array is derived empty from the explicit profile condition, not from the
return-place capability or a successful write. -/
theorem Compatible.extras_at {before : DuplicatePrefixCallSpecification.Before}
    (metadata : Compatible before) (id : AllocId)
    (entry : LocalAllocation Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind)
    (present : before.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (noClocks : before.dataRace = none) :
    before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == id) =
      some (id,⟨none,#[]⟩) := by
  have member : (id,entry) ∈ before.memory.live.toList :=
    Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some present)
  obtain ⟨extra,found,sync,weak⟩ := metadata.liveExtras (id,entry) member
  have noWeak := weak noClocks
  cases extra with
  | mk weakMemory entries =>
    dsimp only at sync noWeak
    subst weakMemory
    subst entries
    exact found

/-- The same raw profile evidence supplies the existing return-allocation
extras leaf, without restricting its size, pointer provenance or borrow tree. -/
theorem Compatible.return_extras {before : DuplicatePrefixCallSpecification.Before}
    {place : MPlaceTy Provenance} (metadata : Compatible before)
    (input : DuplicatePrefixReturnPlaceInput.Input before place) (noClocks : before.dataRace = none) :
    before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == input.id) =
      some (input.id,⟨none,#[]⟩) :=
  metadata.extras_at input.id input.entry input.live noClocks

/-- Any extras row actually selected for the general return place has no sync
entry inside its byte. This is the raw premise of S04ReturnSyncOutside; no
callback equation or execution result is used. -/
theorem Compatible.return_sync_outside {before : DuplicatePrefixCallSpecification.Before}
    {place : MPlaceTy Provenance} (metadata : Compatible before)
    (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (extra : MemoryExtras.AllocationExtra Unit)
    (present : before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == input.id) =
      some (input.id,extra)) :
    ∀ row ∈ extra.sync,
      row.1.bytes.toNat < input.offset.toNat ∨ input.offset.toNat+1 ≤ row.1.bytes.toNat := by
  have member : (input.id,input.entry) ∈ before.memory.live.toList :=
    Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some input.live)
  obtain ⟨selected,found,sync,_⟩ := metadata.liveExtras (input.id,input.entry) member
  have equal : selected = extra := congrArg Prod.snd (Option.some.inj (found.symm.trans present))
  rw [←equal,sync]
  intro row absent
  exact False.elim (by simpa using absent)

/-- Coherent origins derive the old ty4 absence condition without imposing
an empty cache. The compiler metadata equation is the existing Model field. -/
theorem Compatible.slice_not_constructed {options : EvalConfigurationCore.Options} {remaining : Nat}
    {span : PreparedContracts.FixedSpanQuery} {before : DuplicatePrefixCallSpecification.Before}
    (metadata : Compatible before) (model : DuplicatePrefixCallModel.Model options remaining span before) :
    before.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false :=
  DuplicatePrefixTypeCacheOrigins.slice_not_constructed _ model.metadata metadata.cacheOrigins

/-- Direct bridge from the unchanged Contract PLUS separately named profile
metadata. This packages only initial extras/sync/type-cache premises. It does
not establish the actual call, empty-input coverage, or Target. -/
theorem from_contract {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : DuplicatePrefixCallSpecification.Before}
    {argument : DuplicatePrefixSliceArgument.Argument} {len : UInt64} {place : MPlaceTy Provenance}
    (contract : DuplicatePrefixCallSpecification.Contract options limits remaining span before argument len place)
    (metadata : Compatible before) :
    ∃ sync : Array (Size × MemoryExtras.Entry Unit),
      before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == contract.destination.id) =
        some (contract.destination.id,⟨none,sync⟩) ∧
      (∀ row ∈ sync, row.1.bytes.toNat < contract.destination.offset.toNat ∨
        contract.destination.offset.toNat+1 ≤ row.1.bytes.toNat) ∧
      before.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false := by
  have extras := metadata.return_extras contract.destination contract.model.noDataRace
  exact ⟨#[],extras,metadata.return_sync_outside contract.destination ⟨none,#[]⟩ extras,
    metadata.slice_not_constructed contract.model⟩

end DuplicatePrefix.S05FixedProfileMetadata
