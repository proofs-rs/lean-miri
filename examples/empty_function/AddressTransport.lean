import empty_function.AddressPost
namespace EmptyFunction.AddressTransport
open Miri Miri.Memory Miri.Interpreter Miri.Memory.AllocAddresses
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Root-tag and choice-tape updates preserve current metadata backing when
the actual physical memory registry remains equal. -/
theorem backing (before after : WholeCall.State)
    (memory : after.machine.memory = before.machine.memory)
    (id : AllocId) (prior : InputDraft.MetadataBacking before id) :
    InputDraft.MetadataBacking after id := by
  cases prior with
  | live entry row => exact .live entry (by simpa only [memory] using row)
  | global entry row identity => exact .global entry (by simpa only [memory] using row) identity
  | extraFunction row => exact .extraFunction (by simpa only [memory] using row)
  | vaList row => exact .vaList (by simpa only [memory] using row)
  | dead entry row => exact .dead entry (by simpa only [memory] using row)

/-- Transport an established table postcondition to the actual root/address
machine result using its proved physical-memory and address-state equalities. -/
theorem tables (before after : WholeCall.State)
    (memory : after.machine.memory = before.machine.memory)
    (addresses : after.machine.user.addresses = before.machine.user.addresses)
    (prior : InputDraft.AddressTables before) : InputDraft.AddressTables after := by
  constructor
  · simpa only [addresses] using prior.baseIds
  · simpa only [addresses] using prior.inverseIds
  · intro row member
    exact backing before after memory row.allocId (prior.suppliers row (by simpa only [addresses] using member))
  · intro row member
    simpa only [memory] using prior.inverseLive row (by simpa only [addresses] using member)
  · intro row member
    exact prior.nonzero row (by simpa only [addresses] using member)
  · intro row member
    simpa only [addresses] using prior.bases row (by simpa only [addresses] using member)
  · intro row member live nonzero
    simpa only [addresses] using prior.liveBases row (by simpa only [addresses] using member)
      (by simpa only [memory] using live) nonzero
  · simpa only [addresses] using prior.ordered
  · intro left leftMember right rightMember different leftInfo rightInfo leftQuery rightQuery
    exact prior.separated left (by simpa only [addresses] using leftMember)
      right (by simpa only [addresses] using rightMember) different leftInfo rightInfo
      (by simpa only [memory] using leftQuery) (by simpa only [memory] using rightQuery)
  · intro id member
    simpa only [memory] using prior.exposedLive id (by simpa only [addresses] using member)
  · intro id member
    simpa only [addresses] using prior.exposedBases id (by simpa only [addresses] using member)

/-- Full generation representation depends on physical memory and address
state, so independently proved tracker/tape/thread updates can be retained. -/
theorem representation (before after : WholeCall.State)
    (memory : after.machine.memory = before.machine.memory)
    (addresses : after.machine.user.addresses = before.machine.user.addresses)
    (generation : AddressGenerationState)
    (prior : InputDraft.GenerationRepresentation before generation) :
    InputDraft.GenerationRepresentation after generation := by
  constructor
  · simpa only [addresses] using prior.current
  · simpa only [addresses] using prior.managed
  · exact tables before after memory addresses prior.tables
  · exact prior.reuseRateLower
  · exact prior.reuseRateUpper
  · exact prior.crossRateLower
  · exact prior.crossRateUpper
  · exact prior.poolKeys
  · exact prior.poolSize
  · exact prior.poolAddresses
  · exact prior.poolAlignment
  · exact prior.poolUnique
  · exact prior.poolSeparatedPairwise
  · intro bucket member row stored inverse indexed
    exact prior.poolAbsent bucket member row stored inverse (by simpa only [addresses] using indexed)
  · intro bucket member row stored inverse indexed info query
    exact prior.poolSeparated bucket member row stored inverse (by simpa only [addresses] using indexed)
      info (by simpa only [memory] using query)
  · intro row member info query
    exact prior.allocatedBeforeCursor row (by simpa only [addresses] using member) info
      (by simpa only [memory] using query)
end EmptyFunction.AddressTransport
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.AddressTransport.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved address transport axiom {dependency} in {name}"
