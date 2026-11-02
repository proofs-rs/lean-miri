import empty_function.AddressGenerationPost
namespace EmptyFunction.AddressStaticPost
open Miri Miri.Memory Miri.Memory.AllocAddresses
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 65536

def view (state : GlobalAddressState) := (state.addressMode,state.provenanceMode,state.exposed)

private theorem cache (state : GlobalAddressState) (id : AllocId) (address : UInt64) :
    view (state.cacheAddress id address).state = view state := by
  unfold GlobalAddressState.cacheAddress
  repeat' first | rfl | split

private theorem generation (state : GlobalAddressState) (next : AddressGenerationState) :
    view ((reuse_actual ".GlobalAddressState.setGeneration") state next) = view state := rfl

private theorem assigned (result : AddressStateResult AddressAssignment) (after : GlobalAddressState)
    (actual : AddressChoicePlan.assignedState result = .ok after) : view after = view result.state := by
  unfold AddressChoicePlan.assignedState at actual
  split at actual
  · cases actual
  · cases actual; rfl
  · dsimp only at actual
    split at actual
    · cases actual
    · cases actual; exact cache _ _ _

/-- Only generation/cache fields change in the actual pure address operation.
This postcondition is consumed after raw success is proved, never by validity. -/
theorem assignment (state : GlobalAddressState) (id : AllocId) (info : AllocationAddressInfo)
    (choices : AddressRandomChoices) (after : GlobalAddressState)
    (actual : AddressChoicePlan.assignedState (state.addrFromAllocId id (some info) choices) = .ok after) :
    view after = view state := by
  have result := assigned _ after actual
  unfold GlobalAddressState.addrFromAllocId at result
  split at result
  · exact result
  · simp only at result
    cases kind : info.memoryKind with
    | none => simpa only [kind,Id.run,pure] using result
    | some memoryKind =>
      simp only [kind,Id.run,pure] at result
      split at result
      · exact result
      · split at result
        · split at result <;> simpa only [cache,generation] using result
        · split at result
          · exact result
          · split at result
            · split at result
              · exact result
              · split at result
                · exact result
                · split at result <;> simpa only [cache,generation] using result
              · split at result
                · exact result
                · split at result <;> simpa only [cache,generation] using result
            · exact result

/-- Address observations used by whole-call preservation. -/
def Facts (before after : GlobalAddressState) : Prop :=
  after.addressMode = before.addressMode ∧ after.provenanceMode = before.provenanceMode ∧
  (∀ id row, before.baseAddr.find? (fun old => old.allocId == id) = some row →
    after.baseAddr.find? (fun current => current.allocId == id) = some row) ∧
  (∀ row ∈ before.intToPtrMap, ∃ next ∈ after.intToPtrMap,
    next.allocId = row.allocId ∧ next.address = row.address) ∧
  (∀ id ∈ before.exposed, after.exposed.contains id = true)

theorem identical (before after : GlobalAddressState) (same : after=before) : Facts before after := by
  subst after
  exact ⟨rfl,rfl,(by intro id row prior;exact prior),(by intro row member;exact ⟨row,member,rfl,rfl⟩),
    (by intro id member;exact Array.contains_eq_true_of_mem member)⟩

/-- Existing inverse entries follow from retained bases and the two current
coherence tables; no second operational map-insertion proof is required. -/
theorem inverse (before after : EmptyFunction.WholeCall.State) (old : EmptyFunction.InputDraft.AddressTables before)
    (current : EmptyFunction.InputDraft.AddressTables after) (memory : after.machine.memory = before.machine.memory)
    (bases : ∀ id row, before.machine.user.addresses.baseAddr.find? (fun entry => entry.allocId == id) = some row →
      after.machine.user.addresses.baseAddr.find? (fun entry => entry.allocId == id) = some row) :
    ∀ row ∈ before.machine.user.addresses.intToPtrMap,
      ∃ next ∈ after.machine.user.addresses.intToPtrMap, next.allocId = row.allocId ∧ next.address = row.address := by
  intro row member
  have query := bases row.allocId ⟨row.allocId,row.address⟩ (old.bases row member)
  have live : after.machine.memory.isAllocLive row.allocId = true := by
    rw [memory]
    exact old.inverseLive row member
  exact current.liveBases ⟨row.allocId,row.address⟩ (Array.mem_of_find?_eq_some query) live (old.nonzero row member)

theorem facts (before after : EmptyFunction.WholeCall.State) (old : EmptyFunction.InputDraft.AddressTables before)
    (current : EmptyFunction.InputDraft.AddressTables after) (memory : after.machine.memory = before.machine.memory)
    (bases : ∀ id row, before.machine.user.addresses.baseAddr.find? (fun entry => entry.allocId == id) = some row →
      after.machine.user.addresses.baseAddr.find? (fun entry => entry.allocId == id) = some row)
    (static : view after.machine.user.addresses = view before.machine.user.addresses) :
    EmptyFunction.Preservation.ExistingAddressFacts before after := by
  have mode := congrArg Prod.fst static
  have provenance := congrArg (fun fields => fields.2.1) static
  have exposed := congrArg (fun fields => fields.2.2) static
  refine ⟨mode,provenance,bases,inverse before after old current memory bases,?_⟩
  intro id member
  change after.machine.user.addresses.exposed = before.machine.user.addresses.exposed at exposed
  rw [exposed]
  exact Array.contains_eq_true_of_mem member

end EmptyFunction.AddressStaticPost
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.AddressStaticPost.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved static address post axiom {dependency} in {name}"
