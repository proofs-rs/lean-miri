import duplicate_prefix.CandidateCurrentJointCall
import duplicate_prefix.DuplicatePrefixCallSpecification

/-! A bounded current-representation exposure bridge. RuntimeInput.State does
not imply address/tree exposure coherence; error states can lack it because
address exposure is recorded before the tree hook. No ordinary admission is
asserted here. -/
namespace DuplicatePrefix.CandidateCurrentExposureOrigin
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Interpreter Miri.Input
open CandidateStableCallOwnership CandidateCurrentJointCall
set_option autoImplicit false

theorem resolved_exposed (addresses : GlobalAddressState) (address : UInt64)
    (size : Int64) (hooks : AddressLookupHooks) (id : AllocId)
    (resolved : addresses.allocIdFromAddr address size hooks = .ok (some id)) :
    addresses.exposed.contains id = true := by
  unfold GlobalAddressState.allocIdFromAddr at resolved
  simp only [bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure] at resolved
  repeat' first
    | split at resolved
    | simp_all only [Except.ok.injEq,Option.some.injEq,reduceCtorEq]
  all_goals cases exposure : addresses.exposed.contains id <;> simp_all

def ExposureCoherent (before : Before) : Prop :=
  ∀ id allocation, Present (ActualWorld before) id allocation →
    before.user.addresses.exposed.contains id = true →
    ∃ index node, allocation.extra.nodes.get index = some node ∧ node.isExposed = true

theorem older_origin (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (before : Before) (tracker : MachineHooks.BorrowState) (len : UInt64)
    (state : DuplicatePrefixRuntimeInput.State before tracker)
    (resources : DuplicatePrefixCallSpecification.Resources options limits remaining before tracker len)
    (coherent : ExposureCoherent before) (id : AllocId)
    (allocation : Allocation Provenance BorrowTree)
    (present : Present (ActualWorld before) id allocation)
    (address : UInt64) (hooks : AddressLookupHooks)
    (resolved : before.user.addresses.allocIdFromAddr address 0 hooks = .ok (some id)) :
    ∃ index node, allocation.extra.nodes.get index = some node ∧ node.isExposed = true ∧
      node.tag.value.toNat < tracker.global.nextPointerTag.value.toNat := by
  obtain ⟨index,node,nodeAt,exposed⟩ := coherent id allocation present
    (resolved_exposed _ address 0 hooks id resolved)
  refine ⟨index,node,nodeAt,exposed,?_⟩
  simp only [Present,ActualWorld,Array.toList_map] at present
  obtain ⟨⟨oldId,entry⟩,member,equal⟩ := List.mem_map.mp present
  rcases Prod.mk.inj equal with ⟨rfl,rfl⟩
  exact GeneralBorrowForestTagHighWater.mapped _ _ _ _ (resources.tagsBelow _ member)
    index ((state.formed _ member).allocator.nodeTags index node nodeAt)

end DuplicatePrefix.CandidateCurrentExposureOrigin

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CandidateCurrentExposureOrigin." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved current exposure origin dependency {dependency}"
