import duplicate_prefix.CurrentCallResourceSourceKeyOrigin
import duplicate_prefix.CurrentCallTypedFnEntry

namespace DuplicatePrefix.CurrentCallResourceBorrowGrowth
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Input Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources CurrentCallResourceNormalization
open GeneralBorrowFnEntryRegistration TypedBorrowSteps ReferenceBorrowDriver
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

/-- One actual protected source borrow allocates at most one node, including
free-slot reuse. No future constructor-size premise is introduced. -/
theorem operation {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (state : DuplicatePrefixRuntimeInput.State before tracker)
    (highwater : ∀ row ∈ before.memory.live.toList,GeneralBorrowForestTagHighWater.Below row.2.allocation.extra tracker.global.protectedTags tracker.global.nextPointerTag)
    (frame : FrameState) (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (exclusive : demandOf mode=.exclusive) (distinct : W.allocation.extra.roots.toList.Nodup)
    (short : W.allocation.extra.nodes.size<65536) (nodeRoom : W.allocation.extra.nodes.size+1≤4294967295)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length) (nonzero : amount≠0)
    (bounds : start.toNat+amount.toNat≤W.allocation.extra.locations.size.bytes.toNat)
    (output : GeneralBorrowForestFnEntry.Output)
    (actual : CandidateCurrentFnEntryRaw.operation W.allocation.extra tracker.global frame id W.pointer.value.provenance start amount=.ok output) :
    output.child.tree.nodes.size ≤ W.allocation.extra.nodes.size + 1 := by
  have literalEq : output=CurrentCallTypedFnEntry.literal W.allocation.extra tracker.global frame id room W.pointer.value.provenance start amount := by
    exact Except.ok.inj (actual.symm.trans (CurrentCallTypedFnEntry.literal_operation _ _ _ _ room _ _ _))
  obtain ⟨_,held,_,_,_,freshTag⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare W.allocation.extra tracker.global frame id room runtime
  let registration := registered tracker.global frame id room
  obtain ⟨_,afterRuntime,_,_,nodes,_,tags,bytes⟩ := CurrentCallResourceFnEntry.prepare_read W runtime state highwater frame room exclusive
    distinct short start amount startEq amountEq bounds
  change DuplicatePrefixBorrowContract.RuntimeFacts (CurrentCallTypedFnEntry.literal W.allocation.extra tracker.global frame id room W.pointer.value.provenance start amount).access.tree registration.1 at afterRuntime
  rw [←literalEq] at afterRuntime
  change (CurrentCallTypedFnEntry.literal W.allocation.extra tracker.global frame id room W.pointer.value.provenance start amount).access.tree.nodes=W.allocation.extra.nodes at nodes
  change (CurrentCallTypedFnEntry.literal W.allocation.extra tracker.global frame id room W.pointer.value.provenance start amount).access.tree.tagMapping=W.allocation.extra.tagMapping at tags
  change (CurrentCallTypedFnEntry.literal W.allocation.extra tracker.global frame id room W.pointer.value.provenance start amount).access.tree.locations.size=W.allocation.extra.locations.size at bytes
  rw [←literalEq] at nodes tags bytes
  have freshAfter : GeneralBorrowTagMap.Fresh output.access.tree.tagMapping tracker.global.nextPointerTag := by rw [tags];exact freshTag
  have nodeCapacity : output.access.tree.nodes.size+1≤4294967295 := by rw [nodes];exact nodeRoom
  have childBounds : start.toNat+amount.toNat≤output.access.tree.locations.size.bytes.toNat := by rw [bytes];exact bounds
  have tagBound : tracker.global.nextPointerTag.value.toNat<registration.1.nextPointerTag.value.toNat := by
    have successor := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag room
    change tracker.global.nextPointerTag.value.toNat<(TypedRetagEmpty.successorTag tracker.global.nextPointerTag room).value.toNat
    omega
  have tagHeld : registration.1.protectedTags.contains tracker.global.nextPointerTag=true := by unfold ProtectedTags.contains;rw [held];rfl
  have childEq : output.child=output.access.tree.newChild (Size.ofBytes start) (CandidateCurrentWindowPointerChecks.extraOf W.pointer.value.provenance)
    tracker.global.nextPointerTag (DedupRangeMap.new (Size.ofBytes amount) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true := by rw [literalEq];rfl
  cases prov : W.pointer.value.provenance with
  | concrete id parentTag =>
    obtain ⟨parentNode,parentAt,_,binds⟩ := W.binding
    rw [prov] at binds
    have parentAfter : output.access.tree.nodeAt W.pointer.grant=some parentNode := by change output.access.tree.nodes.get _=_;rw [nodes];exact parentAt
    have tagged : output.access.tree.indexOfTag parentTag=some W.pointer.grant := by rw [binds.2];exact afterRuntime.formed.allocator.nodeTags _ _ parentAfter
    have ctor := GeneralBorrowProtectedConstructorRuntime.construct output.access.tree registration.1 afterRuntime parentTag tracker.global.nextPointerTag W.pointer.grant parentNode
      tagged parentAfter freshAfter nodeCapacity tagBound tagHeld start amount nonzero childBounds
    rw [childEq]
    simpa only [prov,CandidateCurrentWindowPointerChecks.extraOf,nodes] using ctor.2.2.2
  | wildcard =>
    have ctor := GeneralBorrowWildcardConstructorRuntime.protected_mutable output.access.tree registration.1 afterRuntime tracker.global.nextPointerTag freshAfter nodeCapacity tagBound tagHeld
      start amount nonzero childBounds
    rw [childEq]
    simpa only [prov,CandidateCurrentWindowPointerChecks.extraOf,nodes] using ctor.2.2.2.1

end
end DuplicatePrefix.CurrentCallResourceBorrowGrowth
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallResourceBorrowGrowth.").length != 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved resource growth dependency {dependency}"
