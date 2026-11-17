import duplicate_prefix.CurrentCallResourceDefaultShared
import duplicate_prefix.CurrentCallDefaultSharedAuthority
import duplicate_prefix.S05CurrentReadProtectorRelease

namespace DuplicatePrefix.CurrentCallSharedReadResources
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open GeneralBorrowFnEntryRegistration GeneralRangeMapOrigins GeneralBorrowRawSharedExpression
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

/-- Immediate next-Len resource consumer of the SAME actual Default shared
constructor. Only q's OTHER-root raw rights survive in the public result;
selected-component operation uses the actual r Read capability. -/
theorem rows {before tracker data owner id offset length}
    (W : UniformWindow before tracker data owner id offset length .mut)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (tag : BorTag) (concrete : W.pointer.value.provenance = .concrete id tag)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615)
    (start amount : UInt64)
    (P : CurrentCallResourceDefaultShared.Preparation W tag start amount room)
    (nodeRoom : W.allocation.extra.nodes.size+1 ≤ 4294967295)
    (nonzero : amount ≠ 0) (bounds : start.toNat+amount.toNat ≤ W.allocation.extra.locations.size.bytes.toNat)
    (reader : UniIndex)
    (lookup : (child W.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed).tree.indexOfTag tracker.global.nextPointerTag = some reader)
    (caps : OwnedOn (GeneralBorrowSharedReadConstructor.Capabilities
      (child W.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed).tree
      tracker.global.protectedTags W.pointer.grant reader) start (start+amount)
      (child W.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed).tree.locations) :
    let actual := child W.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed
    OwnedOn (S05CurrentReadProtectorRelease.Authority actual.tree
      (S05ConcreteProtectedChildCompletion.extend W.precise.completion reader W.pointer.grant)
      tracker.global.protectedTags P.geometry.selectedRoot W.pointer.grant reader)
      start (start+amount) actual.tree.locations := by
  dsimp only
  let after := read W.allocation.extra tracker.global.protectedTags tag start amount .VisitChildrenOfAccessed
  have high := GeneralBorrowForestTagHighWater.complete W.allocation.extra _ _ runtime.below runtime.formed.allocator.nodeTags
  obtain ⟨fresh,_,unheld⟩ := GenericFunctionTagFormation.fresh_above W.allocation.extra _ _ tracker.global.nextPointerTag high (Nat.le_refl _)
  have freshAfter : GeneralBorrowTagMap.Fresh after.tree.tagMapping tracker.global.nextPointerTag := by rw [P.tags];exact fresh
  obtain ⟨parent,parentAt,_,binding⟩ := W.binding
  rw [concrete] at binding
  have parentAfter : after.tree.nodeAt W.pointer.grant = some parent := by change after.tree.nodes.get _ = _;rw [P.nodes];exact parentAt
  have tagged : after.tree.indexOfTag tag = some W.pointer.grant := by rw [binding.2];exact P.runtime.formed.allocator.nodeTags _ _ parentAfter
  have boundsAfter : start.toNat+amount.toNat ≤ after.tree.locations.size.bytes.toNat := by rw [P.capacity];exact bounds
  have nodesRoom : after.tree.nodes.size+1 ≤ 4294967295 := by change after.tree.nodes.data.size+1 ≤ _;rw [P.nodes];exact nodeRoom
  have tagBound : tracker.global.nextPointerTag.value.toNat < (advanced tracker.global room).nextPointerTag.value.toNat := by
    have successor := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag room
    change tracker.global.nextPointerTag.value.toNat < (TypedRetagEmpty.successorTag tracker.global.nextPointerTag room).value.toNat
    omega
  obtain ⟨_,afterRuntime,_,_,other,otherLookup,authority⟩ := CurrentCallDefaultSharedAuthority.construct after.tree (advanced tracker.global room) W.precise.completion P.runtime P.parents
    tag tracker.global.nextPointerTag W.pointer.grant parent tagged parentAfter freshAfter nodesRoom tagBound unheld start amount nonzero boundsAfter P.owned
  have same : other = reader := Option.some.inj (otherLookup.symm.trans lookup)
  subst other
  intro position valid positive lower upper
  refine ⟨afterRuntime.possible position valid,(caps position valid positive lower upper).2,?_⟩
  intro rootPosition root rootAt different index node present path
  exact authority position valid positive lower upper index node present

end
end DuplicatePrefix.CurrentCallSharedReadResources
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallSharedReadResources.").length != 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved shared Read resource dependency {dependency}"
