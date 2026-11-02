import duplicate_prefix.CurrentCallSpatialDefaultShared
import duplicate_prefix.CurrentCallDefaultMutableWindow
import duplicate_prefix.GeneralBorrowDefaultCapabilityConstructor
import duplicate_prefix.CurrentCallSpatialRead
import duplicate_prefix.CurrentCallSpatialSourceInstall
import duplicate_prefix.CurrentCallResourceDefaultShared
import duplicate_prefix.CurrentCallSharedConstructorWindow

/-! Default shared construction starts with ONE actual whole-span Read.
Physical Normal is independent of the cell completion used to justify each
row. No one completion owns the whole source request. -/
namespace DuplicatePrefix.CurrentCallSpatialDefaultMutable
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.MIR
open CanonicalConfigFacts ActualReferenceContext RootReferenceInfo RootReferenceTrees
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization CurrentCallSpatialCover CurrentCallSpatialRows
open GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowProjection GeneralRangeMapOrigins GeneralRangeMapState
open GeneralBorrowRawSharedExpression GeneralBorrowFnEntryRegistration
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

variable {before tracker ctx offset length} (role : RoleCover before tracker ctx .mut offset length)

abbrev child := GeneralBorrowRawDefaultExpression.child

theorem construct
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup) (short : role.backing.allocation.extra.nodes.size<65536)
    (nodeRoom : role.backing.allocation.extra.nodes.size+1≤4294967295)
    (tag : BorTag) (concrete : role.family.value.provenance=.concrete role.backing.id tag)
    (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
    (nonzero : amount≠0) (bounds : start.toNat+amount.toNat≤role.backing.allocation.extra.locations.size.bytes.toNat) :
    ∃parent node,role.backing.allocation.extra.indexOfTag tag=some parent ∧role.backing.allocation.extra.nodes.get parent=some node ∧node.tag=tag ∧
      (CurrentCallSpatialDefaultShared.accessed role tag start amount).status=.Completed ∧
      let actual:=child role.backing.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed
      actual.outcome=.ok () ∧DuplicatePrefixBorrowContract.RuntimeFacts actual.tree (advanced tracker.global room) ∧
      actual.tree.locations.size=role.backing.allocation.extra.locations.size ∧actual.tree.nodes.size≤role.backing.allocation.extra.nodes.size+1 ∧
      ∃reader,actual.tree.indexOfTag tracker.global.nextPointerTag=some reader ∧
        OwnedOn (GeneralBorrowDefaultCapabilityRange.Both actual.tree tracker.global.protectedTags parent reader)
          start (start+amount) actual.tree.locations ∧
        GeneralBorrowFreshActiveWithin.ActiveWithin actual.tree reader .Write start (start+amount) := by
  obtain ⟨parent,node,lookup,present,nodeTag,readDone,readRuntime,nodes,roots,tags,capacity,wholeNormal,parents⟩:=
    CurrentCallSpatialDefaultShared.prepare role runtime distinct short tag concrete room start amount startEq amountEq nonzero bounds
  let after:=CurrentCallSpatialDefaultShared.accessed role tag start amount
  have high:=GeneralBorrowForestTagHighWater.complete role.backing.allocation.extra _ _ runtime.below runtime.formed.allocator.nodeTags
  obtain ⟨fresh,_,unheld⟩:=GenericFunctionTagFormation.fresh_above role.backing.allocation.extra _ _ tracker.global.nextPointerTag high (Nat.le_refl _)
  have freshAfter : GeneralBorrowTagMap.Fresh after.tree.tagMapping tracker.global.nextPointerTag:=by rw [tags];exact fresh
  have parentAt : after.tree.nodeAt parent=some node:=by change after.tree.nodes.get parent=some node;rw [nodes];exact present
  have parentTagged : after.tree.indexOfTag tag=some parent:=by change after.tree.tagMapping.get tag=some parent;rw [tags];exact lookup
  have nodesRoom : after.tree.nodes.size+1≤4294967295:=by rw [nodes];exact nodeRoom
  have childBounds : start.toNat+amount.toNat≤after.tree.locations.size.bytes.toNat:=by rw [capacity];exact bounds
  have tagBound : tracker.global.nextPointerTag.value.toNat<(advanced tracker.global room).nextPointerTag.value.toNat:=by
    have successor:=GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag room
    change tracker.global.nextPointerTag.value.toNat<(TypedRetagEmpty.successorTag tracker.global.nextPointerTag room).value.toNat
    omega
  have caps:=GeneralBorrowDefaultCapabilityConstructor.construct after.tree (advanced tracker.global room) readRuntime tag tracker.global.nextPointerTag
    parent node parentTagged parentAt freshAfter nodesRoom tagBound unheld start amount nonzero childBounds wholeNormal
  obtain ⟨reader,readerLookup,both⟩:=caps.2.2.2.2
  obtain ⟨activeReader,activeLookup,active⟩:=GeneralBorrowConstructorChildActivity.Default.construct after.tree (advanced tracker.global room) readRuntime
    tag tracker.global.nextPointerTag parent node parentTagged parentAt freshAfter nodesRoom start amount nonzero childBounds
  have same : activeReader=reader:=Option.some.inj (activeLookup.symm.trans readerLookup)
  subst activeReader
  refine ⟨parent,node,lookup,present,nodeTag,readDone,caps.1,caps.2.1,caps.2.2.1.trans capacity,?_,reader,readerLookup,both,active⟩
  have growth:=caps.2.2.2.1
  change _≤after.tree.nodes.size+1 at growth
  rw [nodes] at growth
  exact growth

theorem cells
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup) (short : role.backing.allocation.extra.nodes.size<65536)
    (nodeRoom : role.backing.allocation.extra.nodes.size+1≤4294967295)
    (tag : BorTag) (concrete : role.family.value.provenance=.concrete role.backing.id tag)
    (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
    (nonzero : amount≠0) (bounds : start.toNat+amount.toNat≤role.backing.allocation.extra.locations.size.bytes.toNat) :
    let actual:=child role.backing.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed
    ∃parent reader,role.backing.allocation.extra.indexOfTag tag=some parent ∧actual.tree.indexOfTag tracker.global.nextPointerTag=some reader ∧
      ∀(i : Fin role.backing.cells.size) (overlap : CurrentCallSpatialSourceCover.Active role i) (lower upper : UInt64),
        offset≤lower.toNat→upper.toNat≤offset+length→role.backing.cells[i].offset≤lower.toNat→upper.toNat≤role.backing.cells[i].offset+role.backing.cells[i].length→
        ParentInterpretation actual.tree (S05ConcreteProtectedChildCompletion.extend role.backing.cells[i].completion reader parent) ∧
        OwnedOn (S05CompletedAncestryReadMutable.Authority actual.tree (S05ConcreteProtectedChildCompletion.extend role.backing.cells[i].completion reader parent)
          tracker.global.protectedTags reader) lower upper actual.tree.locations := by
  obtain ⟨parent,node,mapped,present,nodeTag,readDone,readRuntime,nodes,roots,tags,capacity,wholeNormal,parents⟩:=
    CurrentCallSpatialDefaultShared.prepare role runtime distinct short tag concrete room start amount startEq amountEq nonzero bounds
  obtain ⟨otherParent,_,otherMapped,_,_,_,_,_,_,_,reader,readerLookup,_,_⟩:=
    construct role runtime distinct short nodeRoom tag concrete room start amount startEq amountEq nonzero bounds
  have sameParent : otherParent=parent:=Option.some.inj (otherMapped.symm.trans mapped)
  subst otherParent
  refine ⟨parent,reader,mapped,readerLookup,?_⟩
  intro i overlap lower upper requestLower requestUpper cellLower cellUpper
  let after:=CurrentCallSpatialDefaultShared.accessed role tag start amount
  have raw:=(spatial_install_rule ".CurrentCallSpatialDefaultShared.read_owned") role runtime distinct short tag concrete start amount startEq amountEq nonzero bounds i overlap lower upper requestLower requestUpper cellLower cellUpper
  have sourceAt:=CurrentCallSpatialRows.source_at role i overlap
  simp only [concrete] at sourceAt
  have sourceMapped : CurrentCallSpatialRows.source role=some parent:=by simp only [CurrentCallSpatialRows.source,concrete,mapped]
  have grant : (role.roles i overlap).grant=parent:=Option.some.inj (sourceAt.symm.trans sourceMapped)
  rw [grant] at raw
  have high:=GeneralBorrowForestTagHighWater.complete role.backing.allocation.extra _ _ runtime.below runtime.formed.allocator.nodeTags
  obtain ⟨fresh,_,unheld⟩:=GenericFunctionTagFormation.fresh_above role.backing.allocation.extra _ _ tracker.global.nextPointerTag high (Nat.le_refl _)
  have freshAfter : GeneralBorrowTagMap.Fresh after.tree.tagMapping tracker.global.nextPointerTag:=by rw [tags];exact fresh
  have parentAt : after.tree.nodeAt parent=some node:=by change after.tree.nodes.get parent=some node;rw [nodes];exact present
  have parentTagged : after.tree.indexOfTag tag=some parent:=by change after.tree.tagMapping.get tag=some parent;rw [tags];exact mapped
  have nodesRoom : after.tree.nodes.size+1≤4294967295:=by rw [nodes];exact nodeRoom
  have childBounds : start.toNat+amount.toNat≤after.tree.locations.size.bytes.toNat:=by rw [capacity];exact bounds
  have tagBound : tracker.global.nextPointerTag.value.toNat<(advanced tracker.global room).nextPointerTag.value.toNat:=by
    have successor:=GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag room
    change tracker.global.nextPointerTag.value.toNat<(TypedRetagEmpty.successorTag tracker.global.nextPointerTag room).value.toNat
    omega
  have primary : ∃node,after.tree.nodes.get allocationRoot=some node:=by
    obtain ⟨old,found,_⟩:=(role.roles i overlap).issued.capability.rootNode
    exact ⟨old,by rw [nodes];exact found⟩
  have parentOrder : node.tag.value≤tracker.global.nextPointerTag.value:=by
    exact UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp (GeneralBorrowParentTagInvariant.parent_below_fresh _ _ runtime parent node present)))
  have actualLower : start.toNat≤lower.toNat:=by omega
  have actualUpper : upper.toNat≤start.toNat+amount.toNat:=by omega
  obtain ⟨_,_,_,_,cellReader,cellLookup,model,retained⟩:=CurrentCallDefaultMutableWindow.construct_window after.tree (advanced tracker.global room)
    role.backing.cells[i].completion readRuntime (parents i) tag tracker.global.nextPointerTag parent node parentTagged parentAt freshAfter nodesRoom tagBound unheld
    start amount nonzero childBounds lower upper actualLower actualUpper primary parentOrder raw
  have sameReader : cellReader=reader:=Option.some.inj (cellLookup.symm.trans readerLookup)
  subst cellReader
  exact ⟨model,retained⟩

end
end DuplicatePrefix.CurrentCallSpatialDefaultMutable
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallSpatialDefaultMutable" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved spatial Default mutable dependency {dependency}"
