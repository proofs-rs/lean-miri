import duplicate_prefix.CurrentCallSpatialDefaultShared
import duplicate_prefix.CurrentCallSpatialSharedCover
import duplicate_prefix.CurrentCallSpatialRead
import duplicate_prefix.CurrentCallSpatialSourceInstall
import duplicate_prefix.CurrentCallResourceDefaultShared
import duplicate_prefix.CurrentCallSharedConstructorWindow

/-! Default shared construction starts with ONE actual whole-span Read.
Physical Normal is independent of the cell completion used to justify each
row. No one completion owns the whole source request. -/
namespace DuplicatePrefix.CurrentCallSpatialSharedInstall
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

def tree (tag : BorTag) (start amount : UInt64) :=
  (GeneralBorrowRawSharedExpression.child role.backing.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag
    start amount .VisitChildrenOfAccessed).tree

def machine (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (tag : BorTag) (start amount : UInt64) : Before :=
  {ReferenceBorrowDriver.allocatedMachine before tracker room with
    memory:=RetagEntry.updatedMemory before.memory role.backing.id entry (tree role tag start amount)}

def next (room : tracker.global.nextPointerTag.value<18446744073709551615) : MachineHooks.BorrowState :=
  ReferenceBorrowDriver.allocatedTracker tracker room

theorem install
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup) (short : role.backing.allocation.extra.nodes.size<65536)
    (nodeRoom : role.backing.allocation.extra.nodes.size+1≤4294967295)
    (tag : BorTag) (concrete : role.family.value.provenance=.concrete role.backing.id tag)
    (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
    (nonzero : amount≠0) (bounds : start.toNat+amount.toNat≤role.backing.allocation.extra.locations.size.bytes.toNat)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (allocationEq : entry.allocation=role.backing.allocation) :
    ∃ context : CurrentCallSpatialCover.Context (machine role room entry tag start amount),
      ∃ current : RoleCover (machine role room entry tag start amount) (next (tracker:=tracker) room) context .mut offset length,
        current.family=role.family ∧current.backing.allocation=role.backing.allocation.setExtra (tree role tag start amount) ∧current.backing.id=role.backing.id ∧∃parent reader,
          role.backing.allocation.extra.indexOfTag tag=some parent ∧(tree role tag start amount).indexOfTag tracker.global.nextPointerTag=some reader ∧
          ∃original : Fin current.backing.cells.size→Fin role.backing.cells.size,
            ∀j,current.backing.cells[j].offset=role.backing.cells[original j].offset ∧
              current.backing.cells[j].length=role.backing.cells[original j].length ∧
              current.backing.cells[j].completion=S05ConcreteProtectedChildCompletion.extend role.backing.cells[original j].completion reader parent := by
  obtain ⟨parent,node,mapped,present,nodeTag,readDone,readRuntime,nodes,roots,tags,capacity,wholeNormal,parents⟩ :=
    CurrentCallSpatialDefaultShared.prepare role runtime distinct short tag concrete room start amount startEq amountEq nonzero bounds
  obtain ⟨otherParent,reader,otherMapped,readerLookup,cells⟩ :=
    CurrentCallSpatialDefaultShared.cells role runtime distinct short nodeRoom tag concrete room start amount startEq amountEq nonzero bounds
  have sameParent : otherParent=parent:=Option.some.inj (otherMapped.symm.trans mapped)
  subst otherParent
  let accessed:=CurrentCallSpatialDefaultShared.accessed role tag start amount
  have high:=GeneralBorrowForestTagHighWater.complete role.backing.allocation.extra _ _ runtime.below runtime.formed.allocator.nodeTags
  obtain ⟨fresh,_,unheld⟩:=GenericFunctionTagFormation.fresh_above role.backing.allocation.extra _ _ tracker.global.nextPointerTag high (Nat.le_refl _)
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping tracker.global.nextPointerTag := by rw [tags];exact fresh
  have parentAfter : accessed.tree.nodeAt parent=some node := by change accessed.tree.nodes.get _=_;rw [nodes];exact present
  have tagged : accessed.tree.indexOfTag tag=some parent := by change accessed.tree.tagMapping.get _=_;rw [tags];exact mapped
  have boundsAfter : start.toNat+amount.toNat≤accessed.tree.locations.size.bytes.toNat := by rw [capacity];exact bounds
  have roomAfter : accessed.tree.nodes.size+1≤4294967295 := by rw [nodes];exact nodeRoom
  have tagBound : tracker.global.nextPointerTag.value.toNat<(advanced tracker.global room).nextPointerTag.value.toNat := by
    have successor:=GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag room
    change tracker.global.nextPointerTag.value.toNat<(TypedRetagEmpty.successorTag tracker.global.nextPointerTag room).value.toNat
    omega
  obtain ⟨_,afterRuntime,afterCapacity,_,other,lookup,leaf,old⟩ := CurrentCallSharedConstructorFrame.metadata accessed.tree (advanced tracker.global room)
    readRuntime tag tracker.global.nextPointerTag parent node tagged parentAfter freshAfter roomAfter tagBound unheld start amount nonzero boundsAfter
  have same : other=reader:=Option.some.inj (lookup.symm.trans readerLookup)
  subst other
  have live : Present (ActualWorld (machine role room entry tag start amount)) role.backing.id (role.backing.allocation.setExtra (tree role tag start amount)) := by
    unfold Present ActualWorld machine RetagEntry.updatedMemory
    rw [Array.toList_map]
    apply List.mem_map.mpr
    refine ⟨_,Array.mem_toList_iff.mpr Array.mem_push_self,?_⟩
    simp only [allocationEq]
  have oldRoots : ∀(position : Nat) (root : UniIndex),role.backing.allocation.extra.roots[position]?=some root→(tree role tag start amount).roots[position]?=some root := by
    intro position root atRoot
    rw [show (tree role tag start amount).roots=role.backing.allocation.extra.roots from leaf.roots.trans roots]
    exact atRoot
  have metadata : ∀index node,role.backing.allocation.extra.nodes.get index=some node→
      ∃changed,(tree role tag start amount).nodes.get index=some changed ∧changed.tag=node.tag ∧changed.parent=node.parent ∧
        changed.isExposed=node.isExposed ∧changed.defaultInitialPermission=node.defaultInitialPermission := by
    intro index node present
    apply old index node
    change accessed.tree.nodes.get index=some node
    rw [nodes]
    exact present
  have vacant : role.backing.allocation.extra.nodes.get reader=none := by rw [←nodes];exact leaf.vacant
  have boundCapacity : (tree role tag start amount).locations.size=role.backing.allocation.extra.locations.size := afterCapacity.trans capacity
  let updates := CurrentCallSpatialSharedCover.updates (next:=next (tracker:=tracker) room) role live rfl boundCapacity oldRoots metadata vacant afterRuntime concrete mapped cells
  refine ⟨CurrentCallSpatialSourceCover.context role live updates,
    CurrentCallSpatialSourceCover.assemble role live updates role.id,rfl,rfl,rfl,parent,reader,mapped,readerLookup,
    (fun j=>(CurrentCallSpatialSourceCover.originalIndex role live updates j).val),?_⟩
  intro j
  dsimp only [CurrentCallSpatialSourceCover.assemble] at j ⊢
  rw [CurrentCallSpatialSourceCover.backing_cell_original]
  exact ⟨rfl,rfl,rfl⟩

end
end DuplicatePrefix.CurrentCallSpatialSharedInstall
