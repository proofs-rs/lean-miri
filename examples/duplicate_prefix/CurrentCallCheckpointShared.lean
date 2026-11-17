import duplicate_prefix.GeneralBorrowRawTargetActivity
import duplicate_prefix.CurrentCallPostEntryCheckpoint
import duplicate_prefix.CurrentCallSpatialSharedInstall
import duplicate_prefix.CurrentCallSpatialControlView
namespace DuplicatePrefix.CurrentCallCheckpointShared
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization CurrentCallSpatialCover GeneralRangeMapOrigins
open CurrentCallPostEntryCheckpoint GeneralBorrowRawSharedExpression GeneralBorrowFnEntryRegistration
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
variable {options remaining span len count place} (checkpoint : Checkpoint options remaining span len count place)

def before : Before:=RootZeroCompleteState.tick options remaining span checkpoint.machine

theorem start_eq : (UInt64.ofNat checkpoint.offset).toNat=checkpoint.offset := by
  obtain ⟨entry,base,live,cached,extent,headroom,bounds,address,nonnull,provenance⟩:=checkpoint.source.binding
  have fit:=checkpoint.source.role.family.value.offset.bytes.toNat_lt
  have offsetFit : checkpoint.offset<2^64 := by omega
  simp only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt offsetFit]

def role := CurrentCallSpatialControlView.reindex
  (CurrentCallSpatialControlView.role checkpoint.source.role (CurrentCallSpatialControlView.tick_world options remaining span checkpoint.machine))
  (start_eq checkpoint) rfl

theorem bounds : (UInt64.ofNat checkpoint.offset).toNat+len.toNat≤(role checkpoint).backing.allocation.extra.locations.size.bytes.toNat := by
  let Q:=role checkpoint
  let byte:=(Q.backing.id,(UInt64.ofNat checkpoint.offset).toNat+len.toNat-1)
  have positive:=checkpoint.source.positive
  have request : Window Q.backing.id (UInt64.ofNat checkpoint.offset).toNat len.toNat byte:=⟨rfl,by dsimp only [byte];omega,by dsimp only [byte];omega⟩
  obtain ⟨i,cell⟩:=Q.covered byte request
  let overlap : CurrentCallSpatialSourceCover.Active Q i:=⟨byte,request,cell⟩
  have last:=((Q.roles i overlap).available byte request cell).1
  have extent:=(Q.roles i overlap).issued.capability.extent
  have capacity:=(Q.roles i overlap).issued.capability.treeExtent
  rw [capacity]
  rw [extent] at last
  dsimp only [byte] at last
  omega

theorem room : checkpoint.tracker.global.nextPointerTag.value<18446744073709551615 := by
  apply UInt64.lt_iff_toNat_lt.mpr
  have margin:=checkpoint.tags
  change checkpoint.tracker.global.nextPointerTag.value.toNat<18446744073709551615
  omega

def tree : BorrowTree := CurrentCallSpatialSharedInstall.tree (role checkpoint) checkpoint.source.tag (UInt64.ofNat checkpoint.offset) len

def machine : Before:=CurrentCallSpatialSharedInstall.machine (role checkpoint) (room checkpoint) checkpoint.sourceEntry checkpoint.source.tag (UInt64.ofNat checkpoint.offset) len

def tracker : MachineHooks.BorrowState:=CurrentCallSpatialSharedInstall.next (tracker:=checkpoint.tracker) (room checkpoint)

/-- This is the same literal Default Read and constructor used by the typed
shared-reference step. All permission cells survive together. -/
theorem operation :
    let accessed:=CurrentCallSpatialDefaultShared.accessed (role checkpoint) checkpoint.source.tag (UInt64.ofNat checkpoint.offset) len
    accessed.status=.Completed ∧
    (child (role checkpoint).backing.allocation.extra checkpoint.tracker.global.protectedTags checkpoint.source.tag checkpoint.tracker.global.nextPointerTag
      (UInt64.ofNat checkpoint.offset) len .VisitChildrenOfAccessed).outcome=.ok () ∧
    DuplicatePrefixBorrowContract.RuntimeFacts (tree checkpoint) (tracker checkpoint).global ∧
    (tree checkpoint).locations.size=(role checkpoint).backing.allocation.extra.locations.size ∧
    (tree checkpoint).nodes.size≤(role checkpoint).backing.allocation.extra.nodes.size+1 ∧
    ∃reader,(tree checkpoint).indexOfTag checkpoint.tracker.global.nextPointerTag=some reader ∧
      OwnedOn (GeneralBorrowSharedReadConstructor.Capabilities (tree checkpoint) checkpoint.tracker.global.protectedTags checkpoint.source.grant reader)
        (UInt64.ofNat checkpoint.offset) (UInt64.ofNat checkpoint.offset+len) (tree checkpoint).locations ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin (tree checkpoint) reader .Read (UInt64.ofNat checkpoint.offset) (UInt64.ofNat checkpoint.offset+len) := by
  have nonzero : len≠0:=by intro zero;have p:=checkpoint.source.positive;rw [zero] at p;cases p
  obtain ⟨parent,node,mapped,present,nodeTag,readDone,childDone,runtime,capacity,growth,reader,lookup,caps,active⟩:=
    CurrentCallSpatialDefaultShared.construct (role checkpoint) checkpoint.source.runtime checkpoint.source.distinct
      (by have h:=checkpoint.source.nodes;change (role checkpoint).backing.allocation.extra.nodes.size+6<65536 at h;omega)
      (by have h:=checkpoint.source.nodes;change (role checkpoint).backing.allocation.extra.nodes.size+6<65536 at h;omega)
      checkpoint.source.tag checkpoint.source.concrete (room checkpoint) (UInt64.ofNat checkpoint.offset) len rfl rfl nonzero (bounds checkpoint)
  have qMapped : (role checkpoint).backing.allocation.extra.indexOfTag checkpoint.source.tag=some checkpoint.source.grant := by
    rw [←checkpoint.source.nodeTag]
    exact checkpoint.source.runtime.formed.allocator.nodeTags _ _ checkpoint.source.nodeAt
  have same : parent=checkpoint.source.grant:=Option.some.inj (mapped.symm.trans qMapped)
  subst parent
  exact ⟨readDone,childDone,runtime,capacity,growth,reader,lookup,caps,active⟩

theorem installed :
    ∃context : CurrentCallSpatialCover.Context (machine checkpoint),
      ∃current : RoleCover (machine checkpoint) (tracker checkpoint) context .mut (UInt64.ofNat checkpoint.offset).toNat len.toNat,
        current.family=(role checkpoint).family ∧current.backing.allocation=(role checkpoint).backing.allocation.setExtra (tree checkpoint) ∧
        current.backing.id=(role checkpoint).backing.id ∧∃parent reader,
          (role checkpoint).backing.allocation.extra.indexOfTag checkpoint.source.tag=some parent ∧
          (tree checkpoint).indexOfTag checkpoint.tracker.global.nextPointerTag=some reader ∧
          ∃original : Fin current.backing.cells.size→Fin (role checkpoint).backing.cells.size,
            ∀j,current.backing.cells[j].offset=(role checkpoint).backing.cells[original j].offset ∧
              current.backing.cells[j].length=(role checkpoint).backing.cells[original j].length ∧
              current.backing.cells[j].completion=S05ConcreteProtectedChildCompletion.extend (role checkpoint).backing.cells[original j].completion reader parent := by
  have nonzero : len≠0:=by intro zero;have p:=checkpoint.source.positive;rw [zero] at p;cases p
  exact CurrentCallSpatialSharedInstall.install (role checkpoint) checkpoint.source.runtime checkpoint.source.distinct
    (by have h:=checkpoint.source.nodes;change (role checkpoint).backing.allocation.extra.nodes.size+6<65536 at h;omega)
    (by have h:=checkpoint.source.nodes;change (role checkpoint).backing.allocation.extra.nodes.size+6<65536 at h;omega)
    checkpoint.source.tag checkpoint.source.concrete (room checkpoint) (UInt64.ofNat checkpoint.offset) len rfl rfl nonzero (bounds checkpoint)
    checkpoint.sourceEntry checkpoint.sourceAllocation
/-- Same actual constructor metadata and source activity, with no leaf-q claim. -/
theorem metadata :
    ∃reader readerNode,
      (tree checkpoint).indexOfTag checkpoint.tracker.global.nextPointerTag=some reader ∧
      (tree checkpoint).nodeAt reader=some readerNode ∧readerNode.tag=checkpoint.tracker.global.nextPointerTag ∧
      readerNode.parent=some checkpoint.source.grant ∧readerNode.isExposed=false ∧
      (tree checkpoint).roots=(role checkpoint).backing.allocation.extra.roots ∧
      (∃qNode,(tree checkpoint).nodeAt checkpoint.source.grant=some qNode ∧qNode.tag=checkpoint.source.node.tag ∧
        qNode.parent=checkpoint.source.node.parent ∧qNode.isExposed=checkpoint.source.node.isExposed) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin (tree checkpoint) checkpoint.source.grant .Write
        (UInt64.ofNat checkpoint.offset) (UInt64.ofNat checkpoint.offset+len) ∧
      (∀index old,(role checkpoint).backing.allocation.extra.nodes.get index=some old→∃changed,
        (tree checkpoint).nodes.get index=some changed ∧changed.tag=old.tag ∧changed.parent=old.parent ∧
        changed.isExposed=old.isExposed ∧changed.defaultInitialPermission=old.defaultInitialPermission) := by
  let Q:=role checkpoint
  have nonzero : len≠0:=by intro zero;have p:=checkpoint.source.positive;rw [zero] at p;cases p
  have short : Q.backing.allocation.extra.nodes.size<65536 := by have h:=checkpoint.source.nodes;change Q.backing.allocation.extra.nodes.size+6<65536 at h;omega
  have nodeRoom : Q.backing.allocation.extra.nodes.size+1≤4294967295 := by omega
  obtain ⟨parent,node,mapped,present,nodeTag,readDone,readRuntime,nodes,roots,tags,capacity,wholeNormal,parents⟩:=
    CurrentCallSpatialDefaultShared.prepare Q checkpoint.source.runtime checkpoint.source.distinct short checkpoint.source.tag checkpoint.source.concrete
      (room checkpoint) (UInt64.ofNat checkpoint.offset) len rfl rfl nonzero (bounds checkpoint)
  have qMapped : Q.backing.allocation.extra.indexOfTag checkpoint.source.tag=some checkpoint.source.grant := by
    rw [←checkpoint.source.nodeTag]
    exact checkpoint.source.runtime.formed.allocator.nodeTags _ _ checkpoint.source.nodeAt
  have same : parent=checkpoint.source.grant:=Option.some.inj (mapped.symm.trans qMapped)
  subst parent
  have sameNode : node=checkpoint.source.node:=Option.some.inj (present.symm.trans checkpoint.source.nodeAt)
  subst node
  let accessed:=CurrentCallSpatialDefaultShared.accessed Q checkpoint.source.tag (UInt64.ofNat checkpoint.offset) len
  have high:=GeneralBorrowForestTagHighWater.complete Q.backing.allocation.extra _ _ checkpoint.source.runtime.below checkpoint.source.runtime.formed.allocator.nodeTags
  obtain ⟨fresh,_,unheld⟩:=GenericFunctionTagFormation.fresh_above Q.backing.allocation.extra _ _ checkpoint.tracker.global.nextPointerTag high (Nat.le_refl _)
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping checkpoint.tracker.global.nextPointerTag := by rw [tags];exact fresh
  have parentAfter : accessed.tree.nodeAt checkpoint.source.grant=some checkpoint.source.node := by change accessed.tree.nodes.get _=_;rw [nodes];exact present
  have tagged : accessed.tree.indexOfTag checkpoint.source.tag=some checkpoint.source.grant := by change accessed.tree.tagMapping.get _=_;rw [tags];exact mapped
  have boundsAfter : (UInt64.ofNat checkpoint.offset).toNat+len.toNat≤accessed.tree.locations.size.bytes.toNat := by rw [capacity];exact bounds checkpoint
  have roomAfter : accessed.tree.nodes.size+1≤4294967295 := by rw [nodes];exact nodeRoom
  have tagBound : checkpoint.tracker.global.nextPointerTag.value.toNat<(advanced checkpoint.tracker.global (room checkpoint)).nextPointerTag.value.toNat := by
    have successor:=GenericFunctionEntryNumerics.successor_value checkpoint.tracker.global.nextPointerTag (room checkpoint)
    change checkpoint.tracker.global.nextPointerTag.value.toNat<(TypedRetagEmpty.successorTag checkpoint.tracker.global.nextPointerTag (room checkpoint)).value.toNat
    omega
  obtain ⟨reader,lookup,⟨readerNode,readerAt,readerTag,readerParent,readerHidden⟩,old⟩:=GeneralBorrowSharedChildGraph.construct accessed.tree
    (advanced checkpoint.tracker.global (room checkpoint)) readRuntime checkpoint.source.tag checkpoint.tracker.global.nextPointerTag
    checkpoint.source.grant checkpoint.source.node tagged parentAfter freshAfter roomAfter false (UInt64.ofNat checkpoint.offset) len nonzero boundsAfter
  obtain ⟨_,_,_,_,other,otherLookup,leaf,oldFields⟩:=CurrentCallSharedConstructorFrame.metadata accessed.tree (advanced checkpoint.tracker.global (room checkpoint)) readRuntime
    checkpoint.source.tag checkpoint.tracker.global.nextPointerTag checkpoint.source.grant checkpoint.source.node tagged parentAfter freshAfter roomAfter tagBound unheld
    (UInt64.ofNat checkpoint.offset) len nonzero boundsAfter
  have otherSame : other=reader:=Option.some.inj (otherLookup.symm.trans lookup)
  subst other
  have readActivity:=GeneralBorrowFreshActiveWithinAccess.normal Q.backing.allocation.extra checkpoint.source.tag (Size.ofBytes (UInt64.ofNat checkpoint.offset)) (Size.ofBytes len) .Read
    checkpoint.tracker.global.protectedTags .VisitChildrenOfAccessed checkpoint.source.grant (UInt64.ofNat checkpoint.offset) (UInt64.ofNat checkpoint.offset+len)
    checkpoint.source.runtime.formed.well (bounds checkpoint) (Nat.le_refl _) (Nat.le_refl _) checkpoint.source.activity
  have activity:=GeneralBorrowRawTargetActivity.shared accessed.tree (advanced checkpoint.tracker.global (room checkpoint)) readRuntime
    checkpoint.source.tag checkpoint.tracker.global.nextPointerTag checkpoint.source.grant checkpoint.source.node tagged parentAfter freshAfter roomAfter false
    (UInt64.ofNat checkpoint.offset) len nonzero boundsAfter checkpoint.source.grant (UInt64.ofNat checkpoint.offset) (UInt64.ofNat checkpoint.offset+len)
    (Nat.le_refl _) (Nat.le_refl _) readActivity
  refine ⟨reader,readerNode,lookup,readerAt,readerTag,readerParent,readerHidden,leaf.roots.trans roots,old _ _ parentAfter,activity,?_⟩
  intro index node atNode
  apply oldFields index node
  change accessed.tree.nodes.get index=some node
  rw [nodes]
  exact atNode

/-- The Default observer is allocated but never protected. -/
theorem reader_unheld : (tracker checkpoint).global.protectedTags.contains checkpoint.tracker.global.nextPointerTag=false := by
  have high:=GeneralBorrowForestTagHighWater.complete (role checkpoint).backing.allocation.extra _ _ checkpoint.source.runtime.below checkpoint.source.runtime.formed.allocator.nodeTags
  obtain ⟨_,_,unheld⟩:=GenericFunctionTagFormation.fresh_above (role checkpoint).backing.allocation.extra _ _ checkpoint.tracker.global.nextPointerTag high (Nat.le_refl _)
  exact unheld

end
end DuplicatePrefix.CurrentCallCheckpointShared
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointShared" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved checkpoint shared dependency {dependency}"
