import duplicate_prefix.CurrentCallCheckpointLenSource
import duplicate_prefix.CurrentCallSpatialDefaultMutableInstall
import duplicate_prefix.CurrentCallSpatialEntryConstructor

namespace DuplicatePrefix.CurrentCallCheckpointMutable
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open S05ConcreteProtectedChildCompletion S05CompletedAncestryReadMutable
open CurrentCallPostEntryCheckpoint CurrentCallResourceNormalization CurrentCallSpatialCover GeneralRangeMapOrigins
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 65536
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
variable {options remaining span len count place limits} (cp : Checkpoint options remaining span len count place)
  (control : CurrentCallCheckpointLenReturn.Result cp limits) (source : CurrentCallCheckpointLenSource.Data cp control)

def tracker := CurrentCallCheckpointLenControl.postTracker cp

include source in
theorem room : (tracker cp).global.nextPointerTag.value<18446744073709551615 := by
  apply UInt64.lt_iff_toNat_lt.mpr
  change (tracker cp).global.nextPointerTag.value.toNat<18446744073709551615
  have budget : (tracker cp).global.nextPointerTag.value.toNat+4<18446744073709551615:=source.tags
  omega

theorem bounds : (UInt64.ofNat cp.offset).toNat+len.toNat≤source.role.backing.allocation.extra.locations.size.bytes.toNat := by
  let point:=(source.role.backing.id,cp.offset+len.toNat-1)
  have positive:=cp.source.positive
  have request : Window source.role.backing.id cp.offset len.toNat point:=⟨rfl,by dsimp only [point];omega,by dsimp only [point];omega⟩
  obtain ⟨i,cell⟩:=source.role.covered point request
  let overlap : CurrentCallSpatialSourceCover.Active source.role i:=⟨point,request,cell⟩
  have last:=((source.role.roles i overlap).available point request cell).1
  have extent:=(source.role.roles i overlap).issued.capability.extent
  have capacity:=(source.role.roles i overlap).issued.capability.treeExtent
  rw [capacity,CurrentCallCheckpointShared.start_eq cp]
  rw [extent] at last
  dsimp only [point] at last
  omega

def entry : LocalAllocation Provenance BorrowTree MiriMemoryKind:=
  {CurrentCallCheckpointLenControl.entry cp with allocation:=(CurrentCallCheckpointLenControl.entry cp).allocation.setExtra (CurrentCallCheckpointLenControl.releasedTree cp)}

def tree : BorrowTree:=CurrentCallSpatialDefaultMutableInstall.tree source.role cp.source.tag (UInt64.ofNat cp.offset) len

def machine : Before:=CurrentCallSpatialDefaultMutableInstall.machine source.role (room cp control source) (entry cp) cp.source.tag (UInt64.ofNat cp.offset) len

def next : MachineHooks.BorrowState:=CurrentCallSpatialDefaultMutableInstall.next (tracker:=tracker cp) (room cp control source)

/-- One CURRENT installed cover is selected once, then all its cells are used
by the same S operation. No initial-cell ancestry identity is asserted. -/
structure Prepared where
  context : CurrentCallSpatialCover.Context (machine cp control source)
  role : RoleCover (machine cp control source) (next cp control source) context .mut cp.offset len.toNat
  family : role.family=CurrentCallSpatialMutableCover.family source.role (tracker cp).global.nextPointerTag
  allocation : role.backing.allocation=source.role.backing.allocation.setExtra (tree cp control source)
  id : role.backing.id=source.role.backing.id
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra (next cp control source).global
  distinct : role.backing.allocation.extra.roots.toList.Nodup
  short : role.backing.allocation.extra.nodes.size<65536
  nodeRoom : role.backing.allocation.extra.nodes.size+1≤4294967295
  room : (next cp control source).global.nextPointerTag.value<18446744073709551615
  bounds : (UInt64.ofNat cp.offset).toNat+len.toNat≤role.backing.allocation.extra.locations.size.bytes.toNat

private theorem extra_setExtra (allocation : Allocation Provenance BorrowTree) (tree : BorrowTree) :
  (allocation.setExtra tree).extra=tree := by cases allocation;rfl

theorem from_source : Nonempty (Prepared cp control source) := by
  have positive:=cp.source.positive
  have nonzero : len≠0:=by intro zero;rw [zero] at positive;cases positive
  have short : source.role.backing.allocation.extra.nodes.size<65536:=by have budget:=source.nodes;omega
  have nodeRoom : source.role.backing.allocation.extra.nodes.size+1≤4294967295:=by omega
  obtain ⟨context,Q,family,allocation,idEq,parent,child,mapped,lookup,original,cells⟩:=CurrentCallSpatialDefaultMutableInstall.install source.role
    source.runtime source.distinct short nodeRoom cp.source.tag source.concrete (room cp control source)
    (UInt64.ofNat cp.offset) len (CurrentCallCheckpointShared.start_eq cp) rfl nonzero (bounds cp control source) (entry cp) source.allocation.symm
  have treeEq : Q.backing.allocation.extra=tree cp control source:=(congrArg Allocation.extra allocation).trans (extra_setExtra _ _)
  obtain ⟨oldParent,node,oldMapped,oldAt,nodeTag,readDone,childDone,afterRuntime,capacity,growth,newChild,newLookup,both,active⟩:=
    CurrentCallSpatialDefaultMutable.construct source.role source.runtime source.distinct short nodeRoom cp.source.tag source.concrete
      (room cp control source) (UInt64.ofNat cp.offset) len (CurrentCallCheckpointShared.start_eq cp) rfl nonzero (bounds cp control source)
  obtain ⟨readParent,readNode,readMapped,readAt,readTag,_,readRuntime,nodes,roots,tags,readCapacity,normal,parents⟩:=
    CurrentCallSpatialDefaultShared.prepare source.role source.runtime source.distinct short cp.source.tag source.concrete (room cp control source)
      (UInt64.ofNat cp.offset) len (CurrentCallCheckpointShared.start_eq cp) rfl nonzero (bounds cp control source)
  have sameParent : readParent=oldParent:=Option.some.inj (readMapped.symm.trans oldMapped)
  subst readParent
  have sameNode : readNode=node:=Option.some.inj (readAt.symm.trans oldAt)
  subst readNode
  let accessed:=CurrentCallSpatialDefaultShared.accessed source.role cp.source.tag (UInt64.ofNat cp.offset) len
  have high:=GeneralBorrowForestTagHighWater.complete source.role.backing.allocation.extra _ _ source.runtime.below source.runtime.formed.allocator.nodeTags
  obtain ⟨fresh,_,unheld⟩:=GenericFunctionTagFormation.fresh_above source.role.backing.allocation.extra _ _ (tracker cp).global.nextPointerTag high (Nat.le_refl _)
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping (tracker cp).global.nextPointerTag:=by rw [tags];exact fresh
  have parentAt : accessed.tree.nodeAt oldParent=some node:=by change accessed.tree.nodes.get _=_;rw [nodes];exact oldAt
  have parentTagged : accessed.tree.indexOfTag cp.source.tag=some oldParent:=by change accessed.tree.tagMapping.get _=_;rw [tags];exact oldMapped
  have roomAfter : accessed.tree.nodes.size+1≤4294967295:=by rw [nodes];exact nodeRoom
  have boundsAfter : (UInt64.ofNat cp.offset).toNat+len.toNat≤accessed.tree.locations.size.bytes.toNat:=by rw [readCapacity];exact bounds cp control source
  have tagBound : (tracker cp).global.nextPointerTag.value.toNat<(next cp control source).global.nextPointerTag.value.toNat:=by
    have successor:=GenericFunctionEntryNumerics.successor_value (tracker cp).global.nextPointerTag (room cp control source)
    change (tracker cp).global.nextPointerTag.value.toNat<(TypedRetagEmpty.successorTag (tracker cp).global.nextPointerTag (room cp control source)).value.toNat
    omega
  obtain ⟨i,cell⟩:=source.role.covered (source.role.backing.id,cp.offset) ⟨rfl,Nat.le_refl _,by omega⟩
  let overlap : CurrentCallSpatialSourceCover.Active source.role i:=⟨_,⟨rfl,Nat.le_refl _,by omega⟩,cell⟩
  have primary : ∃rootNode,accessed.tree.nodes.get allocationRoot=some rootNode:=by
    obtain ⟨rootNode,atRoot,_⟩:=(source.role.roles i overlap).issued.capability.rootNode
    exact ⟨rootNode,by rw [nodes];exact atRoot⟩
  have parentOrder : node.tag.value≤(tracker cp).global.nextPointerTag.value:=
    UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp (GeneralBorrowParentTagInvariant.parent_below_fresh _ _ source.runtime oldParent node oldAt)))
  obtain ⟨_,_,_,_,_,_,leaf,_,_,_⟩:=(spatial_install_rule ".CurrentCallResourceDefaultMutable.completion_construct") accessed.tree
    (next cp control source).global source.role.backing.cells[i].completion readRuntime (parents i) cp.source.tag (tracker cp).global.nextPointerTag
    oldParent node parentTagged parentAt freshAfter roomAfter tagBound unheld (UInt64.ofNat cp.offset) len nonzero boundsAfter primary parentOrder
  have nextRoom : (next cp control source).global.nextPointerTag.value<18446744073709551615:=by
    apply UInt64.lt_iff_toNat_lt.mpr
    change (next cp control source).global.nextPointerTag.value.toNat<18446744073709551615
    have nextEq : (next cp control source).global.nextPointerTag.value.toNat=(tracker cp).global.nextPointerTag.value.toNat+1:=
      GenericFunctionEntryNumerics.successor_value (tracker cp).global.nextPointerTag (room cp control source)
    have budget : (tracker cp).global.nextPointerTag.value.toNat+4<18446744073709551615:=source.tags
    omega
  have treeCapacity : (tree cp control source).locations.size=source.role.backing.allocation.extra.locations.size:=capacity
  have afterRoots : (tree cp control source).roots=source.role.backing.allocation.extra.roots:=leaf.roots.trans roots
  have afterShort : Q.backing.allocation.extra.nodes.size<65536:=by
    rw [treeEq]
    have growth' : (tree cp control source).nodes.size≤source.role.backing.allocation.extra.nodes.size+1:=growth
    have budget:=source.nodes
    omega
  have roomNodes : Q.backing.allocation.extra.nodes.size+1≤4294967295:=by omega
  refine ⟨{ context := context
            role := Q
            family := family
            allocation := allocation
            id := idEq
            runtime := ?_
            distinct := ?_
            short := afterShort
            nodeRoom := roomNodes
            room := nextRoom
            bounds := ?_ }⟩
  · rw [treeEq];exact afterRuntime
  · rw [treeEq,afterRoots];exact source.distinct
  · rw [treeEq,treeCapacity];exact bounds cp control source

/-- Choose one CURRENT P cover at the actual installed state and fix it for S. -/
def prepared : Prepared cp control source:=Classical.choice (from_source cp control source)
def sOutput := CurrentCallSpatialEntryRead.output (prepared cp control source).role {} (prepared cp control source).room (UInt64.ofNat cp.offset) len

theorem p_tree : (prepared cp control source).role.backing.allocation.extra=tree cp control source:=
  (congrArg Allocation.extra (prepared cp control source).allocation).trans (extra_setExtra _ _)

theorem p_provenance : (prepared cp control source).role.family.value.provenance=
    .concrete source.role.backing.id (tracker cp).global.nextPointerTag := by
  rw [(prepared cp control source).family]
  rfl

theorem s_operation :
    let output := CurrentCallSpatialEntryRead.output (prepared cp control source).role ({} : FrameState) (prepared cp control source).room (UInt64.ofNat cp.offset) len
    CandidateCurrentFnEntryRaw.operation (prepared cp control source).role.backing.allocation.extra (next cp control source).global ({} : FrameState) (prepared cp control source).role.backing.id
      (prepared cp control source).role.family.value.provenance (UInt64.ofNat cp.offset) len=.ok output ∧
    output.access.status=.Completed ∧ output.child.outcome=.ok () ∧
    DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree output.global ∧
    output.child.tree.locations.size=(prepared cp control source).role.backing.allocation.extra.locations.size ∧
    output.child.tree.nodes.size≤(prepared cp control source).role.backing.allocation.extra.nodes.size+1 ∧
    ∃ child,output.child.tree.indexOfTag output.tag=some child ∧
      (∀ (position : Nat) (root : UniIndex),(prepared cp control source).role.backing.allocation.extra.roots[position]?=some root → output.child.tree.roots[position]?=some root) ∧
      (∀ index node,(prepared cp control source).role.backing.allocation.extra.nodes.get index=some node →
        ∃ next,output.child.tree.nodes.get index=some next ∧next.tag=node.tag ∧next.parent=node.parent ∧
          next.isExposed=node.isExposed ∧next.defaultInitialPermission=node.defaultInitialPermission) ∧
      (∃node,output.child.tree.nodes.get child=some node ∧node.tag=output.tag) := by
  have nonzero : len≠0:=by intro zero;have positive:=cp.source.positive;rw [zero] at positive;cases positive
  exact CurrentCallSpatialEntryConstructor.invoke (prepared cp control source).role rfl (prepared cp control source).runtime (prepared cp control source).distinct (prepared cp control source).short (prepared cp control source).nodeRoom {} (prepared cp control source).room (UInt64.ofNat cp.offset) len (CurrentCallCheckpointShared.start_eq cp) rfl nonzero (prepared cp control source).bounds

theorem s_cells :
    let output := CurrentCallSpatialEntryRead.output (prepared cp control source).role ({} : FrameState) (prepared cp control source).room (UInt64.ofNat cp.offset) len
    ∃child,output.child.tree.indexOfTag output.tag=some child ∧
      ∀ (i : Fin (prepared cp control source).role.backing.cells.size)
        (overlap : ∃byte,Window (prepared cp control source).role.backing.id cp.offset len.toNat byte ∧Window (prepared cp control source).role.backing.id (prepared cp control source).role.backing.cells[i].offset (prepared cp control source).role.backing.cells[i].length byte)
        (lower upper : UInt64), cp.offset≤lower.toNat →upper.toNat≤cp.offset+len.toNat →
        (prepared cp control source).role.backing.cells[i].offset≤lower.toNat →upper.toNat≤(prepared cp control source).role.backing.cells[i].offset+(prepared cp control source).role.backing.cells[i].length →
        ParentInterpretation output.child.tree (extend (prepared cp control source).role.backing.cells[i].completion child ((prepared cp control source).role.roles i overlap).grant) ∧
        OwnedOn (Authority output.child.tree (extend (prepared cp control source).role.backing.cells[i].completion child ((prepared cp control source).role.roles i overlap).grant)
          output.global.protectedTags child) lower upper output.child.tree.locations := by
  have nonzero : len≠0:=by intro zero;have positive:=cp.source.positive;rw [zero] at positive;cases positive
  exact CurrentCallSpatialEntryConstructor.cells (prepared cp control source).role rfl (prepared cp control source).runtime (prepared cp control source).distinct (prepared cp control source).short (prepared cp control source).nodeRoom {} (prepared cp control source).room (UInt64.ofNat cp.offset) len (CurrentCallCheckpointShared.start_eq cp) rfl nonzero (prepared cp control source).bounds

theorem s_actual : CandidateCurrentFnEntryRaw.operation (tree cp control source) (next cp control source).global {}
    source.role.backing.id (.concrete source.role.backing.id (tracker cp).global.nextPointerTag) (UInt64.ofNat cp.offset) len=
      .ok (sOutput cp control source) := by
  have actual : CandidateCurrentFnEntryRaw.operation (prepared cp control source).role.backing.allocation.extra (next cp control source).global {}
    (prepared cp control source).role.backing.id (prepared cp control source).role.family.value.provenance (UInt64.ofNat cp.offset) len=.ok (sOutput cp control source) :=
      (s_operation cp control source).1
  rw [p_tree cp control source,(prepared cp control source).id,p_provenance cp control source] at actual
  exact actual

end
end DuplicatePrefix.CurrentCallCheckpointMutable
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointMutable" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved checkpoint mutable dependency {dependency}"
