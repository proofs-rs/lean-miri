import duplicate_prefix.CurrentCallCheckpointMutableBoolFrame
import duplicate_prefix.CurrentCallCheckpointMutable
import duplicate_prefix.CurrentCallCheckpointLenSource

namespace DuplicatePrefix.CurrentCallCheckpointAcceptedBoolFrame
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CurrentCallPostEntryCheckpoint CurrentCallCheckpointLenSource GeneralRangeMapOrigins
open S05ConcreteProtectedChildCompletion S05CompletedAncestryReadMutable
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

variable {options remaining span len count place limits}
    (cp : Checkpoint options remaining span len count place)
    (result : CurrentCallCheckpointLenReturn.Result cp limits) (src : Data cp result)
    (B : CurrentCallCheckpointSharedBoolFrame.Packet cp result)

include src in
theorem room : (CurrentCallCheckpointLenControl.postTracker cp).global.nextPointerTag.value<18446744073709551615 := by
  apply UInt64.lt_iff_toNat_lt.mpr
  change (CurrentCallCheckpointLenControl.postTracker cp).global.nextPointerTag.value.toNat<18446744073709551615
  have budget:=src.tags
  omega

def tree : BorrowTree := (GeneralBorrowRawDefaultExpression.child src.role.backing.allocation.extra
  (CurrentCallCheckpointLenControl.postTracker cp).global.protectedTags cp.source.tag
  (CurrentCallCheckpointLenControl.postTracker cp).global.nextPointerTag (UInt64.ofNat cp.offset) len .VisitChildrenOfAccessed).tree

theorem bounds : (UInt64.ofNat cp.offset).toNat+len.toNat≤src.role.backing.allocation.extra.locations.size.bytes.toNat := by
  have request : Window src.role.backing.id cp.offset len.toNat (src.role.backing.id,cp.offset) := ⟨rfl,Nat.le_refl _,by have p:=cp.source.positive;omega⟩
  obtain ⟨i,cell⟩ := src.role.covered _ request
  let overlap : CurrentCallSpatialSourceCover.Active src.role i := ⟨_,request,cell⟩
  have extent := (src.role.roles i overlap).issued.capability.treeExtent
  rw [extent]
  exact src.storage.slice.bounds

theorem allocation_same (same : cp.output.id=cp.source.role.backing.id) :
    B.current.window.allocation=src.role.backing.allocation := by
  rw [B.allocated]
  dsimp only [CurrentCallCheckpointSharedBoolFrame.allocation]
  rw [ite_eq_left same]
  exact src.allocation.symm

/-- Current source and Bool packets feed the SAME accepted Default mutable
Read/constructor. No source authority under the Bool completion is assumed. -/
theorem default_same (same : cp.output.id=cp.source.role.backing.id) :
    ∃child,(tree cp result src).indexOfTag (CurrentCallCheckpointLenControl.postTracker cp).global.nextPointerTag=some child ∧
      ParentInterpretation (tree cp result src) (extend B.current.window.precise.completion child cp.source.grant) ∧
      OwnedOn (Authority (tree cp result src) (extend B.current.window.precise.completion child cp.source.grant)
        (CurrentCallCheckpointLenControl.postTracker cp).global.protectedTags B.current.window.pointer.grant)
        B.current.physical.offset (B.current.physical.offset+1) (tree cp result src).locations ∧
      (∃node,(tree cp result src).nodeAt B.current.window.pointer.grant=some node ∧node.tag=B.current.node.tag ∧node.parent=B.current.node.parent ∧
        node.children=B.current.node.children ∧node.isExposed=B.current.node.isExposed) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin (tree cp result src) B.current.window.pointer.grant .Write B.current.physical.offset (B.current.physical.offset+1) ∧
      (tree cp result src).locations.size=src.role.backing.allocation.extra.locations.size ∧
      (tree cp result src).roots=src.role.backing.allocation.extra.roots ∧
      (tree cp result src).nodes.size≤src.role.backing.allocation.extra.nodes.size+1 ∧
      (∀query old,src.role.backing.allocation.extra.nodeAt query=some old→∃next,(tree cp result src).nodeAt query=some next ∧
        next.tag=old.tag ∧next.parent=old.parent ∧next.isExposed=old.isExposed ∧next.defaultInitialPermission=old.defaultInitialPermission) := by
  have allocation := allocation_same cp result src B same
  have mapped : src.role.backing.allocation.extra.indexOfTag cp.source.tag=some cp.source.grant := by
    rw [←src.nodeTag];exact src.runtime.formed.allocator.nodeTags _ _ src.nodeAt
  have targetAt : src.role.backing.allocation.extra.nodeAt B.current.window.pointer.grant=some B.current.node := by
    rw [←allocation];exact B.current.nodeAt
  have different : B.current.window.pointer.grant≠cp.source.grant := by
    intro eq
    rw [eq] at targetAt
    have nodeEq := Option.some.inj (targetAt.symm.trans src.nodeAt)
    exact cp.sourceBoolTags (src.nodeTag.symm.trans ((congrArg TreeNode.tag nodeEq).symm.trans B.tag))
  have endEq : (B.current.physical.offset+1).toNat=B.current.offset+1 := by
    rw [UInt64.toNat_add,UInt64.toNat_one,Nat.mod_eq_of_lt,B.current.physicalOffset]
    exact Nat.lt_of_le_of_lt B.current.physical.bounds B.current.physical.capacity.toNat_lt
  have initial := (checkpoint_bool_rule "CurrentCallExclusiveWindowFrame.window_owned") B.current.window rfl B.current.runtime
    B.current.physical.offset (B.current.physical.offset+1) (by have h:=B.current.physicalOffset;omega) (by rw [endEq];exact Nat.le_refl _)
  have parents : ParentInterpretation src.role.backing.allocation.extra B.current.window.precise.completion := by rw [←allocation];exact B.current.window.parents
  have owned : OwnedOn (Authority src.role.backing.allocation.extra B.current.window.precise.completion (CurrentCallCheckpointLenControl.postTracker cp).global.protectedTags
      B.current.window.pointer.grant) B.current.physical.offset (B.current.physical.offset+1) src.role.backing.allocation.extra.locations := by rw [←allocation];exact initial
  have activity : GeneralBorrowFreshActiveWithin.ActiveWithin src.role.backing.allocation.extra B.current.window.pointer.grant .Write B.current.physical.offset (B.current.physical.offset+1) := by rw [←allocation];exact B.current.activity
  obtain ⟨root,rootAt,_,_,_⟩ := B.current.window.issued.capability.rootNode
  have primary : ∃node,src.role.backing.allocation.extra.nodes.get allocationRoot=some node := by rw [←allocation];exact ⟨root,rootAt⟩
  have nonzero : len≠0 := by intro zero;have p:=cp.source.positive;rw [zero] at p;cases p
  have offsetEq : B.current.physical.offset=cp.output.physical.offset := UInt64.toNat_inj.mp
    (B.current.physicalOffset.trans (B.offset.trans cp.output.physicalOffset.symm))
  have interval := CurrentCallCheckpointSharedBoolFrame.checkpoint_apart cp same
  have apart : ∀point : UInt64,B.current.physical.offset.toNat≤point.toNat→point.toNat<(B.current.physical.offset+1).toNat→
      point.toNat<(UInt64.ofNat cp.offset).toNat∨(UInt64.ofNat cp.offset+len).toNat≤point.toNat := by
    rw [offsetEq]
    intro point lo hi
    rcases interval with left | right <;>omega
  obtain ⟨child,lookup,nextParents,nextOwned,facets,active,geometry⟩ := CurrentCallCheckpointMutableBoolFrame.default_frame src.role src.runtime src.distinct
    (by have h:=src.nodes;omega) (by have h:=src.nodes;omega) B.current.window.precise.completion parents
    cp.source.tag cp.source.grant B.current.window.pointer.grant src.node B.current.node src.concrete mapped src.nodeAt targetAt
    B.current.leaf B.current.hidden different (room cp result src) (UInt64.ofNat cp.offset) len B.current.physical.offset (B.current.physical.offset+1)
    (CurrentCallCheckpointShared.start_eq cp) rfl nonzero (bounds cp result src) apart primary owned activity
  exact ⟨child,lookup,nextParents,nextOwned,facets,active,geometry⟩

/-- The SAME installed P role feeds the actual Strong S primitive while its
independent Bool bank retains the fixed two real parent extensions. -/
theorem strong_same (p : CurrentCallCheckpointMutable.Prepared cp result src)
    (same : cp.output.id=cp.source.role.backing.id) :
    let output := CurrentCallSpatialEntryRead.output p.role {} p.room (UInt64.ofNat cp.offset) len
    ∃parent child,p.role.backing.allocation.extra.indexOfTag (CurrentCallCheckpointLenControl.postTracker cp).global.nextPointerTag=some parent ∧
      output.child.tree.indexOfTag output.tag=some child ∧
      ParentInterpretation output.child.tree (extend (extend B.current.window.precise.completion parent cp.source.grant) child parent) ∧
      OwnedOn (Authority output.child.tree (extend (extend B.current.window.precise.completion parent cp.source.grant) child parent)
        output.global.protectedTags B.current.window.pointer.grant) B.current.physical.offset (B.current.physical.offset+1) output.child.tree.locations ∧
      (∃node,output.child.tree.nodeAt B.current.window.pointer.grant=some node ∧node.tag=B.current.node.tag ∧node.parent=B.current.node.parent ∧
        node.children=B.current.node.children ∧node.isExposed=B.current.node.isExposed) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin output.child.tree B.current.window.pointer.grant .Write B.current.physical.offset (B.current.physical.offset+1) := by
  have pTree := congrArg Allocation.extra p.allocation
  dsimp only [Allocation.setExtra,Allocation.mapExtra] at pTree
  have treeAlias : CurrentCallCheckpointMutable.tree cp result src=tree cp result src := rfl
  have actualTree : p.role.backing.allocation.extra=tree cp result src := pTree.trans treeAlias
  have concrete : p.role.family.value.provenance=.concrete p.role.backing.id (CurrentCallCheckpointLenControl.postTracker cp).global.nextPointerTag := by
    rw [p.family,p.id]
    rfl
  have request : Window p.role.backing.id cp.offset len.toNat (p.role.backing.id,cp.offset) := ⟨rfl,Nat.le_refl _,by have positive:=cp.source.positive;omega⟩
  obtain ⟨i,cell⟩ := p.role.covered _ request
  let overlap : CurrentCallSpatialSourceCover.Active p.role i := ⟨_,request,cell⟩
  let parent := (p.role.roles i overlap).grant
  obtain ⟨parentNode,parentAt,parentMapped,parentBinding⟩ := (p.role.roles i overlap).binding
  have value : (CurrentCallCheckpointLenControl.postTracker cp).global.nextPointerTag=parentNode.tag := by
    change (match p.role.family.value.provenance with
      | .concrete id tag=>id=p.role.family.allocation ∧tag=parentNode.tag
      | .wildcard=>parentNode.isExposed=true) at parentBinding
    rw [concrete] at parentBinding
    exact parentBinding.2
  have mapped : p.role.backing.allocation.extra.indexOfTag (CurrentCallCheckpointLenControl.postTracker cp).global.nextPointerTag=some parent := by
    rw [value]
    exact parentMapped
  obtain ⟨other,otherLookup,parents,owned,⟨node,nodeAt,nodeTag,nodeParent,nodeChildren,nodeHidden⟩,activity,_geometry⟩ := default_same cp result src B same
  have mappedOld : (tree cp result src).indexOfTag (CurrentCallCheckpointLenControl.postTracker cp).global.nextPointerTag=some parent := by rw [←actualTree];exact mapped
  have parentEq : other=parent := Option.some.inj (otherLookup.symm.trans mappedOld)
  subst other
  have targetAt : p.role.backing.allocation.extra.nodeAt B.current.window.pointer.grant=some node := by rw [actualTree];exact nodeAt
  have different : B.current.window.pointer.grant≠parent := by
    intro eq
    rw [eq] at targetAt
    have nodeEq := Option.some.inj (targetAt.symm.trans parentAt)
    have older := GeneralBorrowParentTagInvariant.parent_below_fresh _ _ B.current.runtime _ B.current.node B.current.nodeAt
    rw [←nodeTag,nodeEq,←value] at older
    exact UInt64.lt_irrefl _ older
  have currentParents : ParentInterpretation p.role.backing.allocation.extra (extend B.current.window.precise.completion parent cp.source.grant) := by rw [actualTree];exact parents
  have currentOwned : OwnedOn (Authority p.role.backing.allocation.extra (extend B.current.window.precise.completion parent cp.source.grant)
      (CurrentCallCheckpointMutable.next cp result src).global.protectedTags B.current.window.pointer.grant)
      B.current.physical.offset (B.current.physical.offset+1) p.role.backing.allocation.extra.locations := by rw [actualTree];exact owned
  have currentActivity : GeneralBorrowFreshActiveWithin.ActiveWithin p.role.backing.allocation.extra B.current.window.pointer.grant .Write
      B.current.physical.offset (B.current.physical.offset+1) := by rw [actualTree];exact activity
  obtain ⟨root,rootAt,_,_,_⟩ := (p.role.roles i overlap).issued.capability.rootNode
  have primary : ∃node,p.role.backing.allocation.extra.nodes.get allocationRoot=some node := ⟨root,rootAt⟩
  have nonzero : len≠0 := by intro zero;have positive:=cp.source.positive;rw [zero] at positive;cases positive
  have offsetEq : B.current.physical.offset=cp.output.physical.offset := UInt64.toNat_inj.mp
    (B.current.physicalOffset.trans (B.offset.trans cp.output.physicalOffset.symm))
  have interval := CurrentCallCheckpointSharedBoolFrame.checkpoint_apart cp same
  have apart : ∀point : UInt64,B.current.physical.offset.toNat≤point.toNat→point.toNat<(B.current.physical.offset+1).toNat→
      point.toNat<(UInt64.ofNat cp.offset).toNat∨(UInt64.ofNat cp.offset+len).toNat≤point.toNat := by
    rw [offsetEq]
    intro point lo hi
    rcases interval with left | right <;>omega
  obtain ⟨child,lookup,nextParents,nextOwned,facets,active,old⟩ := CurrentCallCheckpointMutableBoolFrame.strong_frame p.role p.runtime p.distinct p.short p.nodeRoom
    (extend B.current.window.precise.completion parent cp.source.grant) currentParents (CurrentCallCheckpointLenControl.postTracker cp).global.nextPointerTag
    parent B.current.window.pointer.grant parentNode node concrete mapped parentAt targetAt (nodeChildren.trans B.current.leaf) (nodeHidden.trans B.current.hidden)
    different p.room (UInt64.ofNat cp.offset) len B.current.physical.offset (B.current.physical.offset+1) (CurrentCallCheckpointShared.start_eq cp) rfl nonzero p.bounds
    apart primary currentOwned currentActivity
  obtain ⟨next,nextAt,nextTag,nextParent,nextChildren,nextHidden⟩ := facets
  refine ⟨parent,child,mapped,?_,?_,?_,⟨next,?_,nextTag.trans nodeTag,nextParent.trans nodeParent,nextChildren.trans nodeChildren,nextHidden.trans nodeHidden⟩,?_⟩
  · simpa only [CurrentCallSpatialEntryRead.output,CurrentCallSpatialEntryRead.read,CurrentCallSpatialEntryRead.registeredTracker,CurrentCallSpatialRows.provenance,concrete] using lookup
  · simpa only [CurrentCallSpatialEntryRead.output,CurrentCallSpatialEntryRead.read,CurrentCallSpatialEntryRead.registeredTracker,CurrentCallSpatialRows.provenance,concrete] using nextParents
  · simpa only [CurrentCallSpatialEntryRead.output,CurrentCallSpatialEntryRead.read,CurrentCallSpatialEntryRead.registeredTracker,CurrentCallSpatialRows.provenance,concrete] using nextOwned
  · simpa only [CurrentCallSpatialEntryRead.output,CurrentCallSpatialEntryRead.read,CurrentCallSpatialEntryRead.registeredTracker,CurrentCallSpatialRows.provenance,concrete] using nextAt
  · simpa only [CurrentCallSpatialEntryRead.output,CurrentCallSpatialEntryRead.read,CurrentCallSpatialEntryRead.registeredTracker,CurrentCallSpatialRows.provenance,concrete] using active



/-- The actual S observer release retains the independent Bool bank. The
physical source certificates are supplied by the SAME S resource producer. -/
theorem released_same (same : cp.output.id=cp.source.role.backing.id)
    (source : UniIndex) (sourceNode : TreeNode)
    (mapped : (CurrentCallCheckpointMutable.sOutput cp result src).child.tree.indexOfTag
      (CurrentCallCheckpointMutable.sOutput cp result src).tag=some source)
    (sourceAt : (CurrentCallCheckpointMutable.sOutput cp result src).child.tree.nodeAt source=some sourceNode)
    (sourceHidden : sourceNode.isExposed=false)
    (sourceTag : sourceNode.tag=(CurrentCallCheckpointMutable.sOutput cp result src).tag)
    (sourceActive : GeneralBorrowFreshActiveWithin.ActiveWithin (CurrentCallCheckpointMutable.sOutput cp result src).child.tree
      source .Write (UInt64.ofNat cp.offset) (UInt64.ofNat cp.offset+len))
    (normal : OwnedOn (fun location=>Nonempty (DuplicatePrefixBorrowAuthorization.Normal
      (CurrentCallCheckpointMutable.sOutput cp result src).child.tree location
      (CurrentCallCheckpointMutable.sOutput cp result src).global.protectedTags source))
      (UInt64.ofNat cp.offset) (UInt64.ofNat cp.offset+len) (CurrentCallCheckpointMutable.sOutput cp result src).child.tree.locations) :
    let output := CurrentCallCheckpointMutable.sOutput cp result src
    let actual := output.child.tree.releaseProtector output.tag output.global.protectedTags
    ∃parent,(CurrentCallCheckpointMutable.prepared cp result src).role.backing.allocation.extra.indexOfTag
        (CurrentCallCheckpointLenControl.postTracker cp).global.nextPointerTag=some parent ∧ParentInterpretation actual.tree (extend (extend B.current.window.precise.completion parent cp.source.grant) source parent) ∧
      OwnedOn (Authority actual.tree (extend (extend B.current.window.precise.completion parent cp.source.grant) source parent)
        (output.global.endCall output.frame).protectedTags B.current.window.pointer.grant)
        B.current.physical.offset (B.current.physical.offset+1) actual.tree.locations ∧
      (∃node,actual.tree.nodeAt B.current.window.pointer.grant=some node ∧node.tag=B.current.node.tag ∧node.parent=B.current.node.parent ∧
        node.children=B.current.node.children ∧node.isExposed=B.current.node.isExposed) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin actual.tree B.current.window.pointer.grant .Write B.current.physical.offset (B.current.physical.offset+1) := by
  let output := CurrentCallCheckpointMutable.sOutput cp result src
  obtain ⟨parent,child,parentMapped,childMapped,parents,owned,⟨node,nodeAt,nodeTag,nodeParent,nodeChildren,nodeHidden⟩,active⟩ :=
    strong_same cp result src B (CurrentCallCheckpointMutable.prepared cp result src) same
  have childEq : child=source := Option.some.inj (childMapped.symm.trans mapped)
  subst child
  have runtime := (CurrentCallCheckpointMutable.s_operation cp result src).2.2.2.1
  have different : B.current.window.pointer.grant≠source := by
    intro equal
    rw [equal] at nodeAt
    have eq := Option.some.inj (nodeAt.symm.trans sourceAt)
    have older := GeneralBorrowParentTagInvariant.parent_below_fresh _ _ B.current.runtime _ B.current.node B.current.nodeAt
    have successor := GenericFunctionEntryNumerics.successor_value (CurrentCallCheckpointLenControl.postTracker cp).global.nextPointerTag (room cp result src)
    change output.tag.value.toNat=(CurrentCallCheckpointLenControl.postTracker cp).global.nextPointerTag.value.toNat+1 at successor
    have tags := (congrArg TreeNode.tag eq).trans sourceTag
    rw [nodeTag] at tags
    have numeric := congrArg (fun tag : BorTag=>tag.value.toNat) tags
    have lower := UInt64.lt_iff_toNat_lt.mp older
    change B.current.node.tag.value.toNat<(CurrentCallCheckpointLenControl.postTracker cp).global.nextPointerTag.value.toNat at lower
    change B.current.node.tag.value.toNat=output.tag.value.toNat at numeric
    have ordering : B.current.node.tag.value.toNat<output.tag.value.toNat := by
      rw [successor]
      exact Nat.lt_trans lower (Nat.lt_succ_self _)
    exact (Nat.ne_of_lt ordering) numeric
  have offsetEq : B.current.physical.offset=cp.output.physical.offset := UInt64.toNat_inj.mp
    (B.current.physicalOffset.trans (B.offset.trans cp.output.physicalOffset.symm))
  have apart : (UInt64.ofNat cp.offset+len).toNat≤B.current.physical.offset.toNat ∨
      (B.current.physical.offset+1).toNat≤(UInt64.ofNat cp.offset).toNat := by
    have split := CurrentCallCheckpointSharedBoolFrame.checkpoint_apart cp same
    rw [offsetEq]
    rcases split with left | right <;> omega
  obtain ⟨nextParents,nextOwned,nextAt,nextActive⟩ := CurrentCallCheckpointMutableBoolFrame.release_frame
    output.child.tree output.global (extend (extend B.current.window.precise.completion parent cp.source.grant) source parent)
    runtime parents (CurrentCallCheckpointMutable.prepared cp result src).role.backing.id output.tag source B.current.window.pointer.grant
    sourceNode node mapped sourceAt sourceHidden nodeAt (nodeChildren.trans B.current.leaf) (nodeHidden.trans B.current.hidden) different
    (UInt64.ofNat cp.offset) (UInt64.ofNat cp.offset+len) B.current.physical.offset (B.current.physical.offset+1)
    sourceActive normal apart owned active
  exact ⟨parent,parentMapped,nextParents,nextOwned,⟨node,nextAt,nodeTag,nodeParent,nodeChildren,nodeHidden⟩,nextActive⟩


/-- Whole-frame endCall removes exactly the fresh Strong S registration.
The old Bool protector table is retained, including when its allocation differs. -/
theorem final_flags :
    let output := CurrentCallCheckpointMutable.sOutput cp result src
    (output.global.endCall output.frame).protectedTags=
      (CurrentCallCheckpointLenControl.postTracker cp).global.protectedTags := by
  let p := CurrentCallCheckpointMutable.prepared cp result src
  change ((CurrentCallCheckpointMutable.next cp result src).global.protectedTags.insert
    (CurrentCallCheckpointMutable.next cp result src).global.nextPointerTag .StrongProtector).remove
    (CurrentCallCheckpointMutable.next cp result src).global.nextPointerTag=_
  apply (checkpoint_bool_rule "CurrentCallCheckpointSharedBoolFrame.remove_fresh_insert")
  intro row member equal
  have below := p.runtime.below.protectors row member
  rw [equal] at below
  exact Nat.lt_irrefl _ below


/-- The two actual mutable constructors allocate exactly two tags. -/
theorem final_counter :
    (CurrentCallCheckpointMutable.sOutput cp result src).global.nextPointerTag.value.toNat=
      (CurrentCallCheckpointLenControl.postTracker cp).global.nextPointerTag.value.toNat+2 := by
  have first := GenericFunctionEntryNumerics.successor_value
    (CurrentCallCheckpointLenControl.postTracker cp).global.nextPointerTag (room cp result src)
  have second := GenericFunctionEntryNumerics.successor_value
    (CurrentCallCheckpointMutable.next cp result src).global.nextPointerTag
    (CurrentCallCheckpointMutable.prepared cp result src).room
  change (CurrentCallCheckpointMutable.next cp result src).global.nextPointerTag.value.toNat=
    (CurrentCallCheckpointLenControl.postTracker cp).global.nextPointerTag.value.toNat+1 at first
  change (CurrentCallCheckpointMutable.sOutput cp result src).global.nextPointerTag.value.toNat=
    (CurrentCallCheckpointMutable.next cp result src).global.nextPointerTag.value.toNat+1 at second
  omega

/-- A different Bool allocation is unchanged by source-local P/S operations;
its runtime facts weaken only the actual counter and restore the exact flags. -/
theorem different_runtime :
    DuplicatePrefixBorrowContract.RuntimeFacts B.current.window.allocation.extra
      ((CurrentCallCheckpointMutable.sOutput cp result src).global.endCall
        (CurrentCallCheckpointMutable.sOutput cp result src).frame) := by
  have flags := final_flags cp result src
  have counter := final_counter cp result src
  refine ⟨by rw [flags];exact B.current.runtime.formed,by rw [flags];exact B.current.runtime.coherent,
    B.current.runtime.possible,⟨?_,?_⟩⟩
  · intro row member
    exact Nat.lt_of_lt_of_le (B.current.runtime.below.mapping row member) (by
      change (CurrentCallCheckpointLenControl.postTracker cp).global.nextPointerTag.value.toNat≤
        (CurrentCallCheckpointMutable.sOutput cp result src).global.nextPointerTag.value.toNat
      omega)
  · intro row member
    rw [flags] at member
    exact Nat.lt_of_lt_of_le (B.current.runtime.below.protectors row member) (by
      change (CurrentCallCheckpointLenControl.postTracker cp).global.nextPointerTag.value.toNat≤
        (CurrentCallCheckpointMutable.sOutput cp result src).global.nextPointerTag.value.toNat
      omega)


end
end DuplicatePrefix.CurrentCallCheckpointAcceptedBoolFrame
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointAcceptedBoolFrame" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved accepted checkpoint Bool dependency {dependency}"
