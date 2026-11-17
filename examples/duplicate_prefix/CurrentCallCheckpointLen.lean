import duplicate_prefix.CurrentCallSpatialLenFuture
import duplicate_prefix.CurrentCallCheckpointShared
import duplicate_prefix.CurrentCallSpatialLenAssociatedRead
import duplicate_prefix.CurrentCallSpatialEntryRead

/-! Mutable-resource associated Read over a fixed spatial cover. The actual
range fold is unchanged; all saved original rows and intersecting cell parent
maps are retained together, independently of interpreter row splitting. -/
namespace DuplicatePrefix.CurrentCallCheckpointLen
open Miri Miri.ABI Miri.Memory Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization CurrentCallSpatialCover CurrentCallSpatialRows
open GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowProjection
open GeneralRangeMapOrigins GeneralRangeMapState GeneralBorrowExposedConditionalRangeFrames
set_option autoImplicit false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

theorem invoke {before tracker ctx mode offset length}
    (role : RoleCover before tracker ctx mode offset length)
    (exclusive : demandOf mode=.exclusive)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup)
    (short : role.backing.allocation.extra.nodes.size<65536)
    (nodeRoom : role.backing.allocation.extra.nodes.size+1≤4294967295)
    (parentTag : BorTag) (parent reader : UniIndex) (readerNode : TreeNode)
    (concrete : role.family.value.provenance=.concrete role.backing.id parentTag)
    (tagged : role.backing.allocation.extra.indexOfTag parentTag=some parent)
    (readerAt : role.backing.allocation.extra.nodeAt reader=some readerNode)
    (readerEdge : readerNode.parent=some parent) (hidden : readerNode.isExposed=false)
    (unheld : tracker.global.protectedTags.contains readerNode.tag=false)
    (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
    (nonzero : amount ≠ 0)
    (bounds : start.toNat+amount.toNat≤role.backing.allocation.extra.locations.size.bytes.toNat)
    (readable : OwnedOn (fun location => Nonempty (DuplicatePrefixNormalKind.Capability
      role.backing.allocation.extra location tracker.global.protectedTags reader .Read)) start (start+amount) role.backing.allocation.extra.locations)
    (visit : ChildrenVisitMode) :
    let registered := CurrentCallSpatialEntryRead.registeredTracker role {} room
    let accessed := role.backing.allocation.extra.performBorrowAccessRange (.concrete readerNode.tag) (Size.ofBytes start) (Size.ofBytes amount)
      .Read registered.global.protectedTags visit
    let actual := accessed.tree.newChild (Size.ofBytes start) (.concrete readerNode.tag) tracker.global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes amount) GeneralBorrowFreshAnchor.sharedState) .Frozen true
    accessed.status=.Completed ∧actual.outcome=.ok () ∧DuplicatePrefixBorrowContract.RuntimeFacts actual.tree registered.global ∧
    actual.tree.locations.size=role.backing.allocation.extra.locations.size ∧actual.tree.nodes.size≤role.backing.allocation.extra.nodes.size+1 ∧
    ∃helper,actual.tree.indexOfTag tracker.global.nextPointerTag=some helper ∧
      OwnedOn (GeneralBorrowSharedReadConstructor.Capabilities actual.tree registered.global.protectedTags reader helper)
        start (start+amount) actual.tree.locations ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin actual.tree helper .Read start (start+amount) ∧
      ∀(i : Fin role.backing.cells.size) (overlap : CurrentCallSpatialSourceCover.Active role i) (lower upper : UInt64),
        offset≤lower.toNat→upper.toNat≤offset+length→role.backing.cells[i].offset≤lower.toNat→upper.toNat≤role.backing.cells[i].offset+role.backing.cells[i].length→
        ParentInterpretation actual.tree (S05ConcreteProtectedChildCompletion.extend role.backing.cells[i].completion helper reader) ∧
        OwnedOn (S05CompletedAncestryReadMutable.Authority actual.tree (S05ConcreteProtectedChildCompletion.extend role.backing.cells[i].completion helper reader)
          (registered.global.endCall (({} : FrameState).addProtector role.backing.id tracker.global.nextPointerTag)).protectedTags parent)
          lower upper actual.tree.locations := by
  obtain ⟨readDone,childDone,afterRuntime,capacity,growth,helper,lookup,capabilities,active⟩ :=
    CurrentCallSpatialLenConstructor.construct role exclusive runtime distinct short nodeRoom parentTag parent reader readerNode concrete tagged readerAt readerEdge hidden unheld room start amount startEq amountEq nonzero bounds readable visit
  obtain ⟨cellHelper,cellLookup,cells⟩ := CurrentCallSpatialLenFuture.cells role exclusive runtime distinct short nodeRoom parentTag parent reader readerNode concrete tagged readerAt readerEdge hidden unheld room start amount startEq amountEq nonzero bounds readable visit
  have same : cellHelper=helper := Option.some.inj (cellLookup.symm.trans lookup)
  subst cellHelper
  exact ⟨readDone,childDone,afterRuntime,capacity,growth,helper,lookup,capabilities,active,cells⟩


open CurrentCallPostEntryCheckpoint
/-- Derived logical inputs at the SAME installed Default-shared world. -/
structure Prepared {options remaining span len count place}
    (cp : Checkpoint options remaining span len count place) where
  context : CurrentCallSpatialCover.Context (CurrentCallCheckpointShared.machine cp)
  source : RoleCover (CurrentCallCheckpointShared.machine cp) (CurrentCallCheckpointShared.tracker cp) context .mut
    (UInt64.ofNat cp.offset).toNat len.toNat
  tree : source.backing.allocation.extra=CurrentCallCheckpointShared.tree cp
  family : source.family=(CurrentCallCheckpointShared.role cp).family
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts source.backing.allocation.extra (CurrentCallCheckpointShared.tracker cp).global
  distinct : source.backing.allocation.extra.roots.toList.Nodup
  short : source.backing.allocation.extra.nodes.size<65536
  nodeRoom : source.backing.allocation.extra.nodes.size+1≤4294967295
  reader : UniIndex
  readerNode : TreeNode
  concrete : source.family.value.provenance=.concrete source.backing.id cp.source.tag
  tagged : source.backing.allocation.extra.indexOfTag cp.source.tag=some cp.source.grant
  readerAt : source.backing.allocation.extra.nodeAt reader=some readerNode
  readerTag : readerNode.tag=cp.tracker.global.nextPointerTag
  readerEdge : readerNode.parent=some cp.source.grant
  hidden : readerNode.isExposed=false
  unheld : (CurrentCallCheckpointShared.tracker cp).global.protectedTags.contains readerNode.tag=false
  room : (CurrentCallCheckpointShared.tracker cp).global.nextPointerTag.value<18446744073709551615
  bounds : (UInt64.ofNat cp.offset).toNat+len.toNat≤source.backing.allocation.extra.locations.size.bytes.toNat
  readable : OwnedOn (fun location=>Nonempty (DuplicatePrefixNormalKind.Capability source.backing.allocation.extra location
    (CurrentCallCheckpointShared.tracker cp).global.protectedTags reader .Read)) (UInt64.ofNat cp.offset) (UInt64.ofNat cp.offset+len) source.backing.allocation.extra.locations

theorem from_shared {options remaining span len count place}
    (cp : Checkpoint options remaining span len count place) : Nonempty (Prepared cp) := by
  obtain ⟨context,Q,family,allocation,idEq,parent,other,_,_,original,cells⟩:=CurrentCallCheckpointShared.installed cp
  have treeEq : Q.backing.allocation.extra=CurrentCallCheckpointShared.tree cp := congrArg Allocation.extra allocation
  obtain ⟨readDone,childDone,runtime,capacity,growth,reader,lookup,capabilities,active⟩:=CurrentCallCheckpointShared.operation cp
  obtain ⟨otherReader,node,otherLookup,nodeAt,nodeTag,nodeParent,nodeHidden,roots,qNode,qActivity,oldFields⟩:=CurrentCallCheckpointShared.metadata cp
  have same : otherReader=reader:=Option.some.inj (otherLookup.symm.trans lookup)
  subst otherReader
  obtain ⟨qChanged,qAt,qTag,qParent,qHidden⟩:=qNode
  have qMapped : (CurrentCallCheckpointShared.tree cp).indexOfTag cp.source.tag=some cp.source.grant := by
    rw [←cp.source.nodeTag,←qTag]
    exact runtime.formed.allocator.nodeTags _ _ qAt
  have nextEq : (CurrentCallCheckpointShared.tracker cp).global.nextPointerTag.value.toNat=cp.tracker.global.nextPointerTag.value.toNat+1 := by
    exact GenericFunctionEntryNumerics.successor_value _ (CurrentCallCheckpointShared.room cp)
  have fresh : (CurrentCallCheckpointShared.tracker cp).global.nextPointerTag.value<18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    change (CurrentCallCheckpointShared.tracker cp).global.nextPointerTag.value.toNat<18446744073709551615
    have margin:=cp.tags
    omega
  have short : Q.backing.allocation.extra.nodes.size<65536 := by
    rw [treeEq]
    have old:=cp.source.nodes
    change (CurrentCallCheckpointShared.role cp).backing.allocation.extra.nodes.size+6<65536 at old
    omega
  have roomNodes : Q.backing.allocation.extra.nodes.size+1≤4294967295 := by omega
  refine ⟨{ context := context
            source := Q
            tree := treeEq
            family := family
            runtime := ?_
            distinct := ?_
            short := short
            nodeRoom := roomNodes
            reader := reader
            readerNode := node
            concrete := ?_
            tagged := ?_
            readerAt := ?_
            readerTag := nodeTag
            readerEdge := nodeParent
            hidden := nodeHidden
            unheld := ?_
            room := fresh
            bounds := ?_
            readable := ?_ }⟩
  · rw [treeEq];exact runtime
  · rw [treeEq,roots];exact cp.source.distinct
  · rw [family,idEq];exact cp.source.concrete
  · rw [treeEq];exact qMapped
  · rw [treeEq];exact nodeAt
  · rw [nodeTag];exact CurrentCallCheckpointShared.reader_unheld cp
  · rw [treeEq,capacity];exact CurrentCallCheckpointShared.bounds cp
  · rw [treeEq]
    intro position valid positive lower upper
    exact (capabilities position valid positive lower upper).2

/-- Select the installed logical packet once; all later cells use this SAME
actual role and reader, never a fresh per-byte interpretation. -/
def prepared {options remaining span len count place}
    (cp : Checkpoint options remaining span len count place) : Prepared cp := Classical.choice (from_shared cp)

theorem operations {options remaining span len count place}
    (cp : Checkpoint options remaining span len count place) :
    let registered := CurrentCallSpatialEntryRead.registeredTracker (prepared cp).source {} (prepared cp).room
    let accessed := (prepared cp).source.backing.allocation.extra.performBorrowAccessRange (.concrete (prepared cp).readerNode.tag) (Size.ofBytes (UInt64.ofNat cp.offset)) (Size.ofBytes len)
      .Read registered.global.protectedTags .VisitChildrenOfAccessed
    let actual := accessed.tree.newChild (Size.ofBytes (UInt64.ofNat cp.offset)) (.concrete (prepared cp).readerNode.tag) (CurrentCallCheckpointShared.tracker cp).global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen true
    accessed.status=.Completed ∧actual.outcome=.ok () ∧DuplicatePrefixBorrowContract.RuntimeFacts actual.tree registered.global ∧
    actual.tree.locations.size=(prepared cp).source.backing.allocation.extra.locations.size ∧actual.tree.nodes.size≤(prepared cp).source.backing.allocation.extra.nodes.size+1 ∧
    ∃helper,actual.tree.indexOfTag (CurrentCallCheckpointShared.tracker cp).global.nextPointerTag=some helper ∧
      OwnedOn (GeneralBorrowSharedReadConstructor.Capabilities actual.tree registered.global.protectedTags (prepared cp).reader helper)
        (UInt64.ofNat cp.offset) ((UInt64.ofNat cp.offset)+len) actual.tree.locations ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin actual.tree helper .Read (UInt64.ofNat cp.offset) ((UInt64.ofNat cp.offset)+len) ∧
      ∀(i : Fin (prepared cp).source.backing.cells.size) (overlap : CurrentCallSpatialSourceCover.Active (prepared cp).source i) (lower upper : UInt64),
        (UInt64.ofNat cp.offset).toNat≤lower.toNat→upper.toNat≤(UInt64.ofNat cp.offset).toNat+len.toNat→(prepared cp).source.backing.cells[i].offset≤lower.toNat→upper.toNat≤(prepared cp).source.backing.cells[i].offset+(prepared cp).source.backing.cells[i].length→
        ParentInterpretation actual.tree (S05ConcreteProtectedChildCompletion.extend (prepared cp).source.backing.cells[i].completion helper (prepared cp).reader) ∧
        OwnedOn (S05CompletedAncestryReadMutable.Authority actual.tree (S05ConcreteProtectedChildCompletion.extend (prepared cp).source.backing.cells[i].completion helper (prepared cp).reader)
          (registered.global.endCall (({} : FrameState).addProtector (prepared cp).source.backing.id (CurrentCallCheckpointShared.tracker cp).global.nextPointerTag)).protectedTags cp.source.grant)
          lower upper actual.tree.locations :=
  invoke (prepared cp).source rfl (prepared cp).runtime (prepared cp).distinct (prepared cp).short (prepared cp).nodeRoom
    cp.source.tag cp.source.grant (prepared cp).reader (prepared cp).readerNode
    (prepared cp).concrete (prepared cp).tagged (prepared cp).readerAt (prepared cp).readerEdge (prepared cp).hidden
    (prepared cp).unheld (prepared cp).room (UInt64.ofNat cp.offset) len rfl rfl
    (by intro zero;have positive:=cp.source.positive;rw [zero] at positive;cases positive)
    (prepared cp).bounds (prepared cp).readable .VisitChildrenOfAccessed

end
end DuplicatePrefix.CurrentCallCheckpointLen
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointLen" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved checkpoint Len dependency {dependency}"
