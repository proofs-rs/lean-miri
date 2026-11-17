import duplicate_prefix.CurrentCallSpatialDefaultShared
import duplicate_prefix.CurrentCallSpatialObserverRead
import duplicate_prefix.CurrentCallSpatialEntryRead

/-! Mutable-resource associated Read over a fixed spatial cover. The actual
range fold is unchanged; all saved original rows and intersecting cell parent
maps are retained together, independently of interpreter row splitting. -/
namespace DuplicatePrefix.CurrentCallSpatialLenAssociatedRead
open Miri Miri.ABI Miri.Memory Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization CurrentCallSpatialCover CurrentCallSpatialRows
open GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowProjection
open GeneralRangeMapOrigins GeneralRangeMapState GeneralBorrowExposedConditionalRangeFrames
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

theorem prepare {before tracker ctx mode offset length}
    (role : RoleCover before tracker ctx mode offset length)
    (exclusive : demandOf mode=.exclusive)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup)
    (short : role.backing.allocation.extra.nodes.size<65536)
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
    let current := CurrentCallSpatialEntryRead.registeredRole role runtime {} room
    let actual := role.backing.allocation.extra.performBorrowAccessRange (.concrete readerNode.tag) (Size.ofBytes start) (Size.ofBytes amount)
      .Read registered.global.protectedTags visit
    GeneralBorrowConcreteRangeInvariant.Contract role.backing.allocation.extra
      (fun location => Nonempty (DuplicatePrefixNormalKind.Capability role.backing.allocation.extra location registered.global.protectedTags reader .Read))
      (fun location => GeneralBorrowExposureCardinality.LocationCoherent role.backing.allocation.extra location registered.global.protectedTags ∧
        GeneralBorrowLocationSifaConsistency.Profile role.backing.allocation.extra location registered.global.protectedTags ∧
        GeneralBorrowSnapshotReadRuntime.GlobalPossible role.backing.allocation.extra location)
      (Frame current) start (start+amount) actual ∧
    DuplicatePrefixBorrowContract.RuntimeFacts actual.tree registered.global ∧
    ∀ i : Fin role.backing.cells.size, ParentInterpretation actual.tree role.backing.cells[i].completion := by
  obtain ⟨_,_,_,currentRuntime,nodeFresh,_⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare
    role.backing.allocation.extra tracker.global {} role.backing.id room runtime
  let next := CurrentCallSpatialEntryRead.registeredTracker role {} room
  let current := CurrentCallSpatialEntryRead.registeredRole role runtime {} room
  have flags : ∀ index node, role.backing.allocation.extra.nodes.get index=some node →
      next.global.protectedTags.contains node.tag=tracker.global.protectedTags.contains node.tag := by
    intro index node present
    exact ProtectorInsertion.contains_other tracker.global.protectedTags tracker.global.nextPointerTag node.tag .StrongProtector
      (nodeFresh (index,node) (Array.mem_toList_iff.mp ((GeneralBorrowFreshReuseProtection.entries_get _ index node).mpr present)))
  obtain ⟨position,root,rootNode,slot,rootAt,path⟩ := CandidateCurrentWindowAuthority.root_path
    role.backing.allocation.extra runtime.formed.toGraphState reader readerNode readerAt
  obtain ⟨rootActual,rootPresent,parentless⟩ := runtime.formed.toGraphState.rootNodes root (Array.mem_toList_iff.mpr (Array.mem_of_getElem? slot))
  have same := Option.some.inj (rootPresent.symm.trans rootAt)
  subst rootActual
  have currentReadable : OwnedOn (fun location => Nonempty (DuplicatePrefixNormalKind.Capability
      role.backing.allocation.extra location next.global.protectedTags reader .Read)) start (start+amount) role.backing.allocation.extra.locations := by
    intro cursor valid positive beforeUpper afterLower
    obtain ⟨capability⟩ := readable cursor valid positive beforeUpper afterLower
    apply GeneralBorrowPhysicalNormalCapability.of_physical_component role.backing.allocation.extra _ next.global.protectedTags
      runtime.formed.toGraphState runtime.formed.fits root reader rootNode rootAt parentless path .Read
    intro index node present component
    rw [flags index node present]
    exact (spatial_install_rule ".CurrentCallOptionalLenAssociatedRead.capability_selected") role.backing.allocation.extra _
      tracker.global.protectedTags runtime.formed.toGraphState root reader path capability index node present component
  have currentUnheld : next.global.protectedTags.contains readerNode.tag=false := (flags reader readerNode readerAt).trans unheld
  exact CurrentCallSpatialObserverRead.access_runtime current exclusive currentRuntime distinct short
    parentTag parent reader readerNode concrete tagged readerAt readerEdge hidden currentUnheld
    start amount startEq amountEq nonzero bounds currentReadable visit

theorem subwindow {before tracker ctx mode offset length}
    (role : RoleCover before tracker ctx mode offset length)
    (exclusive : demandOf mode=.exclusive)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup)
    (short : role.backing.allocation.extra.nodes.size<65536)
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
    (visit : ChildrenVisitMode)
    (i : Fin role.backing.cells.size) (overlap : CurrentCallSpatialSourceCover.Active role i)
    (lower upper : UInt64) (requestLower : offset≤lower.toNat) (requestUpper : upper.toNat≤offset+length)
    (cellLower : role.backing.cells[i].offset≤lower.toNat)
    (cellUpper : upper.toNat≤role.backing.cells[i].offset+role.backing.cells[i].length) :
    let registered := CurrentCallSpatialEntryRead.registeredTracker role {} room
    let actual := role.backing.allocation.extra.performBorrowAccessRange (.concrete readerNode.tag) (Size.ofBytes start) (Size.ofBytes amount)
      .Read registered.global.protectedTags visit
    OwnedOn (S05CompletedAncestryReadMutable.Authority actual.tree role.backing.cells[i].completion
      (registered.global.endCall (({} : FrameState).addProtector role.backing.id tracker.global.nextPointerTag)).protectedTags parent)
      lower upper actual.tree.locations := by
  obtain ⟨contract,afterRuntime,parents⟩ := prepare role exclusive runtime distinct short parentTag parent reader readerNode
    concrete tagged readerAt readerEdge hidden unheld room start amount startEq amountEq nonzero bounds readable visit
  let registered := CurrentCallSpatialEntryRead.registeredTracker role {} room
  let current := CurrentCallSpatialEntryRead.registeredRole role runtime {} room
  let actual := role.backing.allocation.extra.performBorrowAccessRange (.concrete readerNode.tag) (Size.ofBytes start) (Size.ofBytes amount)
    .Read registered.global.protectedTags visit
  have sourceAt := CurrentCallSpatialRows.source_at role i overlap
  simp only [concrete] at sourceAt
  have grantEq : (role.roles i overlap).grant=parent := by
    have look : CurrentCallSpatialRows.source role=some parent := by simp only [CurrentCallSpatialRows.source,concrete];exact tagged
    exact Option.some.inj (sourceAt.symm.trans look)
  have freshNode := (GeneralBorrowFnEntryRegistrationRuntime.prepare role.backing.allocation.extra tracker.global {} role.backing.id room runtime).2.2.2.2.1
  change OwnedOn (S05CompletedAncestryReadMutable.Authority actual.tree role.backing.cells[i].completion
    (registered.global.endCall (({} : FrameState).addProtector role.backing.id tracker.global.nextPointerTag)).protectedTags parent)
    lower upper actual.tree.locations
  intro cursor valid positive beforeUpper afterLower
  have well : actual.tree.locations.WellFormed := contract.well
  have rowPositive := (GeneralRangeMapGeometry.facts _ well (by omega)).2.1 cursor valid
  let point := max lower.toNat actual.tree.locations.entries[cursor].range.start.toNat
  have pointLower : lower.toNat≤point := Nat.le_max_left _ _
  have rowLower : actual.tree.locations.entries[cursor].range.start.toNat≤point := Nat.le_max_right _ _
  have pointUpper : point<upper.toNat := by dsimp only [point];omega
  have rowUpper : point<actual.tree.locations.entries[cursor].range.stop.toNat := by dsimp only [point];omega
  have pointFit : point<2^64 := Nat.lt_trans pointUpper upper.toNat_lt
  have pointEq : (UInt64.ofNat point).toNat=point := by simp only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt pointFit]
  have atPoint : ValueAt actual.tree.locations (UInt64.ofNat point) actual.tree.locations.entries[cursor].data :=
    ⟨cursor,valid,by rw [pointEq];exact rowLower,by rw [pointEq];exact rowUpper,rfl⟩
  have request : Window role.backing.id offset length (role.backing.id,(UInt64.ofNat point).toNat) :=
    ⟨rfl,by rw [pointEq];omega,by rw [pointEq];omega⟩
  have cell : Window role.backing.id role.backing.cells[i].offset role.backing.cells[i].length (role.backing.id,(UInt64.ofNat point).toNat) :=
    ⟨rfl,by rw [pointEq];omega,by rw [pointEq];omega⟩
  have raw := CurrentCallSpatialRows.recover current _ contract.frames (UInt64.ofNat point)
    actual.tree.locations.entries[cursor].data atPoint request i overlap cell
  change S05CompletedAncestryReadMutable.Authority role.backing.allocation.extra role.backing.cells[i].completion
    registered.global.protectedTags (role.roles i overlap).grant actual.tree.locations.entries[cursor].data at raw
  rw [grantEq] at raw
  intro index node present
  rw [contract.nodes] at present
  have fresh : node.tag≠tracker.global.nextPointerTag := freshNode (index,node)
    (Array.mem_toList_iff.mp ((GeneralBorrowFreshReuseProtection.entries_get _ index node).mpr present))
  rw [(spatial_install_rule ".CurrentCallOptionalLenAssociatedRead.end_flags") registered.global role.backing.id tracker.global.nextPointerTag node.tag (.inr fresh)]
  have result := raw index node present
  exact result

end
end DuplicatePrefix.CurrentCallSpatialLenAssociatedRead
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallSpatialLenAssociatedRead" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved spatial Len associated Read dependency {dependency}"
