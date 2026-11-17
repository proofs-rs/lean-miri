import duplicate_prefix.CurrentCallSpatialRead
import duplicate_prefix.CurrentCallSpatialSourceInstall
import duplicate_prefix.CurrentCallResourceDefaultShared
import duplicate_prefix.CurrentCallSharedConstructorWindow

/-! Default shared construction starts with ONE actual whole-span Read.
Physical Normal is independent of the cell completion used to justify each
row. No one completion owns the whole source request. -/
namespace DuplicatePrefix.CurrentCallSpatialDefaultShared
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

def accessed (tag : BorTag) (start amount : UInt64) := read role.backing.allocation.extra tracker.global.protectedTags tag start amount .VisitChildrenOfAccessed

private theorem normals
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup) (short : role.backing.allocation.extra.nodes.size<65536)
    (tag : BorTag) (concrete : role.family.value.provenance=.concrete role.backing.id tag)
    (parent : UniIndex) (mapped : role.backing.allocation.extra.indexOfTag tag=some parent)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
    (nonzero : amount≠0) (bounds : start.toNat+amount.toNat≤role.backing.allocation.extra.locations.size.bytes.toNat) :
    OwnedOn (fun location=>Nonempty (DuplicatePrefixBorrowAuthorization.Normal (accessed role tag start amount).tree
      location tracker.global.protectedTags parent)) start (start+amount) (accessed role tag start amount).tree.locations := by
  obtain ⟨contract,_,_⟩:=CurrentCallSpatialRead.access_runtime role rfl runtime distinct short start amount startEq amountEq nonzero bounds .VisitChildrenOfAccessed
  have actual : role.backing.allocation.extra.performBorrowAccessRange (CurrentCallSpatialRows.provenance role) (Size.ofBytes start) (Size.ofBytes amount)
      .Read tracker.global.protectedTags .VisitChildrenOfAccessed=accessed role tag start amount := by simp only [CurrentCallSpatialRows.provenance,concrete,accessed,GeneralBorrowRawSharedExpression.read]
  rw [actual] at contract
  have fit : start.toNat+amount.toNat<2^64:=Nat.lt_of_le_of_lt bounds role.backing.allocation.extra.locations.size.bytes.toNat_lt
  have endEq : (start+amount).toNat=offset+length:=by rw [UInt64.toNat_add,Nat.mod_eq_of_lt fit,startEq,amountEq]
  intro cursor valid positive beforeUpper afterLower
  have rowPositive:=(GeneralRangeMapGeometry.facts _ contract.well (by omega)).2.1 cursor valid
  let point:=max start.toNat (accessed role tag start amount).tree.locations.entries[cursor].range.start.toNat
  have pointLower : start.toNat≤point:=Nat.le_max_left _ _
  have rowLower : (accessed role tag start amount).tree.locations.entries[cursor].range.start.toNat≤point:=Nat.le_max_right _ _
  have pointUpper : point<(start+amount).toNat:=by dsimp only [point];omega
  have rowUpper : point<(accessed role tag start amount).tree.locations.entries[cursor].range.stop.toNat:=by dsimp only [point];omega
  have pointFit : point<2^64:=Nat.lt_trans pointUpper (start+amount).toNat_lt
  have pointEq : (UInt64.ofNat point).toNat=point:=by simp only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt pointFit]
  have atPoint : ValueAt (accessed role tag start amount).tree.locations (UInt64.ofNat point) (accessed role tag start amount).tree.locations.entries[cursor].data:=
    ⟨cursor,valid,by rw [pointEq];exact rowLower,by rw [pointEq];exact rowUpper,rfl⟩
  have request : Window role.backing.id offset length (role.backing.id,(UInt64.ofNat point).toNat):=⟨rfl,by rw [pointEq];omega,by rw [pointEq];omega⟩
  obtain ⟨i,cell⟩:=role.covered _ request
  let overlap : CurrentCallSpatialSourceCover.Active role i:=⟨_,request,cell⟩
  have authority:=CurrentCallSpatialRows.recover role _ contract.frames (UInt64.ofNat point)
    (accessed role tag start amount).tree.locations.entries[cursor].data atPoint request i overlap cell
  let W:=CurrentCallSpatialRows.singleByte role i overlap _ request cell
  obtain ⟨G⟩:=geometry_selected W (CandidateCurrentGrantRuntime.tree_rows _ _ runtime) rfl
  have sourceAt:=CurrentCallSpatialRows.source_at role i overlap
  simp only [concrete] at sourceAt
  have sourceMapped : CurrentCallSpatialRows.source role=some parent:=by simp only [CurrentCallSpatialRows.source,concrete,mapped]
  have grant : W.pointer.grant=parent:=Option.some.inj (sourceAt.symm.trans sourceMapped)
  obtain ⟨depth⟩:=W.parents.graph.depth
  have normal:=(spatial_install_rule ".CurrentCallResourceDefaultShared.normal_of_authority") W.allocation.extra W.precise.completion
    (accessed role tag start amount).tree.locations.entries[cursor].data tracker.global.protectedTags W.parents.graph depth W.parents.graph.fits
    G.selectedPosition G.selectedRoot W.pointer.grant G.selectedNode G.selectedSlot G.selectedAt G.sourcePath G.normalAncestry
    (fun index node present _ below=>(authority index node present).1 below)
    (fun index node present _ outside=>(authority index node present).2 outside)
  rw [grant] at normal
  have transport (location : LocationTree)
      (old : Nonempty (DuplicatePrefixBorrowAuthorization.Normal role.backing.allocation.extra location tracker.global.protectedTags parent)) :
      Nonempty (DuplicatePrefixBorrowAuthorization.Normal (accessed role tag start amount).tree location tracker.global.protectedTags parent) := by
    rw [contract.tree_eq]
    obtain ⟨normal⟩:=old
    exact ⟨⟨normal.component,normal.permissions⟩⟩
  exact transport _ normal

/-- Actual associated Read and tag allocation supply whole-span physical Normal
and SAME fixed per-cell interpretations. The physical Normal predicate carries
no single cell completion. -/
theorem prepare
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup) (short : role.backing.allocation.extra.nodes.size<65536)
    (tag : BorTag) (concrete : role.family.value.provenance=.concrete role.backing.id tag)
    (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
    (nonzero : amount≠0) (bounds : start.toNat+amount.toNat≤role.backing.allocation.extra.locations.size.bytes.toNat) :
    ∃parent node,role.backing.allocation.extra.indexOfTag tag=some parent ∧role.backing.allocation.extra.nodes.get parent=some node ∧node.tag=tag ∧
      (accessed role tag start amount).status=.Completed ∧
      DuplicatePrefixBorrowContract.RuntimeFacts (accessed role tag start amount).tree (advanced tracker.global room) ∧
      (accessed role tag start amount).tree.nodes=role.backing.allocation.extra.nodes ∧
      (accessed role tag start amount).tree.roots=role.backing.allocation.extra.roots ∧
      (accessed role tag start amount).tree.tagMapping=role.backing.allocation.extra.tagMapping ∧
      (accessed role tag start amount).tree.locations.size=role.backing.allocation.extra.locations.size ∧
      OwnedOn (fun location=>Nonempty (DuplicatePrefixBorrowAuthorization.Normal (accessed role tag start amount).tree
        location tracker.global.protectedTags parent)) start (start+amount) (accessed role tag start amount).tree.locations ∧
      ∀i : Fin role.backing.cells.size,ParentInterpretation (accessed role tag start amount).tree role.backing.cells[i].completion := by
  have positive : 0<length:=by have p : 0<amount.toNat:=Nat.pos_of_ne_zero (fun zero=>nonzero (UInt64.toNat_inj.mp zero));omega
  obtain ⟨i,cell⟩:=role.covered (role.backing.id,offset) ⟨rfl,by omega,by omega⟩
  let overlap : CurrentCallSpatialSourceCover.Active role i:=⟨(role.backing.id,offset),⟨rfl,by omega,by omega⟩,cell⟩
  obtain ⟨node,present,mapping,binding⟩:=(role.roles i overlap).binding
  simp only [Family.at] at present mapping binding
  rw [concrete] at binding
  have mapped : role.backing.allocation.extra.indexOfTag tag=some (role.roles i overlap).grant:=by rw [binding.2];exact mapping
  obtain ⟨contract,afterRuntime,parents⟩:=CurrentCallSpatialRead.access_runtime role rfl runtime distinct short start amount startEq amountEq nonzero bounds .VisitChildrenOfAccessed
  have actual : role.backing.allocation.extra.performBorrowAccessRange (CurrentCallSpatialRows.provenance role) (Size.ofBytes start) (Size.ofBytes amount)
      .Read tracker.global.protectedTags .VisitChildrenOfAccessed=accessed role tag start amount := by simp only [CurrentCallSpatialRows.provenance,concrete,accessed,GeneralBorrowRawSharedExpression.read]
  rw [actual] at contract afterRuntime parents
  obtain ⟨allocated,allocatedEq,below⟩:=GeneralBorrowForestTagHighWaterHistory.allocate role.backing.allocation.extra tracker.global room runtime.below runtime.formed.allocator.nodeTags false
  have equal : advanced tracker.global room=allocated:=congrArg Prod.fst (Except.ok.inj ((TypedRetagEmpty.allocate_tag tracker.global room).symm.trans allocatedEq))
  rw [←equal] at below
  have nextBelow : GeneralBorrowForestTagHighWater.Below role.backing.allocation.extra (advanced tracker.global room).protectedTags (advanced tracker.global room).nextPointerTag:=by
    simpa only [GeneralBorrowFreshSharedSequence.registered,Bool.false_eq_true,ite_false] using below
  have nextRuntime : DuplicatePrefixBorrowContract.RuntimeFacts (accessed role tag start amount).tree (advanced tracker.global room):=
    ⟨afterRuntime.formed,afterRuntime.coherent,afterRuntime.possible,⟨by rw [contract.tags];exact nextBelow.mapping,nextBelow.protectors⟩⟩
  exact ⟨(role.roles i overlap).grant,node,mapped,present,binding.2.symm,contract.completed,nextRuntime,contract.nodes,contract.roots,contract.tags,contract.capacity,
    normals role runtime distinct short tag concrete _ mapped start amount startEq amountEq nonzero bounds,parents⟩

/-- ONE unprotected Frozen child follows the actual whole-span Read. Its
physical Read capabilities do not require a whole-span cell completion. -/
theorem construct
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup) (short : role.backing.allocation.extra.nodes.size<65536)
    (nodeRoom : role.backing.allocation.extra.nodes.size+1≤4294967295)
    (tag : BorTag) (concrete : role.family.value.provenance=.concrete role.backing.id tag)
    (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
    (nonzero : amount≠0) (bounds : start.toNat+amount.toNat≤role.backing.allocation.extra.locations.size.bytes.toNat) :
    ∃parent node,role.backing.allocation.extra.indexOfTag tag=some parent ∧role.backing.allocation.extra.nodes.get parent=some node ∧node.tag=tag ∧
      (accessed role tag start amount).status=.Completed ∧
      let actual:=child role.backing.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed
      actual.outcome=.ok () ∧DuplicatePrefixBorrowContract.RuntimeFacts actual.tree (advanced tracker.global room) ∧
      actual.tree.locations.size=role.backing.allocation.extra.locations.size ∧actual.tree.nodes.size≤role.backing.allocation.extra.nodes.size+1 ∧
      ∃reader,actual.tree.indexOfTag tracker.global.nextPointerTag=some reader ∧
        OwnedOn (GeneralBorrowSharedReadConstructor.Capabilities actual.tree tracker.global.protectedTags parent reader)
          start (start+amount) actual.tree.locations ∧
        GeneralBorrowFreshActiveWithin.ActiveWithin actual.tree reader .Read start (start+amount) := by
  obtain ⟨parent,node,lookup,present,nodeTag,readDone,readRuntime,nodes,roots,tags,capacity,wholeNormal,parents⟩:=
    prepare role runtime distinct short tag concrete room start amount startEq amountEq nonzero bounds
  let after:=accessed role tag start amount
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
  have caps:=GeneralBorrowSharedCapabilityConstructor.construct after.tree (advanced tracker.global room) readRuntime tag tracker.global.nextPointerTag
    parent node parentTagged parentAt freshAfter nodesRoom tagBound unheld start amount nonzero childBounds wholeNormal
  obtain ⟨reader,readerLookup,both⟩:=caps.2.2.2.2
  obtain ⟨_,activeReader,activeLookup,active⟩:=S05SharedChildActivity.construct after.tree (advanced tracker.global room) readRuntime
    tag tracker.global.nextPointerTag parent node parentTagged parentAt freshAfter nodesRoom tagBound false unheld start amount nonzero childBounds
  have same : activeReader=reader:=Option.some.inj (activeLookup.symm.trans readerLookup)
  subst activeReader
  have readCaps : OwnedOn (GeneralBorrowSharedReadConstructor.Capabilities
      (child role.backing.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed).tree
      tracker.global.protectedTags parent reader) start (start+amount)
      (child role.backing.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed).tree.locations:=by
    intro position valid positive lower upper
    obtain ⟨⟨normal⟩,readCap⟩:=both position valid positive lower upper
    exact ⟨⟨DuplicatePrefixNormalKind.of_normal _ _ _ _ normal .Read⟩,readCap⟩
  refine ⟨parent,node,lookup,present,nodeTag,readDone,caps.1,caps.2.1,caps.2.2.1.trans capacity,?_,reader,readerLookup,readCaps,active⟩
  have growth:=caps.2.2.2.1
  change _≤after.tree.nodes.size+1 at growth
  rw [nodes] at growth
  exact growth

private theorem read_owned
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup) (short : role.backing.allocation.extra.nodes.size<65536)
    (tag : BorTag) (concrete : role.family.value.provenance=.concrete role.backing.id tag)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
    (nonzero : amount≠0) (bounds : start.toNat+amount.toNat≤role.backing.allocation.extra.locations.size.bytes.toNat)
    (i : Fin role.backing.cells.size) (overlap : CurrentCallSpatialSourceCover.Active role i)
    (lower upper : UInt64) (requestLower : offset≤lower.toNat) (requestUpper : upper.toNat≤offset+length)
    (cellLower : role.backing.cells[i].offset≤lower.toNat) (cellUpper : upper.toNat≤role.backing.cells[i].offset+role.backing.cells[i].length) :
    OwnedOn (S05CompletedAncestryReadMutable.Authority (accessed role tag start amount).tree role.backing.cells[i].completion
      tracker.global.protectedTags (role.roles i overlap).grant) lower upper (accessed role tag start amount).tree.locations := by
  obtain ⟨contract,_,_⟩:=CurrentCallSpatialRead.access_runtime role rfl runtime distinct short start amount startEq amountEq nonzero bounds .VisitChildrenOfAccessed
  have actual : role.backing.allocation.extra.performBorrowAccessRange (CurrentCallSpatialRows.provenance role) (Size.ofBytes start) (Size.ofBytes amount)
      .Read tracker.global.protectedTags .VisitChildrenOfAccessed=accessed role tag start amount := by simp only [CurrentCallSpatialRows.provenance,concrete,accessed,GeneralBorrowRawSharedExpression.read]
  rw [actual] at contract
  intro cursor valid positive beforeUpper afterLower
  have rowPositive:=(GeneralRangeMapGeometry.facts _ contract.well (by omega)).2.1 cursor valid
  let point:=max lower.toNat (accessed role tag start amount).tree.locations.entries[cursor].range.start.toNat
  have pointLower : lower.toNat≤point:=Nat.le_max_left _ _
  have rowLower : (accessed role tag start amount).tree.locations.entries[cursor].range.start.toNat≤point:=Nat.le_max_right _ _
  have pointUpper : point<upper.toNat:=by dsimp only [point];omega
  have rowUpper : point<(accessed role tag start amount).tree.locations.entries[cursor].range.stop.toNat:=by dsimp only [point];omega
  have pointFit : point<2^64:=Nat.lt_trans pointUpper upper.toNat_lt
  have pointEq : (UInt64.ofNat point).toNat=point:=by simp only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt pointFit]
  have atPoint : ValueAt (accessed role tag start amount).tree.locations (UInt64.ofNat point) (accessed role tag start amount).tree.locations.entries[cursor].data:=
    ⟨cursor,valid,by rw [pointEq];exact rowLower,by rw [pointEq];exact rowUpper,rfl⟩
  have request : Window role.backing.id offset length (role.backing.id,(UInt64.ofNat point).toNat):=⟨rfl,by rw [pointEq];omega,by rw [pointEq];omega⟩
  have cell : Window role.backing.id role.backing.cells[i].offset role.backing.cells[i].length (role.backing.id,(UInt64.ofNat point).toNat):=⟨rfl,by rw [pointEq];omega,by rw [pointEq];omega⟩
  have raw:=CurrentCallSpatialRows.recover role _ contract.frames (UInt64.ofNat point)
    (accessed role tag start amount).tree.locations.entries[cursor].data atPoint request i overlap cell
  intro index node present
  rw [contract.nodes] at present
  exact raw index node present

/-- Every contained cell subwindow retains its OLD q authority under its SAME
explicit parent map extended by the ONE actual new shared reader. -/
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
          tracker.global.protectedTags parent) lower upper actual.tree.locations := by
  obtain ⟨parent,node,mapped,present,nodeTag,readDone,readRuntime,nodes,roots,tags,capacity,wholeNormal,parents⟩:=
    prepare role runtime distinct short tag concrete room start amount startEq amountEq nonzero bounds
  obtain ⟨otherParent,_,otherMapped,_,_,_,_,_,_,_,reader,readerLookup,_,_⟩:=
    construct role runtime distinct short nodeRoom tag concrete room start amount startEq amountEq nonzero bounds
  have sameParent : otherParent=parent:=Option.some.inj (otherMapped.symm.trans mapped)
  subst otherParent
  refine ⟨parent,reader,mapped,readerLookup,?_⟩
  intro i overlap lower upper requestLower requestUpper cellLower cellUpper
  let after:=accessed role tag start amount
  have raw:=read_owned role runtime distinct short tag concrete start amount startEq amountEq nonzero bounds i overlap lower upper requestLower requestUpper cellLower cellUpper
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
  obtain ⟨_,_,_,_,cellReader,cellLookup,model,retained⟩:=CurrentCallSharedConstructorWindow.construct_window after.tree (advanced tracker.global room)
    role.backing.cells[i].completion readRuntime (parents i) tag tracker.global.nextPointerTag parent node parentTagged parentAt freshAfter nodesRoom tagBound unheld
    start amount nonzero childBounds lower upper actualLower actualUpper primary parentOrder raw
  have sameReader : cellReader=reader:=Option.some.inj (cellLookup.symm.trans readerLookup)
  subst cellReader
  exact ⟨model,retained⟩

/-- The real typed shared-reference expression consumes the internally derived
ONE Read/constructor pair and retains every fixed cell's raw q resources. -/
theorem rvalue
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false)
    (cmp : ProjectionMetadataFacts.NullComparator) (region : Region)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationFuel : options.limits.validation = validityFuel+1)
    (base offset len : UInt64)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (parentTag : BorTag)
    (cover : CurrentCallSpatialCover.Context machine)
    (role : RoleCover machine tracker cover .mut offset.toNat len.toNat)
    (allocationEq : role.backing.allocation = entry.allocation)
    (concrete : role.family.value.provenance = .concrete id parentTag)
    (address : role.family.value.offset.bytes=base+offset)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup) (short : role.backing.allocation.extra.nodes.size < 65536)
    (nodeRoom : role.backing.allocation.extra.nodes.size+1 ≤ 4294967295)
    (bounds : offset.toNat+len.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat)
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (validSource : (1 : MIR.LocalId) < frame.locals.size) (validDest : (RootReferenceFacts.destination true) < frame.locals.size)
    (sourceLive : frame.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      role.family.value len ActualReferenceMetadata.reference).imm))
    (sourceCached : frame.locals[1].layout = some ActualReferenceMetadata.reference)
    (destLive : frame.locals[(RootReferenceFacts.destination true)].value = .live (.immediate .uninit))
    (destUncached : frame.locals[(RootReferenceFacts.destination true)].layout = none)
    (body : frame.body=RootBody.reflected.body.body)
    (identity : frame.bodyIdentity=RootBody.reflected.body.identity)
    (callee : frame.functionInstance=RootBody.reflected.functionInstance)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine))) :
    let inner := config options remaining span
    let value := RetagReferencePlace.sliceValue inner.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len (layout true)
    let resultMachine := {ReferenceBorrowDriver.allocatedMachine machine tracker fresh with
      memory := RetagEntry.updatedMemory machine.memory id entry (child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree}
    evalRvalueIntoPlace (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      (.Ref region (RootReferenceRvalue.borrowKind true) ⟨1,#[.Deref]⟩) ⟨(RootReferenceFacts.destination true),#[]⟩ (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames (ActualLocalCopy.written frame (RootReferenceFacts.destination true) (layout true) validDest value.imm) resultMachine) ∧
      let actual:=child role.backing.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed
      ∃parent reader,role.backing.allocation.extra.indexOfTag parentTag=some parent ∧actual.tree.indexOfTag tracker.global.nextPointerTag=some reader ∧
        ∀(i : Fin role.backing.cells.size) (overlap : CurrentCallSpatialSourceCover.Active role i) (lower upper : UInt64),
          offset.toNat≤lower.toNat→upper.toNat≤offset.toNat+len.toNat→role.backing.cells[i].offset≤lower.toNat→upper.toNat≤role.backing.cells[i].offset+role.backing.cells[i].length→
          ParentInterpretation actual.tree (S05ConcreteProtectedChildCompletion.extend role.backing.cells[i].completion reader parent) ∧
          OwnedOn (S05CompletedAncestryReadMutable.Authority actual.tree (S05ConcreteProtectedChildCompletion.extend role.backing.cells[i].completion reader parent)
            tracker.global.protectedTags parent) lower upper actual.tree.locations := by
  have lenNonzero : len≠0:=by intro zero;rw [zero] at positive;cases positive
  have positiveNat : 0<len.toNat:=UInt64.lt_iff_toNat_lt.mp positive
  obtain ⟨i,cell⟩:=role.covered (role.backing.id,offset.toNat) ⟨rfl,by omega,by omega⟩
  let overlap : CurrentCallSpatialSourceCover.Active role i:=⟨_,⟨rfl,by omega,by omega⟩,cell⟩
  obtain ⟨node,_,_,binding⟩:=(role.roles i overlap).binding
  simp only [Family.at] at binding
  rw [concrete] at binding
  have idEq : id=role.backing.id:=binding.1.trans role.id
  have concreteRole : role.family.value.provenance=.concrete role.backing.id parentTag:=by rw [←idEq];exact concrete
  have pointerEq : role.family.value=Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset)):=by
    have value:=role.family.value
    cases valueEq : role.family.value with
    | mk position provenance =>
      simp only [valueEq] at concrete address
      cases position
      simp only [Pointer.new, Size.ofBytes]
      simp_all
  rw [pointerEq] at sourceLive
  have roleBounds : offset.toNat+len.toNat≤role.backing.allocation.extra.locations.size.bytes.toNat:=by rw [allocationEq];exact bounds
  obtain ⟨parent,node,mapped,parentPresent,nodeTag,readDone,sharedDone,_,_,_,reader,readerLookup,_,_⟩:=
    construct role runtime distinct short nodeRoom parentTag concreteRole fresh offset len rfl rfl lenNonzero roleBounds
  change (read role.backing.allocation.extra tracker.global.protectedTags parentTag offset len .VisitChildrenOfAccessed).status=.Completed at readDone
  rw [allocationEq] at readDone sharedDone
  have query:=RootReferenceFacts.compute_destination frames frame machine body identity callee true
  have absent:=DuplicatePrefixTypeCacheOrigins.slice_not_constructed (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)) metadata origins
  have evaluated:=CurrentCallSharedReference.rvalue_of_steps options limits remaining span ctx debugOff cmp region dynamicFuel validityFuel fuelEq validationFuel
    base offset len id entry positive nonzero signedFits frames frame machine tracker enabled defaultMode fresh parentTag bounds readDone sharedDone capacity
    (RootReferenceFacts.destination true) (by decide) validSource validDest sourceLive sourceCached destLive destUncached query noClocks ghost shallow cachedAddress present race metadata absent
  exact ⟨evaluated,cells role runtime distinct short nodeRoom parentTag concreteRole fresh offset len rfl rfl lenNonzero roleBounds⟩

end
end DuplicatePrefix.CurrentCallSpatialDefaultShared

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallSpatialDefaultShared" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved spatial shared dependency {dependency}"
