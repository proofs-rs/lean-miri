import duplicate_prefix.CurrentCallCheckpointSharedBoolFrame
import duplicate_prefix.S02HiddenLeafQuietTreeAccess
import duplicate_prefix.CurrentCallSpatialEntryRead
import duplicate_prefix.CurrentCallProtectedConstructorOldFacets
import duplicate_prefix.CurrentCallDefaultMutableDisjoint
import duplicate_prefix.CurrentCallResourceDefaultMutable
import duplicate_prefix.GeneralBorrowRawDefaultExpression

namespace DuplicatePrefix.CurrentCallCheckpointMutableBoolFrame
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall OrdinaryBorrowAuthority CurrentCallResourceNormalization
open GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowWildcardParentTagOrder
open GeneralBorrowView GeneralBorrowFreshGraph GeneralBorrowProjection GeneralRangeMapOrigins
open S05ConcreteProtectedChildCompletion S05CompletedAncestryReadMutable
open GeneralBorrowFreshActiveWithin GeneralRangeMapState GeneralBorrowProjection BorrowRangeAccess GeneralBorrowExposureCardinality
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- Physical capabilities are recovered per original row from its fixed cell. -/
theorem spatial_normal {before tracker ctx offset length}
    (role : CurrentCallSpatialCover.RoleCover before tracker ctx .mut offset length)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (tag : BorTag) (parent : UniIndex)
    (concrete : role.family.value.provenance=.concrete role.backing.id tag)
    (mapped : role.backing.allocation.extra.indexOfTag tag=some parent)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
    (bounds : start.toNat+amount.toNat≤role.backing.allocation.extra.locations.size.bytes.toNat) :
    OwnedOn (fun location=>Nonempty (DuplicatePrefixBorrowAuthorization.Normal role.backing.allocation.extra
      location tracker.global.protectedTags parent)) start (start+amount) role.backing.allocation.extra.locations := by
  have fit : start.toNat+amount.toNat<2^64 := Nat.lt_of_le_of_lt bounds role.backing.allocation.extra.locations.size.bytes.toNat_lt
  have endEq : (start+amount).toNat=offset+length := by
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt fit,startEq,amountEq]
  intro cursor valid positive beforeUpper afterLower
  let segment := role.backing.allocation.extra.locations.entries[cursor]
  have rowPositive := (GeneralRangeMapGeometry.facts _ runtime.formed.well (by omega)).2.1 cursor valid
  let point := max start.toNat segment.range.start.toNat
  have pointLower : start.toNat≤point := Nat.le_max_left _ _
  have rowLower : segment.range.start.toNat≤point := Nat.le_max_right _ _
  have pointUpper : point<(start+amount).toNat := by dsimp only [point]; dsimp only [segment] at *;omega
  have rowUpper : point<segment.range.stop.toNat := by dsimp only [point]; dsimp only [segment] at *;omega
  have request : CandidateStableCallOwnership.Window role.backing.id offset length (role.backing.id,point) := ⟨rfl,by omega,by omega⟩
  obtain ⟨i,cell⟩ := role.covered _ request
  let overlap : CurrentCallSpatialSourceCover.Active role i := ⟨_,request,cell⟩
  let W := CurrentCallSpatialRows.singleByte role i overlap _ request cell
  obtain ⟨G⟩ := geometry_selected W (CandidateCurrentGrantRuntime.tree_rows _ _ runtime) rfl
  have inside := CurrentCallSpatialRows.singleByte_inside role i overlap _ request cell
  have sourceAt := CurrentCallSpatialRows.source_at role i overlap
  simp only [concrete] at sourceAt
  have sourceMapped : CurrentCallSpatialRows.source role=some parent := by
    simp only [CurrentCallSpatialRows.source,concrete,mapped]
  have grant : W.pointer.grant=parent := Option.some.inj (sourceAt.symm.trans sourceMapped)
  have member : segment∈role.backing.allocation.extra.locations.entries.toList :=
    Array.mem_toList_iff.mpr (Array.getElem_mem valid)
  obtain ⟨normal⟩ := CurrentCallResourceAccess.selected_normal W G rfl _ inside segment member rowLower rowUpper
    (runtime.formed.profile cursor valid) (runtime.possible cursor valid)
  rw [grant] at normal
  exact ⟨normal⟩

/-- Actual Default mutable construction frames an independent bank. Its
optional completion supplies no source ownership premise. -/
theorem constructor (tree : BorrowTree) (global : GlobalState) (C : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (parents : ParentInterpretation tree C)
    (parentTag newTag : BorTag) (parent target : UniIndex) (parentNode targetNode : TreeNode)
    (tagged : tree.indexOfTag parentTag=some parent) (present : tree.nodeAt parent=some parentNode)
    (targetAt : tree.nodeAt target=some targetNode) (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag)
    (room : tree.nodes.size+1≤4294967295) (tagBound : newTag.value.toNat<global.nextPointerTag.value.toNat)
    (unheld : global.protectedTags.contains newTag=false)
    (start amount lower upper : UInt64) (nonzero : amount≠0)
    (bounds : start.toNat+amount.toNat≤tree.locations.size.bytes.toNat)
    (apart : ∀point : UInt64,lower.toNat≤point.toNat→point.toNat<upper.toNat→point.toNat<start.toNat∨(start+amount).toNat≤point.toNat)
    (primaryLive : ∃node,tree.nodes.get allocationRoot=some node) (parentOrder : parentNode.tag.value≤newTag.value)
    (owned : OwnedOn (Authority tree C global.protectedTags target) lower upper tree.locations) :
    let actual := tree.newChild (Size.ofBytes start) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes amount) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false
    actual.outcome=.ok () ∧DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global ∧
      actual.tree.locations.size=tree.locations.size ∧actual.tree.nodes.size≤tree.nodes.size+1 ∧
      ∃child,actual.tree.indexOfTag newTag=some child ∧LeafFrame tree actual.tree child parent ∧
        ParentInterpretation actual.tree (extend C child parent) ∧
        OwnedOn (Authority actual.tree (extend C child parent) global.protectedTags target) lower upper actual.tree.locations ∧
        (∀query old,tree.nodeAt query=some old→∃next,actual.tree.nodeAt query=some next ∧next.tag=old.tag ∧next.parent=old.parent ∧
          next.isExposed=old.isExposed ∧next.defaultInitialPermission=old.defaultInitialPermission) := by
  obtain ⟨done,nextRuntime,capacity,growth,child,lookup,frame,nextParents,ancestry,defaults⟩ :=
    (checkpoint_bool_rule "CurrentCallResourceDefaultMutable.completion_construct") tree global C runtime parents parentTag newTag parent parentNode
      tagged present fresh room tagBound unheld start amount nonzero bounds primaryLive parentOrder
  obtain ⟨_,_,_,_,framedChild,framedLookup,framed⟩ := CurrentCallDefaultMutableDisjoint.disjoint tree global C runtime parents
    parentTag newTag parent target parentNode targetNode tagged present targetAt fresh room tagBound unheld start amount lower upper nonzero bounds apart owned
  have same : framedChild=child := Option.some.inj (framedLookup.symm.trans lookup)
  subst framedChild
  refine ⟨done,nextRuntime,capacity,growth,child,lookup,frame,nextParents,framed,?_⟩
  intro query old atOld
  obtain ⟨next,nextAt,tag,parent,hidden⟩ := frame.old query old atOld
  obtain ⟨other,otherAt,permission⟩ := defaults query old atOld
  have equal : other=next := Option.some.inj (otherAt.symm.trans nextAt)
  exact ⟨next,nextAt,tag,parent,hidden,equal ▸ permission⟩

/-- Actual Strong mutable constructor preserves only the independent target
bank; source authority in that bank's interpretation is not required. -/
theorem strong_constructor (tree : BorrowTree) (global : GlobalState) (C : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (parents : ParentInterpretation tree C)
    (parentTag newTag : BorTag) (parent target : UniIndex) (parentNode targetNode : TreeNode)
    (tagged : tree.indexOfTag parentTag=some parent) (present : tree.nodeAt parent=some parentNode)
    (targetAt : tree.nodeAt target=some targetNode) (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag)
    (room : tree.nodes.size+1≤4294967295) (tagBound : newTag.value.toNat<global.nextPointerTag.value.toNat)
    (held : global.protectedTags.contains newTag=true)
    (start amount lower upper : UInt64) (nonzero : amount≠0)
    (bounds : start.toNat+amount.toNat≤tree.locations.size.bytes.toNat)
    (apart : ∀point : UInt64,lower.toNat≤point.toNat→point.toNat<upper.toNat→point.toNat<start.toNat∨(start+amount).toNat≤point.toNat)
    (primaryLive : ∃node,tree.nodes.get allocationRoot=some node) (parentOrder : parentNode.tag.value≤newTag.value)
    (owned : OwnedOn (Authority tree C global.protectedTags target) lower upper tree.locations) :
    let actual := tree.newChild (Size.ofBytes start) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes amount) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    actual.outcome=.ok () ∧DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global ∧
      actual.tree.locations.size=tree.locations.size ∧actual.tree.nodes.size≤tree.nodes.size+1 ∧
      ∃child,actual.tree.indexOfTag newTag=some child ∧LeafFrame tree actual.tree child parent ∧
        ParentInterpretation actual.tree (extend C child parent) ∧
        OwnedOn (Authority actual.tree (extend C child parent) global.protectedTags target) lower upper actual.tree.locations ∧
        (∀query old,tree.nodeAt query=some old→∃next,actual.tree.nodeAt query=some next ∧next.tag=old.tag ∧next.parent=old.parent ∧
          next.isExposed=old.isExposed ∧next.defaultInitialPermission=old.defaultInitialPermission) := by
  obtain ⟨done,nextRuntime,capacity,growth,child,lookup,frame,old⟩ := CurrentCallParentInsertion.concrete_frame tree global runtime parentTag newTag parent parentNode
    tagged present fresh room tagBound held start amount nonzero bounds
  obtain ⟨_,_,_,_,framedChild,framedLookup,framed⟩ := CurrentCallResourceChild.Disjoint.construct tree global C runtime parents
    parentTag newTag parent target parentNode targetNode tagged present targetAt fresh room tagBound held start amount lower upper nonzero bounds apart owned
  have same : framedChild=child := Option.some.inj (framedLookup.symm.trans lookup)
  subst framedChild
  have order := GeneralBorrowProtectedChildOrder.construct tree global runtime parents.order parentTag newTag parent parentNode tagged present fresh room parentOrder
    start amount nonzero bounds
  have nextParents := CurrentCallParentInsertion.of_leaf tree _ C parents child parent frame primaryLive nextRuntime.formed.toGraphState order
  exact ⟨done,nextRuntime,capacity,growth,child,lookup,frame,nextParents,framed,old⟩

/-- SAME Default mutable operation, framed in an independent optional target
completion. Source resources are consumed only through the spatial role. -/
theorem default_frame {before tracker ctx offset length}
    (role : CurrentCallSpatialCover.RoleCover before tracker ctx .mut offset length)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup)
    (short : role.backing.allocation.extra.nodes.size<65536)
    (nodeRoom : role.backing.allocation.extra.nodes.size+1≤4294967295)
    (C : Completion) (parents : ParentInterpretation role.backing.allocation.extra C)
    (tag : BorTag) (parent target : UniIndex) (parentNode targetNode : TreeNode)
    (concrete : role.family.value.provenance=.concrete role.backing.id tag)
    (mapped : role.backing.allocation.extra.indexOfTag tag=some parent)
    (parentAt : role.backing.allocation.extra.nodeAt parent=some parentNode)
    (targetAt : role.backing.allocation.extra.nodeAt target=some targetNode)
    (leaf : targetNode.children=#[]) (hidden : targetNode.isExposed=false) (different : target≠parent)
    (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (start amount lower upper : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
    (nonzero : amount≠0) (bounds : start.toNat+amount.toNat≤role.backing.allocation.extra.locations.size.bytes.toNat)
    (apart : ∀point : UInt64,lower.toNat≤point.toNat→point.toNat<upper.toNat→point.toNat<start.toNat∨(start+amount).toNat≤point.toNat)
    (primaryLive : ∃node,role.backing.allocation.extra.nodes.get allocationRoot=some node)
    (owned : OwnedOn (Authority role.backing.allocation.extra C tracker.global.protectedTags target) lower upper role.backing.allocation.extra.locations)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin role.backing.allocation.extra target .Write lower upper) :
    let actual := GeneralBorrowRawDefaultExpression.child role.backing.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed
    ∃child,actual.tree.indexOfTag tracker.global.nextPointerTag=some child ∧
      ParentInterpretation actual.tree (extend C child parent) ∧
      OwnedOn (Authority actual.tree (extend C child parent) tracker.global.protectedTags target) lower upper actual.tree.locations ∧
      (∃next,actual.tree.nodeAt target=some next ∧next.tag=targetNode.tag ∧next.parent=targetNode.parent ∧next.children=targetNode.children ∧next.isExposed=targetNode.isExposed) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin actual.tree target .Write lower upper ∧
      actual.tree.locations.size=role.backing.allocation.extra.locations.size ∧
      actual.tree.roots=role.backing.allocation.extra.roots ∧
      actual.tree.nodes.size≤role.backing.allocation.extra.nodes.size+1 ∧
      (∀query old,role.backing.allocation.extra.nodeAt query=some old→∃next,actual.tree.nodeAt query=some next ∧
        next.tag=old.tag ∧next.parent=old.parent ∧next.isExposed=old.isExposed ∧next.defaultInitialPermission=old.defaultInitialPermission) := by
  obtain ⟨other,node,otherMapped,nodeAt,nodeTag,readDone,readRuntime,nodes,roots,tags,capacity,normal,cellParents⟩ :=
    CurrentCallSpatialDefaultShared.prepare role runtime distinct short tag concrete room start amount startEq amountEq nonzero bounds
  have same : other=parent := Option.some.inj (otherMapped.symm.trans mapped)
  subst other
  have sameNode : node=parentNode := Option.some.inj (nodeAt.symm.trans parentAt)
  subst node
  let accessed := CurrentCallSpatialDefaultShared.accessed role tag start amount
  obtain ⟨contract,_,_⟩ := CurrentCallSpatialRead.access_runtime role rfl runtime distinct short start amount startEq amountEq nonzero bounds .VisitChildrenOfAccessed
  have actualRead : role.backing.allocation.extra.performBorrowAccessRange (CurrentCallSpatialRows.provenance role) (Size.ofBytes start) (Size.ofBytes amount)
      .Read tracker.global.protectedTags .VisitChildrenOfAccessed=accessed := by
    simp only [CurrentCallSpatialRows.provenance,concrete,accessed,CurrentCallSpatialDefaultShared.accessed,GeneralBorrowRawSharedExpression.read]
  rw [actualRead] at contract
  have readable := CurrentCallCheckpointSharedBoolFrame.spatial_readable role runtime tag parent concrete mapped start amount startEq amountEq bounds
  obtain ⟨afterParents,afterOwned,afterActive⟩ := CurrentCallCheckpointSharedBoolFrame.read_frame role.backing.allocation.extra tracker.global C runtime parents tag parent target parentNode targetNode
    parentAt mapped targetAt leaf hidden different start amount lower upper bounds readable apart owned active .VisitChildrenOfAccessed contract.tree_eq
  have high := GeneralBorrowForestTagHighWater.complete role.backing.allocation.extra _ _ runtime.below runtime.formed.allocator.nodeTags
  obtain ⟨fresh,_,unheld⟩ := GenericFunctionTagFormation.fresh_above role.backing.allocation.extra _ _ tracker.global.nextPointerTag high (Nat.le_refl _)
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping tracker.global.nextPointerTag := by rw [tags];exact fresh
  have taggedAfter : accessed.tree.indexOfTag tag=some parent := by change accessed.tree.tagMapping.get tag=_;rw [tags];exact mapped
  have parentAfter : accessed.tree.nodeAt parent=some parentNode := by change accessed.tree.nodes.get parent=_;rw [nodes];exact parentAt
  have targetAfter : accessed.tree.nodeAt target=some targetNode := by change accessed.tree.nodes.get target=_;rw [nodes];exact targetAt
  have boundsAfter : start.toNat+amount.toNat≤accessed.tree.locations.size.bytes.toNat := by rw [capacity];exact bounds
  have roomAfter : accessed.tree.nodes.size+1≤4294967295 := by rw [nodes];exact nodeRoom
  have tagBound : tracker.global.nextPointerTag.value.toNat<(GeneralBorrowFnEntryRegistration.advanced tracker.global room).nextPointerTag.value.toNat := by
    have successor:=GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag room
    change tracker.global.nextPointerTag.value.toNat<(TypedRetagEmpty.successorTag tracker.global.nextPointerTag room).value.toNat
    omega
  have order : parentNode.tag.value≤tracker.global.nextPointerTag.value :=
    UInt64.le_of_lt (GeneralBorrowParentTagInvariant.parent_below_fresh _ _ runtime parent parentNode parentAt)
  have primary : ∃node,accessed.tree.nodes.get allocationRoot=some node := by rw [nodes];exact primaryLive
  obtain ⟨done,nextRuntime,cap,growth,child,lookup,frame,nextParents,nextOwned,oldFields⟩ := constructor accessed.tree
    (GeneralBorrowFnEntryRegistration.advanced tracker.global room) C readRuntime afterParents tag tracker.global.nextPointerTag parent target parentNode targetNode
    taggedAfter parentAfter targetAfter freshAfter roomAfter tagBound unheld start amount lower upper nonzero boundsAfter apart primary order afterOwned
  have facets := CurrentCallDefaultMutableDisjoint.old_facets accessed.tree (GeneralBorrowFnEntryRegistration.advanced tracker.global room) readRuntime
    tag tracker.global.nextPointerTag parent target parentNode targetNode taggedAfter parentAfter targetAfter different freshAfter roomAfter start amount nonzero boundsAfter .Write lower upper afterActive
  refine ⟨child,lookup,nextParents,nextOwned,facets.1,facets.2,cap.trans capacity,frame.roots.trans roots,?_,?_⟩
  · rw [nodes] at growth
    exact growth
  · intro query old atOld
    have atRead : accessed.tree.nodeAt query=some old := by change accessed.tree.nodes.get query=_;rw [nodes];exact atOld
    exact oldFields query old atRead

/-- One real Strong mutable FnEntry Read/constructor frames the Bool bank
using per-row physical source capabilities, independently of its completion. -/
theorem strong_frame {before tracker ctx offset length}
    (role : CurrentCallSpatialCover.RoleCover before tracker ctx .mut offset length)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup)
    (short : role.backing.allocation.extra.nodes.size<65536) (nodeRoom : role.backing.allocation.extra.nodes.size+1≤4294967295)
    (C : Completion) (parents : ParentInterpretation role.backing.allocation.extra C)
    (tag : BorTag) (parent target : UniIndex) (parentNode targetNode : TreeNode)
    (concrete : role.family.value.provenance=.concrete role.backing.id tag)
    (mapped : role.backing.allocation.extra.indexOfTag tag=some parent)
    (parentAt : role.backing.allocation.extra.nodeAt parent=some parentNode)
    (targetAt : role.backing.allocation.extra.nodeAt target=some targetNode)
    (leaf : targetNode.children=#[]) (hidden : targetNode.isExposed=false) (different : target≠parent)
    (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (start amount lower upper : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
    (nonzero : amount≠0) (bounds : start.toNat+amount.toNat≤role.backing.allocation.extra.locations.size.bytes.toNat)
    (apart : ∀point : UInt64,lower.toNat≤point.toNat→point.toNat<upper.toNat→point.toNat<start.toNat∨(start+amount).toNat≤point.toNat)
    (primaryLive : ∃node,role.backing.allocation.extra.nodes.get allocationRoot=some node)
    (owned : OwnedOn (Authority role.backing.allocation.extra C tracker.global.protectedTags target) lower upper role.backing.allocation.extra.locations)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin role.backing.allocation.extra target .Write lower upper) :
    let registration := GeneralBorrowFnEntryRegistration.registered tracker.global {} role.backing.id room
    let accessed := role.backing.allocation.extra.performBorrowAccessRange (.concrete tag) (Size.ofBytes start) (Size.ofBytes amount)
      .Read registration.1.protectedTags .VisitChildrenOfAccessed
    let actual := accessed.tree.newChild (Size.ofBytes start) (.concrete tag) tracker.global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes amount) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    ∃child,actual.tree.indexOfTag tracker.global.nextPointerTag=some child ∧ParentInterpretation actual.tree (extend C child parent) ∧
      OwnedOn (Authority actual.tree (extend C child parent) registration.1.protectedTags target) lower upper actual.tree.locations ∧
      (∃node,actual.tree.nodeAt target=some node ∧node.tag=targetNode.tag ∧node.parent=targetNode.parent ∧node.children=targetNode.children ∧node.isExposed=targetNode.isExposed) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin actual.tree target .Write lower upper ∧
      (∀query old,role.backing.allocation.extra.nodeAt query=some old→∃next,actual.tree.nodeAt query=some next ∧next.tag=old.tag ∧next.parent=old.parent ∧
        next.isExposed=old.isExposed ∧next.defaultInitialPermission=old.defaultInitialPermission) := by
  let registration := GeneralBorrowFnEntryRegistration.registered tracker.global {} role.backing.id room
  let accessed := role.backing.allocation.extra.performBorrowAccessRange (.concrete tag) (Size.ofBytes start) (Size.ofBytes amount)
    .Read registration.1.protectedTags .VisitChildrenOfAccessed
  obtain ⟨_,held,_,currentRuntime,nodeFresh,fresh⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare role.backing.allocation.extra tracker.global {} role.backing.id room runtime
  let current := CurrentCallSpatialEntryRead.registeredRole role runtime {} room
  have readable := CurrentCallCheckpointSharedBoolFrame.spatial_readable current currentRuntime tag parent concrete mapped start amount startEq amountEq bounds
  obtain ⟨contract,readRuntime,_⟩ := CurrentCallSpatialEntryRead.invoke role rfl runtime distinct short {} room start amount startEq amountEq nonzero bounds
  have actualRead : CurrentCallSpatialEntryRead.read role {} room start amount=accessed := by
    simp only [CurrentCallSpatialEntryRead.read,CurrentCallSpatialRows.provenance,concrete,accessed]
    rfl
  rw [actualRead] at contract readRuntime
  have flags : ∀index node,role.backing.allocation.extra.nodeAt index=some node→
      registration.1.protectedTags.contains node.tag=tracker.global.protectedTags.contains node.tag := by
    intro index node present
    exact ProtectorInsertion.contains_other tracker.global.protectedTags tracker.global.nextPointerTag node.tag .StrongProtector
      (nodeFresh (index,node) (Array.mem_toList_iff.mp ((GeneralBorrowFreshReuseProtection.entries_get role.backing.allocation.extra.nodes index node).mpr present)))
  have registeredOwned : OwnedOn (Authority role.backing.allocation.extra C registration.1.protectedTags target) lower upper role.backing.allocation.extra.locations := by
    intro cursor valid positive begin finish index node atNode
    rw [flags index node atNode]
    exact owned cursor valid positive begin finish index node atNode
  obtain ⟨readParents,readOwned,readActive⟩ := CurrentCallCheckpointSharedBoolFrame.read_frame role.backing.allocation.extra registration.1 C currentRuntime parents
    tag parent target parentNode targetNode parentAt mapped targetAt leaf hidden different start amount lower upper bounds readable apart registeredOwned active
    .VisitChildrenOfAccessed contract.tree_eq
  have parentAfter : accessed.tree.nodeAt parent=some parentNode := by change accessed.tree.nodes.get parent=_;rw [contract.nodes];exact parentAt
  have targetAfter : accessed.tree.nodeAt target=some targetNode := by change accessed.tree.nodes.get target=_;rw [contract.nodes];exact targetAt
  have mappedAfter : accessed.tree.indexOfTag tag=some parent := by change accessed.tree.tagMapping.get tag=_;rw [contract.tags];exact mapped
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping tracker.global.nextPointerTag := by rw [contract.tags];exact fresh
  have roomAfter : accessed.tree.nodes.size+1≤4294967295 := by rw [contract.nodes];exact nodeRoom
  have boundsAfter : start.toNat+amount.toNat≤accessed.tree.locations.size.bytes.toNat := by rw [contract.capacity];exact bounds
  have tagBound : tracker.global.nextPointerTag.value.toNat<registration.1.nextPointerTag.value.toNat := by
    have step:=GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag room
    change tracker.global.nextPointerTag.value.toNat<(TypedRetagEmpty.successorTag tracker.global.nextPointerTag room).value.toNat
    omega
  have heldTag : registration.1.protectedTags.contains tracker.global.nextPointerTag=true := by
    unfold ProtectedTags.contains
    rw [held]
    rfl
  have primary : ∃node,accessed.tree.nodes.get allocationRoot=some node := by rw [contract.nodes];exact primaryLive
  have parentOrder : parentNode.tag.value≤tracker.global.nextPointerTag.value :=
    UInt64.le_of_lt (GeneralBorrowParentTagInvariant.parent_below_fresh _ _ runtime parent parentNode parentAt)
  obtain ⟨_,_,_,_,child,lookup,frame,nextParents,nextOwned,oldFields⟩ := strong_constructor accessed.tree registration.1 C readRuntime readParents tag tracker.global.nextPointerTag
    parent target parentNode targetNode mappedAfter parentAfter targetAfter freshAfter roomAfter tagBound heldTag start amount lower upper nonzero boundsAfter apart primary parentOrder readOwned
  obtain ⟨facets,activity⟩ := CurrentCallProtectedConstructorOldFacets.concrete accessed.tree registration.1 readRuntime tag tracker.global.nextPointerTag parent target parentNode targetNode
    mappedAfter parentAfter targetAfter different freshAfter roomAfter start amount nonzero boundsAfter .Write lower upper readActive
  refine ⟨child,lookup,nextParents,nextOwned,facets,activity,?_⟩
  intro query old atOld
  apply oldFields query old
  change accessed.tree.nodes.get query=some old
  rw [contract.nodes]
  exact atOld


theorem release_activity (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (tag : BorTag) (source target : UniIndex) (sourceNode targetNode : TreeNode)
    (tagged : tree.indexOfTag tag = some source) (sourceAt : tree.nodeAt source = some sourceNode)
    (sourceHidden : sourceNode.isExposed = false)
    (targetAt : tree.nodeAt target = some targetNode) (targetLeaf : targetNode.children = #[])
    (targetHidden : targetNode.isExposed = false) (different : target ≠ source)
    (offset upper lower targetUpper : UInt64)
    (sourceActive : ActiveWithin tree source .Write offset upper)
    (normalRows : OwnedOn (fun location => Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree location global.protectedTags source))
      offset upper tree.locations)
    (targetActive : ActiveWithin tree target .Write lower targetUpper) :
    ActiveWithin (tree.releaseProtector tag global.protectedTags).tree target .Write lower targetUpper := by
  let P := fun (range : ByteRange) (location : LocationTree) =>
    ∀ point : UInt64, range.start.toNat ≤ point.toNat → point.toNat < range.stop.toNat →
      ∀ state, location.perms.get target = some state → state.accessed = true →
      ∀ kind, state.permission.associatedAccess = some kind → lower.toNat ≤ point.toNat ∧ point.toNat < targetUpper.toNat
  have rows : S05CurrentReleaseIterator.Rows P tree.locations := by
    intro position valid point start stop state stored accessed kind associated
    have old := targetActive point tree.locations.entries[position].data ⟨position,valid,start,stop,rfl⟩ state stored accessed kind associated
    exact ⟨old.1,old.2.1⟩
  have activeRows := GeneralBorrowFreshActiveWithin.active_on tree source .Write offset upper runtime.formed.well sourceActive
  have retained := (checkpoint_bool_rule "CurrentCallReadRootActivity.release_rows") tree global.protectedTags tag source sourceNode sourceAt sourceHidden tagged P rows (by
    intro position valid state stored accessed kind associated
    obtain ⟨start,stop,readKind⟩ := activeRows position valid state stored accessed kind associated
    have positive := (GeneralRangeMapGeometry.facts tree.locations runtime.formed.well (by omega)).2.1 position valid
    have first := sourceActive tree.locations.entries[position].range.start tree.locations.entries[position].data
      ⟨position,valid,Nat.le_refl _,positive,rfl⟩ state stored accessed kind associated
    obtain ⟨normal⟩ := normalRows position valid (by omega) start stop
    intro point pointStart pointStop after afterStored afterAccessed afterKind afterAssociated
    by_cases inside : lower.toNat ≤ point.toNat ∧ point.toNat < targetUpper.toNat
    · exact inside
    have quiet : S02HiddenLeafQuietNormal.Quiet (GeneralBorrowWildcardVirtualLeaf.effective tree.locations.entries[position].data target targetNode) := by
      cases oldStored : tree.locations.entries[position].data.perms.get target with
      | none => left;simp only [GeneralBorrowWildcardVirtualLeaf.effective,oldStored,Option.getD_none,TreeNode.defaultLocationState]
      | some old =>
        simp only [GeneralBorrowWildcardVirtualLeaf.effective,oldStored,Option.getD_some]
        by_cases cell : old.permission = .Cell
        · exact .inr cell
        · left
          cases h : old.accessed with
          | false => rfl
          | true =>
            have oldAssociated : ∃ k,old.permission.associatedAccess = some k := by cases p : old.permission <;> simp_all [Permission.associatedAccess]
            obtain ⟨k,oldAssociated⟩ := oldAssociated
            exact False.elim (inside (rows position valid point pointStart pointStop old oldStored h k oldAssociated))
    have afterQuiet := (S02HiddenLeafQuietTreeAccess.concrete tree runtime.formed.toGraphState tree.locations.entries[position].data global.protectedTags
      target source targetNode sourceNode targetAt sourceAt targetLeaf targetHidden different normal (runtime.coherent position valid) kind
      .SkipChildrenOfAccessed tree.locations.entries[position].range quiet).1
    change S02HiddenLeafQuietNormal.Quiet (((source_access_location (source_tree_access_at tree tree.locations.entries[position].data (some source) kind global.protectedTags
      .SkipChildrenOfAccessed tree.locations.entries[position].range)).perms.get target).getD targetNode.defaultLocationState) at afterQuiet
    rw [afterStored] at afterQuiet
    rcases afterQuiet with inactive | cell
    · simp only [Option.getD_some] at inactive;rw [afterAccessed] at inactive;cases inactive
    · simp only [Option.getD_some] at cell;rw [cell,Permission.associatedAccess] at afterAssociated;cases afterAssociated)
  intro point location valueAt state stored accessed kind associated
  obtain ⟨position,valid,start,stop,data⟩ := valueAt
  rw [←data] at stored
  have inside := retained position valid point start stop state stored accessed kind associated
  exact ⟨inside.1,inside.2,by intro impossible;cases impossible⟩

/-- Actual mutable observer release and its whole singleton endCall retain
both the Bool bank and its hidden-leaf activity. No whole-source interpretation
is used to justify the callback's physical Normal permissions. -/
theorem release_frame (tree : BorrowTree) (global : GlobalState) (C : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (parents : ParentInterpretation tree C)
    (allocation : AllocId) (tag : BorTag) (source target : UniIndex) (sourceNode targetNode : TreeNode)
    (tagged : tree.indexOfTag tag=some source) (sourceAt : tree.nodeAt source=some sourceNode) (sourceHidden : sourceNode.isExposed=false)
    (targetAt : tree.nodeAt target=some targetNode) (leaf : targetNode.children=#[]) (hidden : targetNode.isExposed=false) (different : target≠source)
    (start stop lower upper : UInt64)
    (sourceActive : ActiveWithin tree source .Write start stop)
    (normalRows : OwnedOn (fun location=>Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree location global.protectedTags source)) start stop tree.locations)
    (apart : stop.toNat≤lower.toNat∨upper.toNat≤start.toNat)
    (owned : OwnedOn (Authority tree C global.protectedTags target) lower upper tree.locations)
    (active : ActiveWithin tree target .Write lower upper) :
    let actual := tree.releaseProtector tag global.protectedTags
    let next := global.endCall (({} : FrameState).addProtector allocation tag)
    ParentInterpretation actual.tree C ∧
      OwnedOn (Authority actual.tree C next.protectedTags target) lower upper actual.tree.locations ∧
      actual.tree.nodeAt target=some targetNode ∧ActiveWithin actual.tree target .Write lower upper := by
  have retained := S02DisjointReleaseFrame.release tree global.protectedTags tag source source sourceNode tagged sourceAt sourceHidden
    start stop sourceActive sourceActive (Authority tree C global.protectedTags target) lower upper apart owned runtime.formed.well
  have activity := release_activity tree global runtime tag source target sourceNode targetNode tagged sourceAt sourceHidden targetAt leaf hidden different
    start stop lower upper sourceActive normalRows active
  have shape := GeneralBorrowStructuralReleaseGeometryFrame.release tree global.protectedTags tag
  have nodes := congrArg BorrowTree.nodes shape
  refine ⟨?_,?_,?_,activity⟩
  · rw [shape]
    exact CurrentCallCheckpointSharedBoolFrame.parents_locations tree C parents _
  · intro cursor valid positive begin finish index node atNode
    rw [nodes] at atNode
    have rights := retained cursor valid positive begin finish index node atNode
    have weaken := GeneralBorrowRelease.end_call_weakens global (({} : FrameState).addProtector allocation tag) node.tag
    refine ⟨?_,?_⟩
    · intro below
      obtain ⟨possible,disabled,frozen,reserved⟩ := rights.1 below
      exact ⟨possible,disabled,frozen,fun held=>reserved (weaken held)⟩
    · intro outside
      obtain ⟨possible,quiet⟩ := rights.2 outside
      exact ⟨possible,fun held=>quiet (weaken held)⟩
  · change (tree.releaseProtector tag global.protectedTags).tree.nodes.get target=some targetNode
    rw [nodes]
    exact targetAt


end
end DuplicatePrefix.CurrentCallCheckpointMutableBoolFrame
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointMutableBoolFrame" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved checkpoint mutable Bool dependency {dependency}"
