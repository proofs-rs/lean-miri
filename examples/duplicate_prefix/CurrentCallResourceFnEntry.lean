import duplicate_prefix.CurrentCallResourceRead
import duplicate_prefix.GeneralBorrowFnEntryRegistrationRuntime
import duplicate_prefix.CandidateCurrentFnEntryRaw
import duplicate_prefix.CurrentCallResourceChild
import duplicate_prefix.GeneralBorrowRangeOutsideOwned

/-! Actual FnEntry registration and Read/constructor composition for the finite
candidate denotation. No ordinary-input adoption or family/GC adequacy is
asserted by these operational resource transports. -/
namespace DuplicatePrefix.CurrentCallResourceFnEntry
open Miri Miri.ABI Miri.Memory Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization GeneralBorrowExposedNonleafPrimaryPath
open GeneralBorrowFnEntryRegistration
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 65536
noncomputable section

private def extra (provenance : Provenance) : ProvenanceExtra :=
  match provenance with | .concrete _ tag => .concrete tag | .wildcard => .wildcard

private theorem local_token (state : LocationState) (held : Bool)
    (realized : Realized state held) (right : OrdinaryBorrowAuthority.LocalWrite state held) :
    .exclusive ∈ tokens (denote state held) := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflicted => cases conflicted <;> cases accessed <;> cases held <;>
      simp_all [OrdinaryBorrowAuthority.LocalWrite,Realized,WellFormed,denote,tokens,LocationState.possible]
  | Cell | ReservedIM | Unique | Frozen | Disabled => cases accessed <;> cases held <;>
      simp_all [OrdinaryBorrowAuthority.LocalWrite,Realized,WellFormed,denote,tokens,LocationState.possible,Permission.isUnique]

private theorem foreign_no_clash (state : LocationState) (held : Bool)
    (realized : Realized state held) (right : OrdinaryBorrowAuthority.ForeignWrite state held) :
    ¬Clash (guard (denote state held)) .exclusive := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflicted => cases conflicted <;> cases accessed <;> cases held <;>
      simp_all [OrdinaryBorrowAuthority.ForeignWrite,Realized,WellFormed,denote,CandidateCurrentGrantResources.guard,Clash,LocationState.possible]
  | Cell | ReservedIM | Unique | Frozen | Disabled => cases accessed <;> cases held <;>
      simp_all [OrdinaryBorrowAuthority.ForeignWrite,Realized,WellFormed,denote,CandidateCurrentGrantResources.guard,Clash,LocationState.possible,Permission.isUnique]

private theorem child_of_operation (tree : BorrowTree) (global : GlobalState) (frame : FrameState)
    (id : AllocId) (provenance : Provenance) (start amount : UInt64)
    (room : global.nextPointerTag.value < 18446744073709551615) (output : GeneralBorrowForestFnEntry.Output)
    (actual : CandidateCurrentFnEntryRaw.operation tree global frame id provenance start amount = .ok output) :
    output.child =
      (tree.performBorrowAccessRange (extra provenance)
        (Size.ofBytes start) (Size.ofBytes amount) .Read (registered global frame id room).1.protectedTags .VisitChildrenOfAccessed).tree.newChild
      (Size.ofBytes start) (extra provenance) global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes amount) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true := by
  have allocated := TypedRetagEmpty.allocate_tag global room
  cases provenance with
  | concrete suppliedId tag =>
    simp only [CandidateCurrentFnEntryRaw.operation,GeneralBorrowForestFnEntry.operation,GeneralBorrowForestProtected.read,
      allocated,Except.bind,Except.pure,bind,pure] at actual
    cases Except.ok.inj actual
    rfl
  | wildcard =>
    simp only [CandidateCurrentFnEntryRaw.operation,GeneralBorrowRawWildcardFnEntryRuntime.operation,
      allocated,Except.bind,Except.pure,bind,pure] at actual
    cases Except.ok.inj actual
    rfl

private theorem window_owned {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode)
    (exclusive : demandOf mode = .exclusive)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (lo hi : UInt64) (windowLower : offset ≤ lo.toNat) (windowUpper : hi.toNat ≤ offset+length) :
    GeneralRangeMapOrigins.OwnedOn (S05CompletedAncestryReadMutable.Authority W.allocation.extra W.precise.completion tracker.global.protectedTags W.pointer.grant)
      lo hi W.allocation.extra.locations := by
  intro position valid positive beforeUpper afterLower
  have segmentPositive := (GeneralRangeMapGeometry.facts W.allocation.extra.locations runtime.formed.well (by omega)).2.1 position valid
  have member : W.allocation.extra.locations.entries[position] ∈ W.allocation.extra.locations.entries.toList :=
    Array.mem_toList_iff.mpr (Array.getElem_mem valid)
  by_cases earlier : lo.toNat ≤ W.allocation.extra.locations.entries[position].range.start.toNat
  · apply CurrentCallResourceAccess.row_authority W exclusive (id,W.allocation.extra.locations.entries[position].range.start.toNat)
      ⟨rfl,by omega,by omega⟩ _ member (Nat.le_refl _) segmentPositive
      (runtime.formed.profile position valid) (runtime.possible position valid)
  · apply CurrentCallResourceAccess.row_authority W exclusive (id,lo.toNat) ⟨rfl,windowLower,by omega⟩ _ member (by omega) afterLower
      (runtime.formed.profile position valid) (runtime.possible position valid)

private theorem issuance_tracker {before tracker next id allocation completion grant}
    (rootTags : ∀ id,next.global.rootTag? id = tracker.global.rootTag? id)
    (issued : SpatialDelegation before tracker id allocation completion grant) :
    SpatialDelegation before next id allocation completion grant := by
  induction issued with
  | allocated cap =>
    apply SpatialDelegation.allocated
    refine ⟨cap.live,cap.extent,cap.treeExtent,cap.rootSlot,?_⟩
    obtain ⟨node,present,parentless,disabled,cached⟩ := cap.rootNode
    exact ⟨node,present,parentless,disabled,(rootTags id).trans cached⟩
  | concrete original path ih => exact .concrete ih path
  | wildcard originNode rootNode earlier position originRoot original originAt exposed rootAt parentless older before earlierAt rootSlot path edge ih =>
    exact .wildcard originNode rootNode earlier position originRoot ih originAt exposed rootAt parentless older before earlierAt rootSlot path edge

/-- The actual fresh Strong registration preserves every old family, grant,
parent interpretation, allocation identity/cache, and byte embedding. The new
protector has no old physical node, so no old active resource is newly charged. -/
def registered_window {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (frame : FrameState) (room : tracker.global.nextPointerTag.value < 18446744073709551615) :
    UniformWindow before {tracker with global := (registered tracker.global frame id room).1}
      data owner id offset length mode := by
  obtain ⟨_,_,_,_,fresh,_⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare W.allocation.extra tracker.global frame id room runtime
  have flags : ∀ index node,W.allocation.extra.nodes.get index = some node →
      (registered tracker.global frame id room).1.protectedTags.contains node.tag = tracker.global.protectedTags.contains node.tag := by
    intro index node present
    exact ProtectorInsertion.contains_other tracker.global.protectedTags tracker.global.nextPointerTag node.tag .StrongProtector
      (fresh (index,node) (Array.mem_toList_iff.mp ((GeneralBorrowFreshReuseProtection.entries_get W.allocation.extra.nodes index node).mpr present)))
  refine ⟨W.loan,W.pointer,W.allocation,W.precise,W.loanAt,W.pointerAt,W.pointerId,W.present,W.preciseAt,W.binding,
    issuance_tracker (tracker := tracker) (next := {tracker with global := (registered tracker.global frame id room).1}) (fun _ => rfl) W.issued,W.parents,?_⟩
  intro byte inside
  refine ⟨(W.window byte inside).1,?_⟩
  intro segment member lower upper index node present
  rw [flags index node present]
  exact (W.window byte inside).2 segment member lower upper index node present

/-- The selected runtime state and its existing high-water resource provide
realization after fresh Strong registration in every ACTUAL live allocation.
This is representation transport, not an ownership or callback-table premise. -/
theorem registered_actual {before tracker}
    (state : DuplicatePrefixRuntimeInput.State before tracker)
    (highwater : ∀ row ∈ before.memory.live.toList, GeneralBorrowForestTagHighWater.Below row.2.allocation.extra
      tracker.global.protectedTags tracker.global.nextPointerTag)
    (frame : FrameState) (allocationId : AllocId)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615) :
    ActualRealized (ActualWorld before) (registered tracker.global frame allocationId room).1.protectedTags := by
  apply CandidateCurrentGrantRuntime.actual
  intro id allocation live
  simp only [Present,ActualWorld,Array.toList_map] at live
  obtain ⟨⟨oldId,entry⟩,present,equal⟩ := List.mem_map.mp live
  rcases Prod.mk.inj equal with ⟨rfl,rfl⟩
  let runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global :=
    ⟨state.formed (oldId,entry) present,state.coherent (oldId,entry) present,
      state.possible (oldId,entry) present,highwater (oldId,entry) present⟩
  exact (GeneralBorrowFnEntryRegistrationRuntime.prepare entry.allocation.extra tracker.global frame allocationId room runtime).2.2.2.1

/-- Same current arrays/families/grant and optional C, with geometry rederived
under the actual fresh registration. No post-registration Proposed is needed. -/
theorem registered_geometry_selected {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (frame : FrameState) (room : tracker.global.nextPointerTag.value < 18446744073709551615)
    (exclusive : demandOf mode = .exclusive) :
    Nonempty (Geometry (registered_window W runtime frame room)) := by
  have registeredRuntime := (GeneralBorrowFnEntryRegistrationRuntime.prepare W.allocation.extra tracker.global frame id room runtime).2.2.2.1
  exact CurrentCallResourceNormalization.geometry_selected (registered_window W runtime frame room)
    (CandidateCurrentGrantRuntime.tree_rows W.allocation.extra (registered tracker.global frame id room).1 registeredRuntime) exclusive


set_option linter.unusedVariables false in
theorem registered_geometry {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (state : DuplicatePrefixRuntimeInput.State before tracker)
    (highwater : ∀ row ∈ before.memory.live.toList, GeneralBorrowForestTagHighWater.Below row.2.allocation.extra
      tracker.global.protectedTags tracker.global.nextPointerTag)
    (frame : FrameState) (room : tracker.global.nextPointerTag.value < 18446744073709551615)
    (exclusive : demandOf mode = .exclusive) :
    Nonempty (Geometry (registered_window W runtime frame room)) := by
  exact registered_geometry_selected W runtime frame room exclusive

/-- Actual registration followed by the associated ranged Read. The output
runtime, optional parent interpretation and mutable window all concern the
SAME result tree which the following newChild operation will consume. -/
theorem prepare_read_selected {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (frame : FrameState) (room : tracker.global.nextPointerTag.value < 18446744073709551615)
    (exclusive : demandOf mode = .exclusive) (distinct : W.allocation.extra.roots.toList.Nodup)
    (short : W.allocation.extra.nodes.size < 65536)
    (start amount : UInt64) (startEq : start.toNat = offset) (amountEq : amount.toNat = length)
    (bounds : start.toNat+amount.toNat ≤ W.allocation.extra.locations.size.bytes.toNat) :
    let registration := registered tracker.global frame id room
    let accessed := W.allocation.extra.performBorrowAccessRange
      (extra W.pointer.value.provenance)
      (Size.ofBytes start) (Size.ofBytes amount) .Read registration.1.protectedTags .VisitChildrenOfAccessed
    accessed.status = .Completed ∧ DuplicatePrefixBorrowContract.RuntimeFacts accessed.tree registration.1 ∧
      ParentInterpretation accessed.tree W.precise.completion ∧
      GeneralRangeMapOrigins.OwnedOn (S05CompletedAncestryReadMutable.Authority accessed.tree W.precise.completion registration.1.protectedTags W.pointer.grant)
        start (start+amount) accessed.tree.locations ∧
      accessed.tree.nodes = W.allocation.extra.nodes ∧ accessed.tree.roots = W.allocation.extra.roots ∧
      accessed.tree.tagMapping = W.allocation.extra.tagMapping ∧ accessed.tree.locations.size = W.allocation.extra.locations.size := by
  have registeredRuntime := (GeneralBorrowFnEntryRegistrationRuntime.prepare W.allocation.extra tracker.global frame id room runtime).2.2.2.1
  let current := registered_window W runtime frame room
  obtain ⟨geometry⟩ := registered_geometry_selected W runtime frame room exclusive
  have noWrap : start.toNat+amount.toNat < 2^64 := Nat.lt_of_le_of_lt bounds (UInt64.toNat_lt W.allocation.extra.locations.size.bytes)
  have upper : (start+amount).toNat = start.toNat+amount.toNat := by
    simp only [UInt64.toNat_add,Nat.mod_eq_of_lt noWrap]
  exact CurrentCallResourceRead.read_range_runtime current geometry exclusive distinct short registeredRuntime
    (Size.ofBytes start) (Size.ofBytes amount) start (start+amount) (by omega) (by omega) bounds (Nat.le_refl _) (Nat.le_refl _)
    .VisitChildrenOfAccessed


set_option linter.unusedVariables false in
theorem prepare_read {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (state : DuplicatePrefixRuntimeInput.State before tracker)
    (highwater : ∀ row ∈ before.memory.live.toList, GeneralBorrowForestTagHighWater.Below row.2.allocation.extra
      tracker.global.protectedTags tracker.global.nextPointerTag)
    (frame : FrameState) (room : tracker.global.nextPointerTag.value < 18446744073709551615)
    (exclusive : demandOf mode = .exclusive) (distinct : W.allocation.extra.roots.toList.Nodup)
    (short : W.allocation.extra.nodes.size < 65536)
    (start amount : UInt64) (startEq : start.toNat = offset) (amountEq : amount.toNat = length)
    (bounds : start.toNat+amount.toNat ≤ W.allocation.extra.locations.size.bytes.toNat) :
    let registration := registered tracker.global frame id room
    let accessed := W.allocation.extra.performBorrowAccessRange
      (extra W.pointer.value.provenance)
      (Size.ofBytes start) (Size.ofBytes amount) .Read registration.1.protectedTags .VisitChildrenOfAccessed
    accessed.status = .Completed ∧ DuplicatePrefixBorrowContract.RuntimeFacts accessed.tree registration.1 ∧
      ParentInterpretation accessed.tree W.precise.completion ∧
      GeneralRangeMapOrigins.OwnedOn (S05CompletedAncestryReadMutable.Authority accessed.tree W.precise.completion registration.1.protectedTags W.pointer.grant)
        start (start+amount) accessed.tree.locations ∧
      accessed.tree.nodes = W.allocation.extra.nodes ∧ accessed.tree.roots = W.allocation.extra.roots ∧
      accessed.tree.tagMapping = W.allocation.extra.tagMapping ∧ accessed.tree.locations.size = W.allocation.extra.locations.size := by
  exact prepare_read_selected W runtime frame room exclusive distinct short start amount startEq amountEq bounds

/-- The actual registered Read output is fed directly into the real concrete
or wildcard protected child constructor. Only the new actual child receives
an edge in C; old ambient components are retained without invented origins.
This borrowing-stage result does not assert Ordinary or full family adequacy. -/
theorem invoke_selected {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (frame : FrameState) (room : tracker.global.nextPointerTag.value < 18446744073709551615)
    (exclusive : demandOf mode = .exclusive) (distinct : W.allocation.extra.roots.toList.Nodup)
    (short : W.allocation.extra.nodes.size < 65536) (nodeRoom : W.allocation.extra.nodes.size+1 ≤ 4294967295)
    (start amount : UInt64) (startEq : start.toNat = offset) (amountEq : amount.toNat = length) (nonzero : amount ≠ 0)
    (bounds : start.toNat+amount.toNat ≤ W.allocation.extra.locations.size.bytes.toNat) :
    ∃ output, CandidateCurrentFnEntryRaw.operation W.allocation.extra tracker.global frame id W.pointer.value.provenance start amount = .ok output ∧
      output.tag = tracker.global.nextPointerTag ∧ output.global = (registered tracker.global frame id room).1 ∧
      output.frame = (registered tracker.global frame id room).2 ∧ output.access.status = .Completed ∧ output.child.outcome = .ok () ∧
      DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree output.global ∧
      ∃ child,output.child.tree.indexOfTag output.tag = some child ∧
        ParentInterpretation output.child.tree (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) ∧
        GeneralRangeMapOrigins.OwnedOn (S05CompletedAncestryReadMutable.Authority output.child.tree
          (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) output.global.protectedTags child)
          start (start+amount) output.child.tree.locations ∧
        output.child.tree.locations.size = W.allocation.extra.locations.size ∧
        (∀ (position : Nat) (root : UniIndex),W.allocation.extra.roots[position]? = some root → output.child.tree.roots[position]? = some root) ∧
        (∀ index node,W.allocation.extra.nodes.get index = some node →
          ∃ next,output.child.tree.nodes.get index = some next ∧ next.tag = node.tag ∧ next.parent = node.parent ∧
            next.isExposed = node.isExposed ∧ next.defaultInitialPermission = node.defaultInitialPermission) ∧
        (∃ node,output.child.tree.nodes.get child = some node ∧ node.tag = output.tag ∧
          match W.pointer.value.provenance with
          | .concrete _ _ => node.parent = some W.pointer.grant
          | .wildcard => node.parent = none) := by
  obtain ⟨allocated,held,frameEq,registeredRuntime,_,fresh⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare W.allocation.extra tracker.global frame id room runtime
  let registration := registered tracker.global frame id room
  let accessed := W.allocation.extra.performBorrowAccessRange
    (extra W.pointer.value.provenance)
    (Size.ofBytes start) (Size.ofBytes amount) .Read registration.1.protectedTags .VisitChildrenOfAccessed
  obtain ⟨readDone,afterRuntime,parents,owned,nodes,roots,tags,capacity⟩ := prepare_read_selected W runtime frame room exclusive distinct short start amount startEq amountEq bounds
  obtain ⟨parentNode,parentAt,_,binding⟩ := W.binding
  have parentAfter : accessed.tree.nodes.get W.pointer.grant = some parentNode := by rw [nodes];exact parentAt
  have tagged : accessed.tree.indexOfTag parentNode.tag = some W.pointer.grant := afterRuntime.formed.allocator.nodeTags _ _ parentAfter
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping tracker.global.nextPointerTag := by rw [tags];exact fresh
  have childRoom : accessed.tree.nodes.size+1 ≤ 4294967295 := by change accessed.tree.nodes.data.size+1 ≤ _;rw [nodes];exact nodeRoom
  have childBounds : start.toNat+amount.toNat ≤ accessed.tree.locations.size.bytes.toNat := by rw [capacity];exact bounds
  have tagBound : tracker.global.nextPointerTag.value.toNat < registration.1.nextPointerTag.value.toNat := by
    have successor := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag room
    change tracker.global.nextPointerTag.value.toNat < (TypedRetagEmpty.successorTag tracker.global.nextPointerTag room).value.toNat
    omega
  have tagHeld : registration.1.protectedTags.contains tracker.global.nextPointerTag = true := by
    unfold ProtectedTags.contains
    rw [held]
    rfl
  have older := GeneralBorrowParentTagInvariant.parent_below_fresh W.allocation.extra tracker.global runtime W.pointer.grant parentNode parentAt
  obtain ⟨primaryNode,primaryAt,_,_,_⟩ := W.issued.capability.rootNode
  have primaryLive : ∃ node,accessed.tree.nodes.get allocationRoot = some node := ⟨primaryNode,by rw [nodes];exact primaryAt⟩
  cases provenance : W.pointer.value.provenance with
  | concrete suppliedId tag =>
    rw [provenance] at binding
    have tagEq := binding.2
    obtain ⟨childDone,childRuntime,childCapacity,_,child,lookup,childOwned⟩ := CurrentCallResourceChild.construct accessed.tree registration.1 W.precise.completion afterRuntime parents
      parentNode.tag tracker.global.nextPointerTag W.pointer.grant parentNode tagged parentAfter freshAfter childRoom tagBound tagHeld start amount nonzero childBounds owned
    obtain ⟨_,_,_,_,frameChild,frameLookup,leaf,oldFields⟩ := CurrentCallParentInsertion.concrete_frame accessed.tree registration.1 afterRuntime
      parentNode.tag tracker.global.nextPointerTag W.pointer.grant parentNode tagged parentAfter freshAfter childRoom tagBound tagHeld start amount nonzero childBounds
    have same : frameChild = child := Option.some.inj (frameLookup.symm.trans lookup)
    subst frameChild
    have order := GeneralBorrowProtectedChildOrder.construct accessed.tree registration.1 afterRuntime parents.order parentNode.tag tracker.global.nextPointerTag
      W.pointer.grant parentNode tagged parentAfter freshAfter childRoom (UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp older))) start amount nonzero childBounds
    have childParents := CurrentCallParentInsertion.of_leaf accessed.tree _ W.precise.completion parents child W.pointer.grant leaf primaryLive childRuntime.formed.toGraphState order
    obtain ⟨metadataChild,metadataLookup,metadataNode,_,_⟩ := GeneralBorrowProtectedChildMetadata.construct accessed.tree registration.1 afterRuntime
      parentNode.tag tracker.global.nextPointerTag W.pointer.grant parentNode tagged parentAfter freshAfter childRoom start amount nonzero childBounds
    have sameMetadata : metadataChild = child := Option.some.inj (metadataLookup.symm.trans lookup)
    subst metadataChild
    obtain ⟨newNode,newAt,newTag,_⟩ := metadataNode
    obtain ⟨physicalNode,physicalAt,physicalParent⟩ := leaf.childLive
    have nodeEq : physicalNode = newNode := Option.some.inj (physicalAt.symm.trans newAt)
    subst physicalNode
    let output : GeneralBorrowForestFnEntry.Output := ⟨registration.1,registration.2,tracker.global.nextPointerTag,accessed,
      accessed.tree.newChild (Size.ofBytes start) (.concrete parentNode.tag) tracker.global.nextPointerTag
        (DedupRangeMap.new (Size.ofBytes amount) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true⟩
    refine ⟨output,?_,rfl,rfl,rfl,readDone,childDone,childRuntime,child,lookup,childParents,childOwned,childCapacity.trans capacity,?_,?_,
      newNode,newAt,newTag,(by simpa only [provenance] using physicalParent)⟩
    · simp only [CandidateCurrentFnEntryRaw.operation,tagEq,GeneralBorrowForestFnEntry.operation,allocated,Except.bind,Except.pure,bind,pure]
      simp only [output,accessed,registration,registered,extra,provenance,tagEq,GeneralBorrowForestProtected.read]
    · intro position root slot
      have allRoots : output.child.tree.roots = W.allocation.extra.roots := leaf.roots.trans roots
      rw [allRoots]
      exact slot
    · intro index node present
      exact oldFields index node (by change accessed.tree.nodes.get index = some node;rw [nodes];exact present)
  | wildcard =>
    rw [provenance] at binding
    obtain ⟨childDone,childRuntime,childCapacity,_,child,lookup,_,rootFrame,childOwned⟩ := CurrentCallResourceChild.Wildcard.construct accessed.tree registration.1 W.precise.completion afterRuntime parents
      tracker.global.nextPointerTag freshAfter childRoom tagBound tagHeld W.pointer.grant parentNode parentAfter start amount nonzero childBounds owned
    obtain ⟨mapping,index,inserted,_,vacant,_,_,_⟩ := GeneralBorrowWildcardConstructorSlot.select accessed.tree registration.1 afterRuntime tracker.global.nextPointerTag freshAfter childRoom (.ReservedFrz false) .None
    obtain ⟨depth⟩ := afterRuntime.formed.depth
    have order := GeneralBorrowWildcardChildCausalOrder.inserted_order accessed.tree depth parents.order tracker.global.nextPointerTag mapping index inserted vacant
      (Size.ofBytes start) (DedupRangeMap.new (Size.ofBytes amount) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    obtain ⟨position,root,rootNode,rootSlot,rootAt,path⟩ := CandidateCurrentWindowAuthority.root_path W.allocation.extra W.parents.graph W.pointer.grant parentNode parentAt
    have currentSlot : accessed.tree.roots[position]? = some root := by rw [roots];exact rootSlot
    have currentPath : Path accessed.tree root W.pointer.grant := GeneralBorrowPrimaryWitnessVisibility.path_nodes (before := accessed.tree) (after := W.allocation.extra) nodes.symm path
    have childParents := CurrentCallParentInsertion.of_root accessed.tree _ W.precise.completion parents child W.pointer.grant tracker.global.nextPointerTag rootFrame primaryLive
      childRuntime.formed.toGraphState order parentNode parentAfter binding older position root currentSlot currentPath
    obtain ⟨_,_,_,_,metadataChild,metadataLookup,_,_,oldFields⟩ := CurrentCallParentInsertion.wildcard_frame accessed.tree registration.1 afterRuntime
      tracker.global.nextPointerTag freshAfter childRoom tagBound tagHeld W.pointer.grant parentNode parentAfter start amount nonzero childBounds
    have sameMetadata : metadataChild = child := Option.some.inj (metadataLookup.symm.trans lookup)
    subst metadataChild
    obtain ⟨newNode,newAt,newTag,physicalParent⟩ := rootFrame.childLive
    let output : GeneralBorrowForestFnEntry.Output := ⟨registration.1,registration.2,tracker.global.nextPointerTag,accessed,
      accessed.tree.newChild (Size.ofBytes start) .wildcard tracker.global.nextPointerTag
        (DedupRangeMap.new (Size.ofBytes amount) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true⟩
    refine ⟨output,?_,rfl,rfl,rfl,readDone,childDone,childRuntime,child,lookup,childParents,childOwned,childCapacity.trans capacity,?_,?_,
      newNode,newAt,newTag,(by simpa only [provenance] using physicalParent)⟩
    · simp only [CandidateCurrentFnEntryRaw.operation,GeneralBorrowRawWildcardFnEntryRuntime.operation,allocated,Except.bind,Except.pure,bind,pure]
      simp only [output,accessed,registration,registered,extra,provenance]
    · intro position root slot
      have valid := (Array.getElem?_eq_some_iff.mp slot).1
      have allRoots : output.child.tree.roots = W.allocation.extra.roots.push child := rootFrame.roots.trans (congrArg (fun roots => roots.push child) roots)
      rw [allRoots]
      simpa only [Array.getElem?_push,show position ≠ W.allocation.extra.roots.size by omega,↓reduceIte] using slot
    · intro index node present
      exact oldFields index node (by change accessed.tree.nodes.get index = some node;rw [nodes];exact present)


set_option linter.unusedVariables false in
theorem invoke {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (state : DuplicatePrefixRuntimeInput.State before tracker)
    (highwater : ∀ row ∈ before.memory.live.toList, GeneralBorrowForestTagHighWater.Below row.2.allocation.extra
      tracker.global.protectedTags tracker.global.nextPointerTag)
    (frame : FrameState) (room : tracker.global.nextPointerTag.value < 18446744073709551615)
    (exclusive : demandOf mode = .exclusive) (distinct : W.allocation.extra.roots.toList.Nodup)
    (short : W.allocation.extra.nodes.size < 65536) (nodeRoom : W.allocation.extra.nodes.size+1 ≤ 4294967295)
    (start amount : UInt64) (startEq : start.toNat = offset) (amountEq : amount.toNat = length) (nonzero : amount ≠ 0)
    (bounds : start.toNat+amount.toNat ≤ W.allocation.extra.locations.size.bytes.toNat) :
    ∃ output, CandidateCurrentFnEntryRaw.operation W.allocation.extra tracker.global frame id W.pointer.value.provenance start amount = .ok output ∧
      output.tag = tracker.global.nextPointerTag ∧ output.global = (registered tracker.global frame id room).1 ∧
      output.frame = (registered tracker.global frame id room).2 ∧ output.access.status = .Completed ∧ output.child.outcome = .ok () ∧
      DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree output.global ∧
      ∃ child,output.child.tree.indexOfTag output.tag = some child ∧
        ParentInterpretation output.child.tree (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) ∧
        GeneralRangeMapOrigins.OwnedOn (S05CompletedAncestryReadMutable.Authority output.child.tree
          (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) output.global.protectedTags child)
          start (start+amount) output.child.tree.locations ∧
        output.child.tree.locations.size = W.allocation.extra.locations.size ∧
        (∀ (position : Nat) (root : UniIndex),W.allocation.extra.roots[position]? = some root → output.child.tree.roots[position]? = some root) ∧
        (∀ index node,W.allocation.extra.nodes.get index = some node →
          ∃ next,output.child.tree.nodes.get index = some next ∧ next.tag = node.tag ∧ next.parent = node.parent ∧
            next.isExposed = node.isExposed ∧ next.defaultInitialPermission = node.defaultInitialPermission) ∧
        (∃ node,output.child.tree.nodes.get child = some node ∧ node.tag = output.tag ∧
          match W.pointer.value.provenance with
          | .concrete _ _ => node.parent = some W.pointer.grant
          | .wildcard => node.parent = none) := by
  exact invoke_selected W runtime frame room exclusive distinct short nodeRoom start amount startEq amountEq nonzero bounds

/-- The actual FnEntry output embeds the SAME exclusive source footprint at
the freshly created child. The parent handle is not asserted simultaneously
active. This is source-resource transport, not arbitrary-copy-family adequacy. -/
theorem invoke_resources_selected {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (frame : FrameState) (room : tracker.global.nextPointerTag.value < 18446744073709551615)
    (exclusive : demandOf mode = .exclusive) (distinct : W.allocation.extra.roots.toList.Nodup)
    (short : W.allocation.extra.nodes.size < 65536) (nodeRoom : W.allocation.extra.nodes.size+1 ≤ 4294967295)
    (start amount : UInt64) (startEq : start.toNat = offset) (amountEq : amount.toNat = length) (nonzero : amount ≠ 0)
    (bounds : start.toNat+amount.toNat ≤ W.allocation.extra.locations.size.bytes.toNat) :
    ∃ output, CandidateCurrentFnEntryRaw.operation W.allocation.extra tracker.global frame id W.pointer.value.provenance start amount = .ok output ∧
      output.tag = tracker.global.nextPointerTag ∧ output.global = (registered tracker.global frame id room).1 ∧
      output.frame = (registered tracker.global frame id room).2 ∧ output.access.status = .Completed ∧ output.child.outcome = .ok () ∧
      DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree output.global ∧
      ∃ child,output.child.tree.indexOfTag output.tag = some child ∧
        ParentInterpretation output.child.tree (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) ∧
        GeneralRangeMapOrigins.OwnedOn (S05CompletedAncestryReadMutable.Authority output.child.tree
          (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) output.global.protectedTags child)
          start (start+amount) output.child.tree.locations ∧
        output.child.tree.locations.size = W.allocation.extra.locations.size ∧
        (∀ (position : Nat) (root : UniIndex),W.allocation.extra.roots[position]? = some root → output.child.tree.roots[position]? = some root) ∧
        (∀ index node,W.allocation.extra.nodes.get index = some node →
          ∃ next,output.child.tree.nodes.get index = some next ∧ next.tag = node.tag ∧ next.parent = node.parent ∧
            next.isExposed = node.isExposed ∧ next.defaultInitialPermission = node.defaultInitialPermission) ∧
        (∃ node,output.child.tree.nodes.get child = some node ∧ node.tag = output.tag ∧
          match W.pointer.value.provenance with
          | .concrete _ _ => node.parent = some W.pointer.grant
          | .wildcard => node.parent = none) ∧
        (∀ byte, Window id offset length byte → byte.2 < W.allocation.len ∧
          Embeds (W.allocation.setExtra output.child.tree) output.global.protectedTags
            (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) child byte.2 .exclusive) := by
  obtain ⟨output,actual,tag,global,callFrame,readDone,childDone,afterRuntime,child,lookup,parents,owned,capacity,rootSlots,oldFields,childNode⟩ :=
    invoke_selected W runtime frame room exclusive distinct short nodeRoom start amount startEq amountEq nonzero bounds
  refine ⟨output,actual,tag,global,callFrame,readDone,childDone,afterRuntime,child,lookup,parents,owned,capacity,rootSlots,oldFields,childNode,?_⟩
  intro byte inside
  refine ⟨(W.window byte inside).1,?_⟩
  have noWrap : start.toNat+amount.toNat < 2^64 := Nat.lt_of_le_of_lt bounds (UInt64.toNat_lt W.allocation.extra.locations.size.bytes)
  have endEq : (start+amount).toNat = start.toNat+amount.toNat := by simp only [UInt64.toNat_add,Nat.mod_eq_of_lt noWrap]
  have byteLower : start.toNat ≤ byte.2 := by have interval := inside.2;omega
  have byteUpper : byte.2 < (start+amount).toNat := by have interval := inside.2;omega
  intro segment member lower upper index node present
  simp only [Allocation.setExtra,Allocation.mapExtra] at member lower upper present ⊢
  obtain ⟨position,valid,same⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
  subst segment
  have rights := owned position valid (by omega) (by omega) (by omega) index node present
  have realized := CandidateCurrentGrantRuntime.realized _ _ (afterRuntime.possible position valid index node present)
    ((afterRuntime.formed.profile position valid).present index node present)
  constructor
  · intro below
    exact local_token _ _ realized (rights.1 below)
  · intro clash
    apply Classical.byContradiction
    intro outside
    exact foreign_no_clash _ _ realized (rights.2 outside) clash


set_option linter.unusedVariables false in
theorem invoke_resources {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (state : DuplicatePrefixRuntimeInput.State before tracker)
    (highwater : ∀ row ∈ before.memory.live.toList, GeneralBorrowForestTagHighWater.Below row.2.allocation.extra
      tracker.global.protectedTags tracker.global.nextPointerTag)
    (frame : FrameState) (room : tracker.global.nextPointerTag.value < 18446744073709551615)
    (exclusive : demandOf mode = .exclusive) (distinct : W.allocation.extra.roots.toList.Nodup)
    (short : W.allocation.extra.nodes.size < 65536) (nodeRoom : W.allocation.extra.nodes.size+1 ≤ 4294967295)
    (start amount : UInt64) (startEq : start.toNat = offset) (amountEq : amount.toNat = length) (nonzero : amount ≠ 0)
    (bounds : start.toNat+amount.toNat ≤ W.allocation.extra.locations.size.bytes.toNat) :
    ∃ output, CandidateCurrentFnEntryRaw.operation W.allocation.extra tracker.global frame id W.pointer.value.provenance start amount = .ok output ∧
      output.tag = tracker.global.nextPointerTag ∧ output.global = (registered tracker.global frame id room).1 ∧
      output.frame = (registered tracker.global frame id room).2 ∧ output.access.status = .Completed ∧ output.child.outcome = .ok () ∧
      DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree output.global ∧
      ∃ child,output.child.tree.indexOfTag output.tag = some child ∧
        ParentInterpretation output.child.tree (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) ∧
        GeneralRangeMapOrigins.OwnedOn (S05CompletedAncestryReadMutable.Authority output.child.tree
          (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) output.global.protectedTags child)
          start (start+amount) output.child.tree.locations ∧
        output.child.tree.locations.size = W.allocation.extra.locations.size ∧
        (∀ (position : Nat) (root : UniIndex),W.allocation.extra.roots[position]? = some root → output.child.tree.roots[position]? = some root) ∧
        (∀ index node,W.allocation.extra.nodes.get index = some node →
          ∃ next,output.child.tree.nodes.get index = some next ∧ next.tag = node.tag ∧ next.parent = node.parent ∧
            next.isExposed = node.isExposed ∧ next.defaultInitialPermission = node.defaultInitialPermission) ∧
        (∃ node,output.child.tree.nodes.get child = some node ∧ node.tag = output.tag ∧
          match W.pointer.value.provenance with
          | .concrete _ _ => node.parent = some W.pointer.grant
          | .wildcard => node.parent = none) ∧
        (∀ byte, Window id offset length byte → byte.2 < W.allocation.len ∧
          Embeds (W.allocation.setExtra output.child.tree) output.global.protectedTags
            (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) child byte.2 .exclusive) := by
  exact invoke_resources_selected W runtime frame room exclusive distinct short nodeRoom start amount startEq amountEq nonzero bounds

/-- The concrete pointer returned by retagging has unchanged address bits.
Its family slot is appended; no initial family is overwritten or conflated. -/
def child_pointer {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode) (tag : BorTag) (child : UniIndex) : PointerInstance :=
  ⟨id,{W.pointer.value with provenance := .concrete id tag},child⟩

/-- An OUTPUT borrow witness, not a new Interpretation or an initial validity
condition. In particular it neither overwrites the source owner nor asserts
that its old parent loan is suspended. Post-installation SpatialDelegation and
arbitrary copied-family adequacy remain separate obligations. -/
structure BorrowWitness {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode)
    (output : GeneralBorrowForestFnEntry.Output) (child : UniIndex) (start amount : UInt64) where
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree output.global
  parents : ParentInterpretation output.child.tree (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant)
  parentLoanAt : data.interpretation.loans[owner]? = some W.loan
  parentFamilyAt : data.interpretation.pointers[W.loan.pointer]? = some W.pointer
  node : TreeNode
  nodeAt : output.child.tree.nodes.get child = some node
  tag : node.tag = output.tag
  constructor : match W.pointer.value.provenance with
    | .concrete _ _ => node.parent = some W.pointer.grant
    | .wildcard => node.parent = none
  edge : (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant).parents[child.toNat]? = some (some W.pointer.grant)
  binding : PointerBinds (W.allocation.setExtra output.child.tree) (child_pointer W output.tag child)
  address : (child_pointer W output.tag child).value.offset = W.pointer.value.offset
  familyAt : (data.interpretation.pointers.push (child_pointer W output.tag child))[data.interpretation.pointers.size]? = some (child_pointer W output.tag child)
  oldFamilies : ∀ (index : Nat) (pointer : PointerInstance),data.interpretation.pointers[index]? = some pointer →
    (data.interpretation.pointers.push (child_pointer W output.tag child))[index]? = some pointer
  distinctFamily : W.loan.pointer ≠ data.interpretation.pointers.size
  /-- If recorded, the new wildcard-root attachment names the PARENT family,
  not the freshly appended child's family. -/
  originFamily : (CandidateCurrentJointCall.Attachment.mk id child W.loan.pointer).family = W.loan.pointer
  owned : GeneralRangeMapOrigins.OwnedOn (S05CompletedAncestryReadMutable.Authority output.child.tree
    (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) output.global.protectedTags child)
    start (start+amount) output.child.tree.locations
  window : ∀ byte,Window id offset length byte → byte.2 < W.allocation.len ∧
    Embeds (W.allocation.setExtra output.child.tree) output.global.protectedTags
      (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) child byte.2 .exclusive
  capacity : output.child.tree.locations.size = W.allocation.extra.locations.size
  oldRoots : ∀ (position : Nat) (root : UniIndex),W.allocation.extra.roots[position]? = some root → output.child.tree.roots[position]? = some root
  oldNodes : ∀ index node,W.allocation.extra.nodes.get index = some node →
    ∃ next,output.child.tree.nodes.get index = some next ∧ next.tag = node.tag ∧ next.parent = node.parent ∧
      next.isExposed = node.isExposed ∧ next.defaultInitialPermission = node.defaultInitialPermission

theorem correlated_borrow_selected {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (frame : FrameState) (room : tracker.global.nextPointerTag.value < 18446744073709551615)
    (exclusive : demandOf mode = .exclusive) (distinct : W.allocation.extra.roots.toList.Nodup)
    (short : W.allocation.extra.nodes.size < 65536) (nodeRoom : W.allocation.extra.nodes.size+1 ≤ 4294967295)
    (start amount : UInt64) (startEq : start.toNat = offset) (amountEq : amount.toNat = length) (nonzero : amount ≠ 0)
    (bounds : start.toNat+amount.toNat ≤ W.allocation.extra.locations.size.bytes.toNat) :
    ∃ output child,CandidateCurrentFnEntryRaw.operation W.allocation.extra tracker.global frame id W.pointer.value.provenance start amount = .ok output ∧
      output.tag = tracker.global.nextPointerTag ∧ output.global = (registered tracker.global frame id room).1 ∧
      output.frame = (registered tracker.global frame id room).2 ∧ output.access.status = .Completed ∧ output.child.outcome = .ok () ∧
      output.child.tree.indexOfTag output.tag = some child ∧ Nonempty (BorrowWitness W output child start amount) := by
  obtain ⟨output,actual,tag,global,callFrame,readDone,childDone,runtime,child,lookup,parents,owned,capacity,rootSlots,oldFields,childNode,window⟩ :=
    invoke_resources_selected W runtime frame room exclusive distinct short nodeRoom start amount startEq amountEq nonzero bounds
  obtain ⟨node,nodeAt,nodeTag,constructor⟩ := childNode
  have binding : PointerBinds (W.allocation.setExtra output.child.tree) (child_pointer W output.tag child) := by
    refine ⟨node,nodeAt,?_,?_⟩
    · simpa only [child_pointer,Allocation.setExtra,Allocation.mapExtra,nodeTag,BorrowTree.indexOfTag] using lookup
    · change id = id ∧ output.tag = node.tag
      exact ⟨rfl,nodeTag.symm⟩
  refine ⟨output,child,actual,tag,global,callFrame,readDone,childDone,lookup,⟨?_⟩⟩
  refine ⟨runtime,parents,W.loanAt,W.pointerAt,node,nodeAt,nodeTag,constructor,
    S05ConcreteProtectedChildCompletion.child_edge _ _ _,binding,rfl,?_,?_,?_,rfl,owned,window,capacity,rootSlots,oldFields⟩
  · simp only [Array.getElem?_push,ite_true]
  · intro index pointer present
    have valid := (Array.getElem?_eq_some_iff.mp present).1
    simpa only [Array.getElem?_push,show index ≠ data.interpretation.pointers.size by omega,↓reduceIte] using present
  · have valid := (Array.getElem?_eq_some_iff.mp W.pointerAt).1
    omega

theorem invoke_framed_selected {before tracker data owner id offset length mode returnOwner returnOffset}
    (W : UniformWindow before tracker data owner id offset length mode)
    (V : UniformWindow before tracker data returnOwner id returnOffset 1 .ret)
    (allocationEq : V.allocation = W.allocation) (completionEq : V.precise.completion = W.precise.completion)
    (separate : ∀ byte,Window id offset length byte → Window id returnOffset 1 byte → False)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (frame : FrameState) (room : tracker.global.nextPointerTag.value < 18446744073709551615)
    (exclusive : demandOf mode = .exclusive) (distinct : W.allocation.extra.roots.toList.Nodup)
    (short : W.allocation.extra.nodes.size < 65536) (nodeRoom : W.allocation.extra.nodes.size+1 ≤ 4294967295)
    (start amount : UInt64) (startEq : start.toNat = offset) (amountEq : amount.toNat = length) (nonzero : amount ≠ 0)
    (bounds : start.toNat+amount.toNat ≤ W.allocation.extra.locations.size.bytes.toNat) :
    ∃ output child,CandidateCurrentFnEntryRaw.operation W.allocation.extra tracker.global frame id W.pointer.value.provenance start amount = .ok output ∧
      Nonempty (BorrowWitness W output child start amount) ∧
      GeneralRangeMapOrigins.OwnedOn (S05CompletedAncestryReadMutable.Authority output.child.tree
        (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) output.global.protectedTags V.pointer.grant)
        (UInt64.ofNat returnOffset) (UInt64.ofNat returnOffset+1) output.child.tree.locations ∧
      PointerBinds (W.allocation.setExtra output.child.tree) V.pointer ∧
      (∀ byte,Window id returnOffset 1 byte → byte.2 < V.allocation.len ∧
        Embeds (V.allocation.setExtra output.child.tree) output.global.protectedTags
          (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) V.pointer.grant byte.2 .exclusive) := by
  obtain ⟨output,child,actual,tag,global,callFrame,readDone,childDone,lookup,⟨witness⟩⟩ :=
    correlated_borrow_selected W runtime frame room exclusive distinct short nodeRoom start amount startEq amountEq nonzero bounds
  let registration := registered tracker.global frame id room
  let accessed := W.allocation.extra.performBorrowAccessRange
    (extra W.pointer.value.provenance)
    (Size.ofBytes start) (Size.ofBytes amount) .Read registration.1.protectedTags .VisitChildrenOfAccessed
  obtain ⟨_,held,_,_,_,fresh⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare W.allocation.extra tracker.global frame id room runtime
  obtain ⟨_,afterRuntime,parents,_,nodes,roots,tags,capacity⟩ := prepare_read_selected W runtime frame room exclusive distinct short start amount startEq amountEq bounds
  have retRuntime : DuplicatePrefixBorrowContract.RuntimeFacts V.allocation.extra tracker.global := by rw [allocationEq];exact runtime
  let retCurrent := registered_window V retRuntime frame room
  have registeredRetRuntime := (GeneralBorrowFnEntryRegistrationRuntime.prepare V.allocation.extra tracker.global frame id room retRuntime).2.2.2.1
  have retByteBound := (V.window (id,returnOffset) ⟨rfl,Nat.le_refl _,by omega⟩).1
  have retFits : returnOffset+1 < 2^64 := by
    have capacityBound := UInt64.toNat_lt V.allocation.byteSize.bytes
    have extent := V.issued.capability.extent
    omega
  let retStart := UInt64.ofNat returnOffset
  have retStartEq : retStart.toNat = returnOffset := by simp only [retStart,UInt64.toNat_ofNat',Nat.mod_eq_of_lt (by omega : returnOffset < 2^64)]
  have retEndEq : (retStart+1).toNat = returnOffset+1 := by
    rw [UInt64.toNat_add,retStartEq,show (1 : UInt64).toNat = 1 from rfl,Nat.mod_eq_of_lt retFits]
  have beforeBool := window_owned retCurrent (by simp [demandOf]) registeredRetRuntime retStart (retStart+1) (by omega) (by omega)
  change GeneralRangeMapOrigins.OwnedOn (S05CompletedAncestryReadMutable.Authority V.allocation.extra V.precise.completion registration.1.protectedTags V.pointer.grant)
    retStart (retStart+1) V.allocation.extra.locations at beforeBool
  rw [allocationEq,completionEq] at beforeBool
  have disjoint : ∀ point : UInt64,retStart.toNat ≤ point.toNat → point.toNat < (retStart+1).toNat →
      point.toNat < start.toNat ∨ (start+amount).toNat ≤ point.toNat := by
    intro point lower upper
    have pointEq : point.toNat = returnOffset := by omega
    by_cases early : point.toNat < start.toNat
    · exact Or.inl early
    · apply Or.inr
      have noWrap : start.toNat+amount.toNat < 2^64 := Nat.lt_of_le_of_lt bounds (UInt64.toNat_lt W.allocation.extra.locations.size.bytes)
      have endEq : (start+amount).toNat = start.toNat+amount.toNat := by simp only [UInt64.toNat_add,Nat.mod_eq_of_lt noWrap]
      apply Nat.le_of_not_gt
      intro overlap
      exact separate (id,point.toNat) ⟨rfl,by omega,by omega⟩ ⟨rfl,by omega,by omega⟩
  have boolRead := GeneralBorrowRangeOutsideOwned.owned
    (S05CompletedAncestryReadMutable.Authority W.allocation.extra W.precise.completion registration.1.protectedTags V.pointer.grant)
    W.allocation.extra (extra W.pointer.value.provenance)
    (Size.ofBytes start) (Size.ofBytes amount) .Read registration.1.protectedTags .VisitChildrenOfAccessed runtime.formed.well bounds retStart (retStart+1) disjoint beforeBool
  have afterBool : GeneralRangeMapOrigins.OwnedOn
      (S05CompletedAncestryReadMutable.Authority accessed.tree W.precise.completion registration.1.protectedTags V.pointer.grant)
      retStart (retStart+1) accessed.tree.locations := by
    intro cursor valid positive beforeUpper afterLower index node present
    exact boolRead cursor valid positive beforeUpper afterLower index node (by rw [←nodes];exact present)
  obtain ⟨parentNode,parentAt,_,binding⟩ := W.binding
  have parentAfter : accessed.tree.nodes.get W.pointer.grant = some parentNode := by rw [nodes];exact parentAt
  obtain ⟨targetNode,targetAt,_,targetBinding⟩ := V.binding
  rw [allocationEq] at targetAt
  have targetAfter : accessed.tree.nodes.get V.pointer.grant = some targetNode := by rw [nodes];exact targetAt
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping tracker.global.nextPointerTag := by rw [tags];exact fresh
  have childRoom : accessed.tree.nodes.size+1 ≤ 4294967295 := by change accessed.tree.nodes.data.size+1 ≤ _;rw [nodes];exact nodeRoom
  have childBounds : start.toNat+amount.toNat ≤ accessed.tree.locations.size.bytes.toNat := by rw [capacity];exact bounds
  have tagBound : tracker.global.nextPointerTag.value.toNat < registration.1.nextPointerTag.value.toNat := by
    have successor := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag room
    change tracker.global.nextPointerTag.value.toNat < (TypedRetagEmpty.successorTag tracker.global.nextPointerTag room).value.toNat
    omega
  have tagHeld : registration.1.protectedTags.contains tracker.global.nextPointerTag = true := by
    unfold ProtectedTags.contains
    rw [held]
    rfl
  have childEq := child_of_operation W.allocation.extra tracker.global frame id W.pointer.value.provenance start amount room output actual
  have sourceLookup : (accessed.tree.newChild (Size.ofBytes start)
      (extra W.pointer.value.provenance) tracker.global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes amount) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree.indexOfTag tracker.global.nextPointerTag = some child := by
    rw [←childEq,←tag]
    exact lookup
  have boolAfter : GeneralRangeMapOrigins.OwnedOn (S05CompletedAncestryReadMutable.Authority output.child.tree
      (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) output.global.protectedTags V.pointer.grant)
      retStart (retStart+1) output.child.tree.locations := by
    rw [childEq,global]
    cases provenance : W.pointer.value.provenance with
    | concrete suppliedId parentTag =>
      simp only [extra]
      rw [provenance] at binding
      have tagEq := binding.2
      have tagged : accessed.tree.indexOfTag parentNode.tag = some W.pointer.grant := afterRuntime.formed.allocator.nodeTags _ _ parentAfter
      obtain ⟨_,_,_,_,framedChild,framedLookup,framed⟩ := CurrentCallResourceChild.Disjoint.construct accessed.tree registration.1 W.precise.completion afterRuntime parents
        parentNode.tag tracker.global.nextPointerTag W.pointer.grant V.pointer.grant parentNode targetNode tagged parentAfter targetAfter freshAfter childRoom tagBound tagHeld
        start amount retStart (retStart+1) nonzero childBounds disjoint afterBool
      have same : framedChild = child := Option.some.inj (framedLookup.symm.trans (by simpa only [extra,provenance,tagEq] using sourceLookup))
      subst framedChild
      simpa only [accessed,registration,extra,provenance,tagEq] using framed
    | wildcard =>
      simp only [extra]
      obtain ⟨framedChild,framedLookup,framed⟩ := CurrentCallResourceChild.WildcardDisjoint.disjoint accessed.tree registration.1 W.precise.completion afterRuntime parents
        tracker.global.nextPointerTag freshAfter childRoom tagBound tagHeld W.pointer.grant parentNode parentAfter
        start amount retStart (retStart+1) nonzero childBounds V.pointer.grant ⟨targetNode,targetAfter⟩ disjoint afterBool
      have same : framedChild = child := Option.some.inj (framedLookup.symm.trans (by simpa only [extra,provenance] using sourceLookup))
      subst framedChild
      simpa only [accessed,registration,extra,provenance] using framed
  have currentBinding : PointerBinds (W.allocation.setExtra output.child.tree) V.pointer := by
    obtain ⟨next,nextAt,nextTag,_,nextExposed,_⟩ := witness.oldNodes V.pointer.grant targetNode targetAt
    refine ⟨next,nextAt,?_,?_⟩
    · exact witness.runtime.formed.allocator.nodeTags _ _ nextAt
    · cases provenance : V.pointer.value.provenance with
      | concrete suppliedId targetTag =>
        rw [provenance] at targetBinding
        simpa only [provenance,nextTag] using targetBinding
      | wildcard =>
        rw [provenance] at targetBinding
        simpa only [provenance,nextExposed] using targetBinding
  refine ⟨output,child,actual,⟨witness⟩,boolAfter,currentBinding,?_⟩
  intro byte inside
  refine ⟨(V.window byte inside).1,?_⟩
  have byteEq : byte.2 = returnOffset := by have interval := inside.2;omega
  intro segment member lower upper index node present
  simp only [Allocation.setExtra,Allocation.mapExtra] at member lower upper present ⊢
  obtain ⟨position,valid,same⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
  subst segment
  have rights := boolAfter position valid (by omega) (by omega) (by omega) index node present
  have realized := CandidateCurrentGrantRuntime.realized _ _ (witness.runtime.possible position valid index node present)
    ((witness.runtime.formed.profile position valid).present index node present)
  constructor
  · intro below
    exact local_token _ _ realized (rights.1 below)
  · intro clash
    apply Classical.byContradiction
    intro outside
    exact foreign_no_clash _ _ realized (rights.2 outside) clash


set_option linter.unusedVariables false in
theorem invoke_framed {before tracker data owner id offset length mode returnOwner returnOffset}
    (W : UniformWindow before tracker data owner id offset length mode)
    (V : UniformWindow before tracker data returnOwner id returnOffset 1 .ret)
    (allocationEq : V.allocation = W.allocation) (completionEq : V.precise.completion = W.precise.completion)
    (separate : ∀ byte,Window id offset length byte → Window id returnOffset 1 byte → False)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (state : DuplicatePrefixRuntimeInput.State before tracker)
    (highwater : ∀ row ∈ before.memory.live.toList, GeneralBorrowForestTagHighWater.Below row.2.allocation.extra
      tracker.global.protectedTags tracker.global.nextPointerTag)
    (frame : FrameState) (room : tracker.global.nextPointerTag.value < 18446744073709551615)
    (exclusive : demandOf mode = .exclusive) (distinct : W.allocation.extra.roots.toList.Nodup)
    (short : W.allocation.extra.nodes.size < 65536) (nodeRoom : W.allocation.extra.nodes.size+1 ≤ 4294967295)
    (start amount : UInt64) (startEq : start.toNat = offset) (amountEq : amount.toNat = length) (nonzero : amount ≠ 0)
    (bounds : start.toNat+amount.toNat ≤ W.allocation.extra.locations.size.bytes.toNat) :
    ∃ output child,CandidateCurrentFnEntryRaw.operation W.allocation.extra tracker.global frame id W.pointer.value.provenance start amount = .ok output ∧
      Nonempty (BorrowWitness W output child start amount) ∧
      GeneralRangeMapOrigins.OwnedOn (S05CompletedAncestryReadMutable.Authority output.child.tree
        (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) output.global.protectedTags V.pointer.grant)
        (UInt64.ofNat returnOffset) (UInt64.ofNat returnOffset+1) output.child.tree.locations ∧
      PointerBinds (W.allocation.setExtra output.child.tree) V.pointer ∧
      (∀ byte,Window id returnOffset 1 byte → byte.2 < V.allocation.len ∧
        Embeds (V.allocation.setExtra output.child.tree) output.global.protectedTags
          (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) V.pointer.grant byte.2 .exclusive) := by
  exact invoke_framed_selected W V allocationEq completionEq separate runtime frame room exclusive distinct short nodeRoom start amount startEq amountEq nonzero bounds


set_option linter.unusedVariables false in
theorem correlated_borrow {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (state : DuplicatePrefixRuntimeInput.State before tracker)
    (highwater : ∀ row ∈ before.memory.live.toList, GeneralBorrowForestTagHighWater.Below row.2.allocation.extra
      tracker.global.protectedTags tracker.global.nextPointerTag)
    (frame : FrameState) (room : tracker.global.nextPointerTag.value < 18446744073709551615)
    (exclusive : demandOf mode = .exclusive) (distinct : W.allocation.extra.roots.toList.Nodup)
    (short : W.allocation.extra.nodes.size < 65536) (nodeRoom : W.allocation.extra.nodes.size+1 ≤ 4294967295)
    (start amount : UInt64) (startEq : start.toNat = offset) (amountEq : amount.toNat = length) (nonzero : amount ≠ 0)
    (bounds : start.toNat+amount.toNat ≤ W.allocation.extra.locations.size.bytes.toNat) :
    ∃ output child,CandidateCurrentFnEntryRaw.operation W.allocation.extra tracker.global frame id W.pointer.value.provenance start amount = .ok output ∧
      output.tag = tracker.global.nextPointerTag ∧ output.global = (registered tracker.global frame id room).1 ∧
      output.frame = (registered tracker.global frame id room).2 ∧ output.access.status = .Completed ∧ output.child.outcome = .ok () ∧
      output.child.tree.indexOfTag output.tag = some child ∧ Nonempty (BorrowWitness W output child start amount) := by
  exact correlated_borrow_selected W runtime frame room exclusive distinct short nodeRoom start amount startEq amountEq nonzero bounds

end
end DuplicatePrefix.CurrentCallResourceFnEntry

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallResourceFnEntry.").length != 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved current resource FnEntry dependency {dependency}"
