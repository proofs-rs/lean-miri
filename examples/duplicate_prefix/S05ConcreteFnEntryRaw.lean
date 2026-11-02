import duplicate_prefix.S05CompletedAncestryReadMutable
import duplicate_prefix.GeneralBorrowParentTagInvariant
import duplicate_prefix.GeneralBorrowProtectedChildOrder
import duplicate_prefix.S05ConcreteProtectedChildCompletion
import duplicate_prefix.S05ConcreteProtectedChildAuthority
import duplicate_prefix.GeneralBorrowFnEntryRegistrationRuntime
import duplicate_prefix.CandidateCurrentJointRawReplacement
import duplicate_prefix.GeneralBorrowForestFnEntry
import duplicate_prefix.GeneralBorrowProtectedCapabilityConstructor
import duplicate_prefix.GeneralBorrowConstructorChildActivity

/-! Concrete FnEntry preparation from initial completed mutable raw authority.
Actual global allocation, Strong registration and associated ranged Read are
composed without the legacy Positive packet or any successful-operation premise.
The wildcard max=none lane and full joint-ownership transport remain separate. -/
namespace DuplicatePrefix.S05ConcreteFnEntryRaw
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowExposedNonleafPrimaryPath OrdinaryBorrowAuthority
open GeneralBorrowWildcardParentTagOrder GeneralRangeMapOrigins GeneralRangeMapState
open S05CompletedAncestryReadMutable GeneralBorrowFnEntryRegistration
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Strong registration names a fresh tag, so all actual old-node protector
flags remain exactly the flags under which initial ownership was supplied. -/
private theorem registered_flags (tree : BorrowTree) (global : GlobalState) (frame : FrameState)
    (allocation : AllocId) (room : global.nextPointerTag.value < 18446744073709551615)
    (fresh : GeneralBorrowProtector.Fresh tree global.nextPointerTag) :
    ∀ index node, tree.nodes.get index = some node →
      (registered global frame allocation room).1.protectedTags.contains node.tag = global.protectedTags.contains node.tag := by
  intro index node present
  exact ProtectorInsertion.contains_other global.protectedTags global.nextPointerTag node.tag .StrongProtector
    (fresh (index,node) (Array.mem_toList_iff.mp ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes index node).mpr present)))

/-- The exact registered parent Read completes and retains current raw mutable
authority on its window, with the same finite completed origin assignment. -/
theorem prepare_read (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (completion : Completion) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (complete : Completes tree completion) (order : ParentTagOrder tree)
    (position : Nat) (selected parent : UniIndex) (selectedNode parentNode : TreeNode)
    (slot : tree.roots[position]? = some selected) (selectedPresent : tree.nodes.get selected = some selectedNode)
    (parentPresent : tree.nodes.get parent = some parentNode) (parentPath : Path tree selected parent)
    (tagRoom : global.nextPointerTag.value < 18446744073709551615)
    (offset len : UInt64) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (owned : OwnedOn (Authority tree completion global.protectedTags parent) offset (offset+len) tree.locations)
    (short : tree.nodes.size < 65536) (mode : ChildrenVisitMode) :
    let registration := registered global frame allocation tagRoom
    let accessed := tree.performBorrowAccessRange (.concrete parentNode.tag) (Size.ofBytes offset)
      (Size.ofBytes len) .Read registration.1.protectedTags mode
    accessed.status = .Completed ∧ DuplicatePrefixBorrowContract.RuntimeFacts accessed.tree registration.1 ∧
      Completes accessed.tree completion ∧
      OwnedOn (Authority accessed.tree completion registration.1.protectedTags parent) offset (offset+len) accessed.tree.locations ∧
      accessed.tree.nodes = tree.nodes ∧ accessed.tree.roots = tree.roots ∧ accessed.tree.tagMapping = tree.tagMapping ∧
      accessed.tree.locations.size = tree.locations.size := by
  obtain ⟨_,_,_,registeredRuntime,nodeFresh,_⟩ :=
    GeneralBorrowFnEntryRegistrationRuntime.prepare tree global frame allocation tagRoom runtime
  let registration := registered global frame allocation tagRoom
  let accessed := tree.performBorrowAccessRange (.concrete parentNode.tag) (Size.ofBytes offset)
    (Size.ofBytes len) .Read registration.1.protectedTags mode
  have flags := registered_flags tree global frame allocation tagRoom nodeFresh
  obtain ⟨depth⟩ := registeredRuntime.formed.depth
  have rowInput : OwnedOn (fun location => GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location ∧
      Authority tree completion registration.1.protectedTags parent location) offset (offset+len) tree.locations := by
    intro cursor valid positive start stop
    refine ⟨registeredRuntime.possible cursor valid,?_⟩
    intro index node present
    rw [flags index node present]
    exact owned cursor valid positive start stop index node present
  have range := S05CompletedAncestryReadMutable.range tree completion registration.1.protectedTags complete
    registeredRuntime.formed.toGraphState depth order position selected parent selectedNode parentNode
    slot selectedPresent parentPresent parentPath (Size.ofBytes offset) (Size.ofBytes len) offset (offset+len)
    rowInput registeredRuntime.formed.well
    (fun cursor valid => ⟨registeredRuntime.coherent cursor valid,registeredRuntime.formed.profile cursor valid,
      registeredRuntime.possible cursor valid⟩)
    bounds (Nat.le_refl _) (Nat.le_refl _) short mode
  have nodes : accessed.tree.nodes = tree.nodes := range.nodes
  have same : accessed.tree = {tree with locations := accessed.tree.locations} := range.tree_eq
  have afterRuntime : DuplicatePrefixBorrowContract.RuntimeFacts accessed.tree registration.1 := by
    rw [same]
    refine ⟨⟨⟨GeneralBorrowStructuralHistoryState.graph_locations tree _ registeredRuntime.formed.toGraphState,
      range.well⟩,?_⟩,?_,?_,⟨registeredRuntime.below.mapping,registeredRuntime.below.protectors⟩⟩
    · intro cursor valid
      exact ⟨(range.runtime cursor valid).2.1.present,(range.runtime cursor valid).2.1.vacant⟩
    · intro cursor valid
      exact (range.runtime cursor valid).1
    · intro cursor valid
      exact (range.runtime cursor valid).2.2
  have afterComplete : Completes accessed.tree completion := by
    rw [same]
    exact CandidateCurrentJointRawReplacement.completes tree completion _ complete
  refine ⟨range.completed,afterRuntime,afterComplete,?_,range.nodes,range.roots,range.tags,range.capacity⟩
  intro cursor valid positive start stop
  have authority := (range.rows cursor valid positive start stop).2
  intro index node present
  exact authority index node (by rw [←nodes];exact present)

/-- The actual concrete FnEntry borrowing pipeline completes from independent
initial raw authority. Allocation/registration/Read/constructor are the real
operations; the new completed origin and protected child capability are outputs.
This is not whole MIR entry or ordinary-input coverage. -/
theorem invoke (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (completion : Completion) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (complete : Completes tree completion) (order : ParentTagOrder tree)
    (position : Nat) (selected parent : UniIndex) (selectedNode parentNode : TreeNode)
    (slot : tree.roots[position]? = some selected) (selectedPresent : tree.nodes.get selected = some selectedNode)
    (parentPresent : tree.nodes.get parent = some parentNode) (parentPath : Path tree selected parent)
    (tagRoom : global.nextPointerTag.value < 18446744073709551615)
    (nodeRoom : tree.nodes.size+1 ≤ 4294967295) (short : tree.nodes.size < 65536)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (owned : OwnedOn (Authority tree completion global.protectedTags parent) offset (offset+len) tree.locations) :
    ∃ output, GeneralBorrowForestFnEntry.operation tree global frame allocation parentNode.tag offset len
        .VisitChildrenOfAccessed = .ok output ∧
      output.tag = global.nextPointerTag ∧
      output.global = (registered global frame allocation tagRoom).1 ∧
      output.frame.protectedTags = frame.protectedTags.push (allocation,output.tag) ∧
      output.access.status = .Completed ∧ output.child.outcome = .ok () ∧
      DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree output.global ∧
      output.child.tree.locations.size = tree.locations.size ∧ output.child.tree.nodes.size ≤ tree.nodes.size+1 ∧
      ∃ child, output.child.tree.indexOfTag output.tag = some child ∧
        output.child.tree.roots = tree.roots ∧
        Completes output.child.tree (S05ConcreteProtectedChildCompletion.extend completion child parent) ∧
        OwnedOn (Authority output.child.tree (S05ConcreteProtectedChildCompletion.extend completion child parent)
          output.global.protectedTags child) offset (offset+len) output.child.tree.locations ∧
        OwnedOn (fun location => Nonempty (DuplicatePrefixBorrowAuthorization.Normal output.child.tree
          location output.global.protectedTags child)) offset (offset+len) output.child.tree.locations ∧
        (∀ ancestor, Below completion ancestor parent →
          Below (S05ConcreteProtectedChildCompletion.extend completion child parent) ancestor child) ∧
        GeneralBorrowFreshActiveWithin.ActiveWithin output.child.tree child .Write offset (offset+len) ∧
        ParentTagOrder output.child.tree ∧
        (∀ index node, tree.nodes.get index = some node →
          ∃ next, output.child.tree.nodes.get index = some next ∧ next.tag = node.tag ∧
            next.parent = node.parent ∧ next.isExposed = node.isExposed) ∧
        (∃ node, output.child.tree.nodes.get child = some node ∧ node.tag = output.tag) := by
  obtain ⟨allocated,held,frameEq,registeredRuntime,_,fresh⟩ :=
    GeneralBorrowFnEntryRegistrationRuntime.prepare tree global frame allocation tagRoom runtime
  let registration := registered global frame allocation tagRoom
  let accessed := tree.performBorrowAccessRange (.concrete parentNode.tag) (Size.ofBytes offset)
    (Size.ofBytes len) .Read registration.1.protectedTags .VisitChildrenOfAccessed
  obtain ⟨readDone,afterRuntime,afterComplete,afterOwned,nodes,roots,tags,capacity⟩ :=
    prepare_read tree global frame allocation completion runtime complete order position selected parent selectedNode parentNode
      slot selectedPresent parentPresent parentPath tagRoom offset len bounds owned short .VisitChildrenOfAccessed
  have parentAfter : accessed.tree.nodes.get parent = some parentNode := by rw [nodes];exact parentPresent
  have selectedAfter : accessed.tree.nodes.get selected = some selectedNode := by rw [nodes];exact selectedPresent
  have slotAfter : accessed.tree.roots[position]? = some selected := by rw [roots];exact slot
  have parentPathAfter : Path accessed.tree selected parent :=
    GeneralBorrowPrimaryWitnessVisibility.path_nodes (before := accessed.tree) (after := tree) nodes.symm parentPath
  have tagged : accessed.tree.indexOfTag parentNode.tag = some parent :=
    (afterComplete.2.2.2.2.1 parent parentNode parentAfter).1
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping global.nextPointerTag := by rw [tags];exact fresh
  have room : accessed.tree.nodes.size+1 ≤ 4294967295 := by rw [nodes];exact nodeRoom
  have tagBound : global.nextPointerTag.value.toNat < registration.1.nextPointerTag.value.toNat := by
    have successor := GenericFunctionEntryNumerics.successor_value global.nextPointerTag tagRoom
    change global.nextPointerTag.value.toNat < (TypedRetagEmpty.successorTag global.nextPointerTag tagRoom).value.toNat
    omega
  have heldTag : registration.1.protectedTags.contains global.nextPointerTag = true := by
    unfold ProtectedTags.contains
    rw [held]
    rfl
  have afterBounds : offset.toNat+len.toNat ≤ accessed.tree.locations.size.bytes.toNat := by rw [capacity];exact bounds
  obtain ⟨depth⟩ := afterRuntime.formed.depth
  have fits : accessed.tree.nodes.data.size ≤ 4294967296 := by
    change accessed.tree.nodes.size ≤ _
    omega
  have normals : OwnedOn (fun location => Nonempty (DuplicatePrefixBorrowAuthorization.Normal
      accessed.tree location registration.1.protectedTags parent)) offset (offset+len) accessed.tree.locations := by
    intro cursor valid positive start stop
    have rights := afterOwned cursor valid positive start stop
    exact S05CompletedAncestryNormal.normal accessed.tree completion _ registration.1.protectedTags afterComplete
      afterRuntime.formed.toGraphState depth fits position selected parent selectedNode slotAfter selectedAfter parentPathAfter
      (fun index node present _ => (rights index node present).1)
      (fun index node present _ => (rights index node present).2)
  obtain ⟨childDone,childRuntime,childCapacity,growth,child,lookup,leaf,childComplete,ancestry⟩ :=
    S05ConcreteProtectedChildCompletion.construct accessed.tree registration.1 completion afterRuntime afterComplete
      parentNode.tag global.nextPointerTag parent parentNode tagged parentAfter freshAfter room tagBound heldTag offset len nonzero afterBounds
  obtain ⟨_,_,_,_,authorityChild,authorityLookup,_,childAuthority⟩ :=
    S05ConcreteProtectedChildAuthority.construct accessed.tree registration.1 completion afterRuntime afterComplete
      parentNode.tag global.nextPointerTag parent parentNode tagged parentAfter freshAfter room tagBound heldTag
      offset len nonzero afterBounds afterOwned
  have same : authorityChild = child := Option.some.inj (authorityLookup.symm.trans lookup)
  subst authorityChild
  obtain ⟨_,_,_,_,capabilityChild,capabilityLookup,childNormals⟩ :=
    GeneralBorrowProtectedCapabilityConstructor.construct accessed.tree registration.1 afterRuntime
      parentNode.tag global.nextPointerTag parent parentNode tagged parentAfter freshAfter room tagBound heldTag
      offset len nonzero afterBounds normals
  have same : capabilityChild = child := Option.some.inj (capabilityLookup.symm.trans lookup)
  subst capabilityChild
  obtain ⟨activityChild,activityLookup,activity⟩ := GeneralBorrowConstructorChildActivity.Protected.construct
    accessed.tree registration.1 afterRuntime parentNode.tag global.nextPointerTag parent parentNode tagged parentAfter
    freshAfter room offset len nonzero afterBounds
  have same : activityChild = child := Option.some.inj (activityLookup.symm.trans lookup)
  subst activityChild
  let output : GeneralBorrowForestFnEntry.Output := ⟨registration.1,registration.2,global.nextPointerTag,accessed,
    accessed.tree.newChild (Size.ofBytes offset) (.concrete parentNode.tag) global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true⟩
  have readOrder := GeneralBorrowParentTagInvariant.nodes_frame tree accessed.tree nodes order
  have older := GeneralBorrowParentTagInvariant.parent_below_fresh tree global runtime parent parentNode parentPresent
  have childOrder := GeneralBorrowProtectedChildOrder.construct accessed.tree registration.1 afterRuntime readOrder
    parentNode.tag global.nextPointerTag parent parentNode tagged parentAfter freshAfter room
    (UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp older))) offset len nonzero afterBounds
  obtain ⟨metadataChild,metadataLookup,metadataNode,_,_⟩ := GeneralBorrowProtectedChildMetadata.construct
    accessed.tree registration.1 afterRuntime parentNode.tag global.nextPointerTag parent parentNode tagged parentAfter
    freshAfter room offset len nonzero afterBounds
  have metadataEq : metadataChild = child := Option.some.inj (metadataLookup.symm.trans lookup)
  subst metadataChild
  refine ⟨output,?_,rfl,rfl,frameEq,readDone,childDone,childRuntime,childCapacity.trans capacity,?_,
    child,lookup,leaf.roots.trans roots,childComplete,childAuthority,childNormals,ancestry,activity,childOrder,?_,?_⟩
  · simp only [GeneralBorrowForestFnEntry.operation,allocated,Except.bind,Except.pure,bind,pure]
    rfl
  · rw [nodes] at growth
    exact growth
  · intro index node present
    exact leaf.old index node (by rw [nodes];exact present)
  · obtain ⟨node,nodeAt,tagEq,_⟩ := metadataNode
    exact ⟨node,nodeAt,tagEq⟩

end DuplicatePrefix.S05ConcreteFnEntryRaw

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05ConcreteFnEntryRaw." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved concrete FnEntry raw dependency {dependency}"
