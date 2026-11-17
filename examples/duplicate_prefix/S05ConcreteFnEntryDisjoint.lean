import duplicate_prefix.S05ConcreteFnEntryRaw
import duplicate_prefix.S05ConcreteProtectedChildDisjoint
import duplicate_prefix.GeneralBorrowRangeOutsideOwned
import duplicate_prefix.GeneralBorrowProtectedChildOrder
import duplicate_prefix.GeneralBorrowParentTagInvariant

/-! The concrete FnEntry pipeline frames a disjoint old Bool grant in the SAME
allocation. Source and Bool raw tables share one completed origin assignment.
This is not full Joint, typed memory entry, or ordinary-input admission. -/
namespace DuplicatePrefix.S05ConcreteFnEntryDisjoint
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowExposedNonleafPrimaryPath
open GeneralBorrowWildcardParentTagOrder GeneralRangeMapOrigins
open S05CompletedAncestryReadMutable GeneralBorrowFnEntryRegistration
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- An old same-allocation Bool window retains its raw authority through both
the actual associated Read and protected child insertion. Disjointness is a
physical footprint condition, independently derivable from joint contents. -/
theorem invoke_window (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (completion : Completion) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (complete : Completes tree completion) (order : ParentTagOrder tree)
    (position : Nat) (selected parent : UniIndex) (selectedNode parentNode : TreeNode)
    (slot : tree.roots[position]? = some selected) (selectedPresent : tree.nodes.get selected = some selectedNode)
    (parentPresent : tree.nodes.get parent = some parentNode) (parentPath : Path tree selected parent)
    (tagRoom : global.nextPointerTag.value < 18446744073709551615)
    (nodeRoom : tree.nodes.size+1 ≤ 4294967295) (short : tree.nodes.size < 65536)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (owned : OwnedOn (Authority tree completion global.protectedTags parent) offset (offset+len) tree.locations)
    (target : UniIndex) (targetNode : TreeNode) (targetPresent : tree.nodes.get target = some targetNode)
    (boolOffset boolLen : UInt64) (boolBounds : boolOffset.toNat+boolLen.toNat ≤ tree.locations.size.bytes.toNat)
    (disjoint : ∀ point : UInt64, boolOffset.toNat ≤ point.toNat → point.toNat < (boolOffset+boolLen).toNat →
      point.toNat < offset.toNat ∨ (offset+len).toNat ≤ point.toNat)
    (boolOwned : OwnedOn (Authority tree completion global.protectedTags target)
      boolOffset (boolOffset+boolLen) tree.locations) :
    ∃ output, GeneralBorrowForestFnEntry.operation tree global frame allocation parentNode.tag offset len
        .VisitChildrenOfAccessed = .ok output ∧
      output.tag = global.nextPointerTag ∧
      output.global = (registered global frame allocation tagRoom).1 ∧
      output.frame.protectedTags = frame.protectedTags.push (allocation,output.tag) ∧
      output.access.status = .Completed ∧ output.child.outcome = .ok () ∧
      DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree output.global ∧
      output.child.tree.locations.size = tree.locations.size ∧ output.child.tree.nodes.size ≤ tree.nodes.size+1 ∧
      boolOffset.toNat+boolLen.toNat ≤ output.child.tree.locations.size.bytes.toNat ∧
      ParentTagOrder output.child.tree ∧
      output.child.tree.indexOfTag targetNode.tag = some target ∧
      ∃ child, output.child.tree.indexOfTag output.tag = some child ∧
        output.child.tree.roots = tree.roots ∧
        Completes output.child.tree (S05ConcreteProtectedChildCompletion.extend completion child parent) ∧
        OwnedOn (Authority output.child.tree (S05ConcreteProtectedChildCompletion.extend completion child parent)
          output.global.protectedTags child) offset (offset+len) output.child.tree.locations ∧
        OwnedOn (Authority output.child.tree (S05ConcreteProtectedChildCompletion.extend completion child parent)
          output.global.protectedTags target) boolOffset (boolOffset+boolLen) output.child.tree.locations := by
  obtain ⟨output,actual,tag,outputGlobal,frameEq,readDone,childDone,afterRuntime,capacity,growth,
    child,lookup,roots,childComplete,sourceOwned,_,_,_⟩ :=
    S05ConcreteFnEntryRaw.invoke tree global frame allocation completion runtime complete order position selected parent
      selectedNode parentNode slot selectedPresent parentPresent parentPath tagRoom nodeRoom short offset len nonzero bounds owned
  obtain ⟨allocated,held,_,_,nodeFresh,fresh⟩ :=
    GeneralBorrowFnEntryRegistrationRuntime.prepare tree global frame allocation tagRoom runtime
  let registration := registered global frame allocation tagRoom
  let accessed := tree.performBorrowAccessRange (.concrete parentNode.tag) (Size.ofBytes offset)
    (Size.ofBytes len) .Read registration.1.protectedTags .VisitChildrenOfAccessed
  let canonical : GeneralBorrowForestFnEntry.Output := ⟨registration.1,registration.2,global.nextPointerTag,accessed,
    accessed.tree.newChild (Size.ofBytes offset) (.concrete parentNode.tag) global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true⟩
  have canonicalActual : GeneralBorrowForestFnEntry.operation tree global frame allocation parentNode.tag offset len
      .VisitChildrenOfAccessed = .ok canonical := by
    simp only [GeneralBorrowForestFnEntry.operation,allocated,Except.bind,Except.pure,bind,pure]
    rfl
  have outputEq : output = canonical := Except.ok.inj (actual.symm.trans canonicalActual)
  subst output
  obtain ⟨_,readRuntime,readComplete,_,readNodes,_,readTags,readCapacity⟩ :=
    S05ConcreteFnEntryRaw.prepare_read tree global frame allocation completion runtime complete order position selected parent
      selectedNode parentNode slot selectedPresent parentPresent parentPath tagRoom offset len bounds owned short .VisitChildrenOfAccessed
  have flags : ∀ index node, tree.nodes.get index = some node →
      registration.1.protectedTags.contains node.tag = global.protectedTags.contains node.tag := by
    intro index node present
    exact ProtectorInsertion.contains_other global.protectedTags global.nextPointerTag node.tag .StrongProtector
      (nodeFresh (index,node) (Array.mem_toList_iff.mp ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes index node).mpr present)))
  have beforeBool : OwnedOn (Authority tree completion registration.1.protectedTags target)
      boolOffset (boolOffset+boolLen) tree.locations := by
    intro cursor valid positive start stop index node present
    rw [flags index node present]
    exact boolOwned cursor valid positive start stop index node present
  have boolRead := GeneralBorrowRangeOutsideOwned.owned (Authority tree completion registration.1.protectedTags target)
    tree (.concrete parentNode.tag) (Size.ofBytes offset) (Size.ofBytes len) .Read registration.1.protectedTags
    .VisitChildrenOfAccessed runtime.formed.well bounds boolOffset (boolOffset+boolLen) disjoint beforeBool
  have afterBool : OwnedOn (Authority accessed.tree completion registration.1.protectedTags target)
      boolOffset (boolOffset+boolLen) accessed.tree.locations := by
    intro cursor valid positive start stop index node present
    exact boolRead cursor valid positive start stop index node (by rw [←readNodes];exact present)
  have parentAfter : accessed.tree.nodes.get parent = some parentNode := by rw [readNodes];exact parentPresent
  have targetAfter : accessed.tree.nodes.get target = some targetNode := by rw [readNodes];exact targetPresent
  have tagged : accessed.tree.indexOfTag parentNode.tag = some parent :=
    (readComplete.2.2.2.2.1 parent parentNode parentAfter).1
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping global.nextPointerTag := by rw [readTags];exact fresh
  have room : accessed.tree.nodes.size+1 ≤ 4294967295 := by rw [readNodes];exact nodeRoom
  have tagBound : global.nextPointerTag.value.toNat < registration.1.nextPointerTag.value.toNat := by
    have successor := GenericFunctionEntryNumerics.successor_value global.nextPointerTag tagRoom
    change global.nextPointerTag.value.toNat < (TypedRetagEmpty.successorTag global.nextPointerTag tagRoom).value.toNat
    omega
  have heldTag : registration.1.protectedTags.contains global.nextPointerTag = true := by
    unfold ProtectedTags.contains
    rw [held]
    rfl
  have afterBounds : offset.toNat+len.toNat ≤ accessed.tree.locations.size.bytes.toNat := by rw [readCapacity];exact bounds
  obtain ⟨_,_,_,_,framedChild,frameLookup,_,boolAfter⟩ := S05ConcreteProtectedChildDisjoint.construct
    accessed.tree registration.1 completion readRuntime readComplete parentNode.tag global.nextPointerTag parent target parentNode targetNode
    tagged parentAfter targetAfter freshAfter room tagBound heldTag offset len boolOffset (boolOffset+boolLen) nonzero afterBounds disjoint afterBool
  have same : framedChild = child := Option.some.inj (frameLookup.symm.trans lookup)
  subst framedChild
  obtain ⟨_,_,_,_,originChild,originLookup,leaf,_,_⟩ := S05ConcreteProtectedChildCompletion.construct
    accessed.tree registration.1 completion readRuntime readComplete parentNode.tag global.nextPointerTag parent parentNode
    tagged parentAfter freshAfter room tagBound heldTag offset len nonzero afterBounds
  have same : originChild = child := Option.some.inj (originLookup.symm.trans lookup)
  subst originChild
  obtain ⟨current,currentAt,currentTag,_,_⟩ := leaf.old target targetNode targetAfter
  have targetTag := (childComplete.2.2.2.2.1 target current currentAt).1
  rw [currentTag] at targetTag
  have afterOrder := GeneralBorrowParentTagInvariant.nodes_frame tree accessed.tree readNodes order
  have parentBound := GeneralBorrowParentTagInvariant.parent_below_fresh tree global runtime parent parentNode parentPresent
  have freshOrder : parentNode.tag.value ≤ global.nextPointerTag.value :=
    UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp parentBound))
  have childOrder := GeneralBorrowProtectedChildOrder.construct accessed.tree registration.1 readRuntime afterOrder
    parentNode.tag global.nextPointerTag parent parentNode tagged parentAfter freshAfter room freshOrder offset len nonzero afterBounds
  have boolAfterBounds : boolOffset.toNat+boolLen.toNat ≤ canonical.child.tree.locations.size.bytes.toNat := by
    rw [capacity]
    exact boolBounds
  exact ⟨canonical,actual,tag,outputGlobal,frameEq,readDone,childDone,afterRuntime,capacity,growth,boolAfterBounds,childOrder,targetTag,
    child,lookup,roots,childComplete,sourceOwned,boolAfter⟩


/-- Compatibility specialization for a one-byte target. -/
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
    (owned : OwnedOn (Authority tree completion global.protectedTags parent) offset (offset+len) tree.locations)
    (target : UniIndex) (targetNode : TreeNode) (targetPresent : tree.nodes.get target = some targetNode)
    (boolOffset : UInt64) (boolBounds : boolOffset.toNat+1 ≤ tree.locations.size.bytes.toNat)
    (disjoint : ∀ point : UInt64, boolOffset.toNat ≤ point.toNat → point.toNat < (boolOffset+1).toNat →
      point.toNat < offset.toNat ∨ (offset+len).toNat ≤ point.toNat)
    (boolOwned : OwnedOn (Authority tree completion global.protectedTags target)
      boolOffset (boolOffset+1) tree.locations) :
    ∃ output, GeneralBorrowForestFnEntry.operation tree global frame allocation parentNode.tag offset len
        .VisitChildrenOfAccessed = .ok output ∧
      output.tag = global.nextPointerTag ∧
      output.global = (registered global frame allocation tagRoom).1 ∧
      output.frame.protectedTags = frame.protectedTags.push (allocation,output.tag) ∧
      output.access.status = .Completed ∧ output.child.outcome = .ok () ∧
      DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree output.global ∧
      output.child.tree.locations.size = tree.locations.size ∧ output.child.tree.nodes.size ≤ tree.nodes.size+1 ∧
      boolOffset.toNat+1 ≤ output.child.tree.locations.size.bytes.toNat ∧
      ParentTagOrder output.child.tree ∧
      output.child.tree.indexOfTag targetNode.tag = some target ∧
      ∃ child, output.child.tree.indexOfTag output.tag = some child ∧
        output.child.tree.roots = tree.roots ∧
        Completes output.child.tree (S05ConcreteProtectedChildCompletion.extend completion child parent) ∧
        OwnedOn (Authority output.child.tree (S05ConcreteProtectedChildCompletion.extend completion child parent)
          output.global.protectedTags child) offset (offset+len) output.child.tree.locations ∧
        OwnedOn (Authority output.child.tree (S05ConcreteProtectedChildCompletion.extend completion child parent)
          output.global.protectedTags target) boolOffset (boolOffset+1) output.child.tree.locations := by
  exact invoke_window tree global frame allocation completion runtime complete order position selected parent selectedNode parentNode slot selectedPresent parentPresent parentPath tagRoom nodeRoom short offset len nonzero bounds owned target targetNode targetPresent boolOffset 1 boolBounds disjoint boolOwned

end DuplicatePrefix.S05ConcreteFnEntryDisjoint

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05ConcreteFnEntryDisjoint." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved concrete FnEntry disjoint dependency {dependency}"
