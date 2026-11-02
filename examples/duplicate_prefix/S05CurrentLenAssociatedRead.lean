import duplicate_prefix.S05CompletedAncestryObserverRead
import duplicate_prefix.GeneralBorrowFnEntryRegistrationRuntime
namespace DuplicatePrefix.S05CurrentLenAssociatedRead
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowProjection
open GeneralBorrowWildcardParentTagOrder GeneralRangeMapOrigins GeneralRangeMapState
open S05CompletedAncestryReadMutable (Authority)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
noncomputable section

private theorem end_flags (global : GlobalState) (allocation : AllocId) (tag query : BorTag)
    (quiet : global.protectedTags.contains tag = false ∨ query ≠ tag) :
    (global.endCall (({} : FrameState).addProtector allocation tag)).protectedTags.contains query = global.protectedTags.contains query := by
  have table : (global.endCall (({} : FrameState).addProtector allocation tag)).protectedTags = global.protectedTags.remove tag := by
    simp only [GlobalState.endCall,FrameState.addProtector,Array.foldl_push,Array.foldl_empty]
  rw [table]
  by_cases same : query = tag
  · subst query
    have absent : global.protectedTags.contains tag = false := quiet.resolve_right (by simp)
    simp only [ProtectedTags.contains,ProtectedTags.get_remove_same,Option.isSome_none]
    exact absent.symm
  · unfold ProtectedTags.contains
    rw [GeneralBorrowProtectorCacheMap.remove_other global.protectedTags tag query same]

private theorem capability_selected (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree) (root reader : UniIndex)
    (readerPath : GeneralBorrowExposedNonleafPrimaryPath.Path tree root reader)
    (normal : DuplicatePrefixNormalKind.Capability tree location protections reader .Read) :
    ∀ index node, tree.nodes.get index = some node → GeneralBorrowExposedNonleafPrimaryPath.Path tree root index →
      DuplicatePrefixScalarAuthorization.Compatible (CandidateStableCallOwnership.RawState location index node) .Read
        (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) reader.toNat index.toNat)
        (protections.contains node.tag) := by
  obtain ⟨forest⟩ := formed.forest location protections
  have projected := GeneralBorrowPhysicalRootPath.projection_desc tree location protections root reader readerPath
  have rootInside := GeneralBorrowNormalComponentNormalization.contains_ancestor _ reader.toNat normal.component
    root.toNat reader.toNat projected normal.component.anchor
  intro index node present path
  have projected := GeneralBorrowPhysicalRootPath.projection_desc tree location protections root index path
  have supported := GeneralBorrowNormalComponentNormalization.contains_descendant _ forest reader.toNat normal.component
    root.toNat index.toNat projected rootInside
  obtain ⟨state,stored,compatible⟩ := normal.permissions index.toNat supported
    (GeneralBorrowNodeUpdate.lookup_valid tree.nodes index node present)
  have actualState := projection_state tree location protections index.toNat index node (index_self index) rfl present
  have equal : state = CandidateStableCallOwnership.RawState location index node := Option.some.inj (stored.symm.trans actualState)
  subst state
  rw [GeneralBorrowNormalPermissionMetadata.held tree location protections index node present] at compatible
  exact compatible
theorem prepare (tree : BorrowTree) (global : GlobalState) (allocation : AllocId)
    (completion : Completion) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (complete : Completes tree completion) (order : ParentTagOrder tree)
    (position : Nat) (root source reader : UniIndex) (rootNode readerNode : TreeNode)
    (rootSlot : tree.roots[position]? = some root) (rootAt : tree.nodes.get root = some rootNode)
    (sourcePath : Path tree root source) (readerAt : tree.nodeAt reader = some readerNode)
    (readerPath : Path tree root reader) (readerEdge : readerNode.parent = some source)
    (hidden : readerNode.isExposed = false) (readerUnheld : global.protectedTags.contains readerNode.tag = false)
    (room : global.nextPointerTag.value < 18446744073709551615)
    (offset len : UInt64) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (short : tree.nodes.size < 65536)
    (readable : OwnedOn (fun location => Nonempty (DuplicatePrefixNormalKind.Capability tree location global.protectedTags reader .Read))
      offset (offset+len) tree.locations)
    (owned : OwnedOn (Authority tree completion global.protectedTags source) offset (offset+len) tree.locations) :
    let registration := GeneralBorrowFnEntryRegistration.registered global {} allocation room
    let accessed := tree.performBorrowAccessRange (.concrete readerNode.tag) (Size.ofBytes offset) (Size.ofBytes len) .Read
      registration.1.protectedTags .VisitChildrenOfAccessed
    let future := (registration.1.endCall (({} : FrameState).addProtector allocation global.nextPointerTag)).protectedTags
    accessed.status = .Completed ∧ DuplicatePrefixBorrowContract.RuntimeFacts accessed.tree registration.1 ∧
      Completes accessed.tree completion ∧ accessed.tree.nodes = tree.nodes ∧ accessed.tree.roots = tree.roots ∧
      accessed.tree.tagMapping = tree.tagMapping ∧ accessed.tree.locations.size = tree.locations.size ∧
      OwnedOn (fun location => Nonempty (DuplicatePrefixNormalKind.Capability accessed.tree location registration.1.protectedTags reader .Read) ∧
        Authority accessed.tree completion future source location) offset (offset+len) accessed.tree.locations := by
  obtain ⟨_,_,_,current,nodeFresh,_⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare tree global {} allocation room runtime
  let registration := GeneralBorrowFnEntryRegistration.registered global {} allocation room
  have flags : ∀ index node, tree.nodes.get index = some node →
      registration.1.protectedTags.contains node.tag = global.protectedTags.contains node.tag := by
    intro index node present
    exact ProtectorInsertion.contains_other global.protectedTags global.nextPointerTag node.tag .StrongProtector
      (nodeFresh (index,node) (Array.mem_toList_iff.mp ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes index node).mpr present)))
  have unheld : registration.1.protectedTags.contains readerNode.tag = false := (flags reader readerNode readerAt).trans readerUnheld
  obtain ⟨actualRoot,found,parentless⟩ := complete.2.2.2.1 position root rootSlot
  have same := Option.some.inj (found.symm.trans rootAt)
  subst actualRoot
  have rows : OwnedOn (fun location => Nonempty (DuplicatePrefixNormalKind.Capability tree location registration.1.protectedTags reader .Read) ∧
      Authority tree completion (registration.1.endCall (({} : FrameState).addProtector allocation readerNode.tag)).protectedTags source location)
      offset (offset+len) tree.locations := by
    intro cursor valid positive start stop
    obtain ⟨normal⟩ := readable cursor valid positive start stop
    have authority := owned cursor valid positive start stop
    constructor
    · apply GeneralBorrowPhysicalNormalCapability.of_physical_component tree _ registration.1.protectedTags current.formed.toGraphState
        current.formed.fits root reader rootNode rootAt parentless readerPath .Read
      intro index node present path
      rw [flags index node present]
      exact capability_selected tree _ global.protectedTags runtime.formed.toGraphState root reader readerPath normal index node present path
    · intro index node present
      rw [end_flags registration.1 allocation readerNode.tag node.tag (.inl unheld),flags index node present]
      exact authority index node present
  obtain ⟨contract,afterRuntime,afterComplete⟩ := S05CompletedAncestryObserverRead.range_direct tree completion registration.1 current complete order
    position root source reader rootNode readerNode rootSlot rootAt sourcePath readerAt readerPath allocation readerEdge hidden
    (Size.ofBytes offset) (Size.ofBytes len) offset (offset+len) rows bounds (Nat.le_refl _) (Nat.le_refl _) short .VisitChildrenOfAccessed
  refine ⟨contract.completed,afterRuntime,afterComplete,contract.nodes,contract.roots,contract.tags,contract.capacity,?_⟩
  rw [contract.tree_eq]
  intro cursor valid positive start stop
  have result := contract.rows cursor valid positive start stop
  obtain ⟨capability⟩ := result.1
  refine ⟨⟨⟨capability.component,capability.permissions⟩⟩,?_⟩
  intro index node present
  have freshNode : node.tag ≠ global.nextPointerTag :=
    nodeFresh (index,node) (Array.mem_toList_iff.mp ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes index node).mpr present))
  rw [end_flags registration.1 allocation global.nextPointerTag node.tag (.inr freshNode)]
  have authority := result.2 index node present
  rw [end_flags registration.1 allocation readerNode.tag node.tag (.inl unheld)] at authority
  exact authority
end
end DuplicatePrefix.S05CurrentLenAssociatedRead
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05CurrentLenAssociatedRead." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved associated Len Read dependency {dependency}"
