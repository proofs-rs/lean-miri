import duplicate_prefix.CandidateCurrentExposureOrigin
import duplicate_prefix.CandidateCurrentWindowAuthority
import duplicate_prefix.GeneralBorrowRootExposureFrame
import duplicate_prefix.RetagPointerChecks
import duplicate_prefix.S05WildcardProtectedRootCompletion
import duplicate_prefix.TypedRetagSharedNonFreezePolicy

/-! Bounded current exposure/origin justification. A real successful concrete
exposure marks an actual stored node and records address exposure. A subsequent
zero-size wildcard Cell constructor may use an ORIGINAL older exposed node as
its one completed virtual parent, without any access-right premise.
This is not preservation for arbitrary histories, not a claim that State implies
address/tree exposure coherence, and not adoption of CurrentCallAdmission. -/
namespace DuplicatePrefix.CandidateCurrentExposureCompletion
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall GeneralBorrowExposedNonleafPrimaryPath
open S05WildcardProtectedRootCompletion
open GeneralBorrowProjection
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- Actual exposure has both source branches: a newly marked node or the real
already-exposed early return. Neither branch assumes operation success. -/
theorem expose_tree (tree : BorrowTree) (held : ProtectedTags) (tag : BorTag)
    (index : UniIndex) (node : TreeNode) (tagged : tree.indexOfTag tag = some index)
    (present : tree.nodes.get index = some node) (depth : GeneralBorrowExposure.ParentDepth tree.nodes) :
    (tree.exposeTag held tag).outcome = .ok () ∧
    ∃ marked, (tree.exposeTag held tag).tree.nodes.get index = some marked ∧
      marked.tag = node.tag ∧ marked.isExposed = true := by
  cases exposed : node.isExposed with
  | false =>
    obtain ⟨success,_,nodes⟩ := GeneralBorrowRootExposureFrame.expose tree tag index node tagged present depth exposed held
    exact ⟨success, {node with isExposed := true}, by rw [nodes];exact GeneralBorrowFreshLocation.get_same _ _ _,rfl,rfl⟩
  | true =>
    rw [GeneralBorrowRootExposureFrame.already tree tag index node tagged present exposed held]
    exact ⟨rfl,node,present,rfl,exposed⟩

def exposedAddresses (addresses : AllocAddresses.GlobalAddressState) (id : AllocId) :
    AllocAddresses.GlobalAddressState :=
  {addresses with exposed := if addresses.exposed.contains id then addresses.exposed else addresses.exposed.push id}

/-- Source-derived successful machine exposure for a current live allocation.
The ensure hook is the actual global-allocation wiring, whose already-live path
is derived to be unchanged. Default and permissive provenance modes are both
allowed. Strict/nonlive/tracker-disabled/error branches are not promoted to this
tracked successful-exposure conclusion. No empty-protector or fixed tree shape
assumption is used. -/
theorem expose_machine {K U : Type} [DecidableEq K]
    (pointers : PointerMachine.Hooks K U) (state : PointerMachine.State K U)
    (tracker : MachineHooks.BorrowState) (enabled : state.machine.borrowTracker = some tracker)
    (mode : state.machine.user.addresses.provenanceMode ≠ .strict)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (tag : BorTag) (index : UniIndex) (node : TreeNode)
    (tagged : entry.allocation.extra.indexOfTag tag = some index)
    (nodeAt : entry.allocation.extra.nodes.get index = some node)
    (depth : GeneralBorrowExposure.ParentDepth entry.allocation.extra.nodes)
    (globalKind : K) (globals : GlobalAllocationHooks Provenance BorrowTree K
      (PlaceMachine.AccessState K (PointerMachine.User U)))
    (extraWiring : pointers.ensureTreeExtra = GlobalAllocationMachine.ensure globalKind globals)
    (synchronize : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}}) :
    let exposed := entry.allocation.extra.exposeTag tracker.global.protectedTags tag
    let after := {state with machine := {state.machine with
      user := {state.machine.user with addresses := exposedAddresses state.machine.user.addresses id}
      memory := RetagEntry.updatedMemory state.machine.memory id entry exposed.tree}}
    PointerMachine.exposeProvenance pointers (.concrete id tag) state = .ok () after ∧
    after.machine.user.addresses.exposed.contains id = true ∧
    ∃ marked, exposed.tree.nodes.get index = some marked ∧ marked.tag = node.tag ∧ marked.isExposed = true := by
  obtain ⟨treeSuccess,marked,markedAt,sameTag,isExposed⟩ :=
    expose_tree entry.allocation.extra tracker.global.protectedTags tag index node tagged nodeAt depth
  have live : state.machine.memory.isAllocLive id = true := by
    unfold MemoryState.isAllocLive
    rw [MemoryCopyBridge.live_any_of_present _ id entry present]
    rfl
  have info := MemoryCopyBridge.live_alloc_info state.machine.memory id entry present
  let addresses := exposedAddresses state.machine.user.addresses id
  let next : PointerMachine.State K U := {state with machine := {state.machine with user := {state.machine.user with addresses}}}
  have ensure := RetagPointerChecks.ensure_tree_live globalKind globals synchronize next id entry present
  have stored := MemoryCopyBridge.set_live_exact state.machine.memory id entry
    (entry.allocation.setExtra (entry.allocation.extra.exposeTag tracker.global.protectedTags tag).tree) present
  refine ⟨?_,?_,marked,markedAt,sameTag,isExposed⟩
  · unfold PointerMachine.exposeProvenance
    unfold_internal ".PointerMachine.addresses"
    unfold_internal ".PointerMachine.finish"
    unfold_internal ".PointerMachine.setAddresses"
    simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
      modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,beq_iff_eq,mode,↓reduceIte,
      live,Bool.not_true,enabled,Option.isSome_some,info]
    simp only [AllocAddresses.GlobalAddressState.exposeProvenance,beq_iff_eq,mode,↓reduceIte]
    simp only [reduceCtorEq,Bool.false_eq_true,↓reduceIte,Bool.not_false,
      bind,EStateM.bind,pure,EStateM.pure]
    simp only [Id.run,bind,EStateM.bind,pure,EStateM.pure,get,getThe,MonadStateOf.get,EStateM.get,
      enabled,info,Option.isSome_some,bne_self_eq_false,Bool.false_eq_true,↓reduceIte]
    simp only [EStateM.modifyGet,EStateM.bind,EStateM.pure,EStateM.get,enabled,info,Option.isSome_some,bne_self_eq_false,Bool.false_eq_true,↓reduceIte]
    rw [extraWiring]
    simp only [next,addresses,exposedAddresses,enabled] at ensure
    erw [ensure]
    simp only [bind,EStateM.bind,pure,EStateM.pure,modify,modifyGet,MonadStateOf.modifyGet,
      EStateM.modifyGet,enabled,info,present,treeSuccess,stored]
    simp only [RetagEntry.updatedMemory,exposedAddresses,enabled]
  · dsimp only [exposedAddresses]
    split
    · assumption
    · simp

private theorem physical_graph (tree : BorrowTree) (held : ProtectedTags)
    (graph : GeneralBorrowStructuralHistoryState.GraphState tree)
    (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node) :
    tree.tagMapping.get node.tag = some index ∧
    (∀ child, child ∈ node.children.toList ↔
      ∃ childNode, tree.nodes.get child = some childNode ∧ childNode.parent = some index) ∧
    (node.parent = none ↔ index ∈ tree.roots.toList) := by
  obtain ⟨forest⟩ := graph.forest default held
  obtain ⟨depth⟩ := graph.depth
  have reciprocal := GeneralBorrowExposedScopedReciprocal.of_forest tree default held forest depth
  refine ⟨graph.allocator.nodeTags index node present,?_,?_⟩
  · intro child
    constructor
    · intro member
      obtain ⟨childNode,childAt⟩ := graph.children index node present child member
      let topology := (source_normal_projection tree default held).topology
      have size : topology.nodes.size = tree.nodes.data.size := by
        unfold topology
        unfold_general_projection
        unfold_general_topology
        simp only [Array.size_map]
      have indexValid : index.toNat < topology.nodes.size := by
        rw [size]; exact GeneralBorrowNodeUpdate.lookup_valid _ _ _ present
      have childValid : child.toNat < topology.nodes.size := by
        rw [size]; exact GeneralBorrowNodeUpdate.lookup_valid _ _ _ childAt
      have parentProjection := projection_topology_node tree default held index.toNat index node rfl present
      have childProjection := projection_topology_node tree default held child.toNat child childNode rfl childAt
      change (topology.nodes[index.toNat]?.getD ⟨none,[]⟩) = _ at parentProjection
      change (topology.nodes[child.toNat]?.getD ⟨none,[]⟩) = _ at childProjection
      simp only [Array.getElem?_eq_getElem indexValid,Option.getD_some] at parentProjection
      simp only [Array.getElem?_eq_getElem childValid,Option.getD_some] at childProjection
      have projectedMember : child.toNat ∈ (topology.nodes[index.toNat]'indexValid).children := by
        rw [parentProjection]
        exact List.mem_map.mpr ⟨child,member,rfl⟩
      obtain ⟨valid,edge⟩ := forest.childParent index.toNat indexValid child.toNat projectedMember
      rw [childProjection] at edge
      have parentEq : childNode.parent = some index := by
        cases h : childNode.parent with
        | none => simp [h] at edge
        | some actual =>
          simp only [h,Option.map_some] at edge
          have same : actual = index := GeneralBorrowNodeUpdate.index_injective _ _ (Option.some.inj edge)
          exact congrArg some same
      exact ⟨childNode,childAt,parentEq⟩
    · rintro ⟨childNode,childAt,edge⟩
      obtain ⟨parentNode,parentAt,member⟩ := reciprocal child childNode childAt index edge
      have same : parentNode = node := Option.some.inj (parentAt.symm.trans present)
      simpa only [same] using member
  · constructor
    · exact graph.covered index node present
    · intro member
      obtain ⟨rootNode,rootAt,parentless⟩ := graph.rootNodes index member
      have same : node = rootNode := Option.some.inj (present.symm.trans rootAt)
      simpa only [same] using parentless


private theorem path_shape (before after : BorrowTree) (shape : GeneralBorrowView.treeShape after = GeneralBorrowView.treeShape before)
    {first last : UniIndex} (path : Path before first last) : Path after first last := by
  induction path with
  | refl node present =>
    obtain ⟨next,found,_,_,_,_⟩ := GeneralBorrowFreshMetadata.node_fields before after shape _ node present
    exact .refl _ next found
  | step path node present edge ih =>
    obtain ⟨next,found,_,parentEq,_,_⟩ := GeneralBorrowFreshMetadata.node_fields before after shape _ node present
    exact .step ih next found (parentEq.trans edge)

/-- Finite completion survives an exposure-only shape update: old exposed
origins remain exposed. No permission table or exposure chronology is used. -/
private theorem completes_shape (before after : BorrowTree) (held : ProtectedTags) (completion : Completion)
    (shape : GeneralBorrowView.treeShape after = GeneralBorrowView.treeShape before)
    (graph : GeneralBorrowStructuralHistoryState.GraphState after)
    (retains : ∀ index old next, before.nodes.get index = some old → after.nodes.get index = some next →
      old.isExposed = true → next.isExposed = true)
    (complete : Completes before completion) : Completes after completion := by
  have size := GeneralBorrowFreshMetadata.node_size before after shape
  have roots := GeneralBorrowFreshMetadata.roots before after shape
  refine ⟨?_,?_,by rw [roots];exact complete.2.2.1,?_,?_,?_,?_⟩
  · change completion.parents.size = after.nodes.size
    rw [size];exact complete.1
  · change completion.depths.size = after.nodes.size
    rw [size];exact complete.2.1
  · intro position root slot
    rw [roots] at slot
    obtain ⟨old,oldAt,parentless⟩ := complete.2.2.2.1 position root slot
    obtain ⟨next,nextAt,_,parentEq,_,_⟩ := GeneralBorrowFreshMetadata.node_fields before after shape root old oldAt
    exact ⟨next,nextAt,parentEq.trans parentless⟩
  · intro index node present
    obtain ⟨mapped,children,root⟩ := physical_graph after held graph index node present
    refine ⟨mapped,children,?_,root⟩
    intro parent edge
    obtain ⟨old,oldAt,_,parentEq,_,_⟩ := GeneralBorrowFreshMetadata.node_fields after before shape.symm index node present
    exact (complete.2.2.2.2.1 index old oldAt).2.2.1 parent (parentEq.trans edge)
  · intro position root slot
    rw [roots] at slot
    have old := complete.2.2.2.2.2.1 position root slot
    by_cases zero : position = 0
    · simpa only [zero,ite_true] using old
    · simp only [zero,ite_false] at old ⊢
      obtain ⟨earlier,originRoot,origin,rootNode,originNode,earlierBound,originSlot,rootAt,originAt,exposed,older,path,edge⟩ := old
      obtain ⟨nextRoot,nextRootAt,rootTag,_,_,_⟩ := GeneralBorrowFreshMetadata.node_fields before after shape root rootNode rootAt
      obtain ⟨nextOrigin,nextOriginAt,originTag,_,_,_⟩ := GeneralBorrowFreshMetadata.node_fields before after shape origin originNode originAt
      exact ⟨earlier,originRoot,origin,nextRoot,nextOrigin,earlierBound,by rw [roots];exact originSlot,
        nextRootAt,nextOriginAt,retains origin originNode nextOrigin originAt nextOriginAt exposed,
        by simpa only [rootTag,originTag] using older,path_shape before after shape path,edge⟩
  · intro child parent edge
    obtain ⟨⟨childNode,childAt⟩,⟨parentNode,parentAt⟩,smaller⟩ := complete.2.2.2.2.2.2 child parent edge
    obtain ⟨nextChild,nextChildAt,_,_,_,_⟩ := GeneralBorrowFreshMetadata.node_fields before after shape child childNode childAt
    obtain ⟨nextParent,nextParentAt,_,_,_,_⟩ := GeneralBorrowFreshMetadata.node_fields before after shape parent parentNode parentAt
    exact ⟨⟨nextChild,nextChildAt⟩,⟨nextParent,nextParentAt⟩,smaller⟩

/-- The actual successful exposeTag retains the same completed ancestry and
intrinsic state while making the selected ORIGINAL node exposed. -/
theorem expose_completed (tree : BorrowTree) (held : ProtectedTags) (tag : BorTag)
    (index : UniIndex) (node : TreeNode) (tagged : tree.indexOfTag tag = some index)
    (present : tree.nodes.get index = some node) (state : GeneralBorrowStructuralHistoryState.State tree)
    (completion : Completion) (complete : Completes tree completion) :
    let after := (tree.exposeTag held tag).tree
    GeneralBorrowView.treeShape after = GeneralBorrowView.treeShape tree ∧
    GeneralBorrowStructuralHistoryState.State after ∧ Completes after completion := by
  obtain ⟨depth⟩ := state.depth
  cases exposed : node.isExposed with
  | true =>
    rw [GeneralBorrowRootExposureFrame.already tree tag index node tagged present exposed held]
    exact ⟨rfl,state,complete⟩
  | false =>
    obtain ⟨_,shape,nodes⟩ := GeneralBorrowRootExposureFrame.expose tree tag index node tagged present depth exposed held
    have afterState := GeneralBorrowStructuralHistoryState.shape tree _ shape state
    refine ⟨shape,afterState,completes_shape tree _ held completion shape afterState.toGraphState ?_ complete⟩
    intro query old next oldAt nextAt oldExposed
    by_cases same : query = index
    · subst query
      have oldEq : old = node := Option.some.inj (oldAt.symm.trans present)
      subst old
      rw [exposed] at oldExposed
      cases oldExposed
    · rw [nodes,GeneralBorrowFreshLocation.get_other _ _ _ _ same,oldAt] at nextAt
      have nextEq : next = old := Option.some.inj nextAt.symm
      simpa only [nextEq] using oldExposed

private theorem inserted_size (nodes : UniValMap TreeNode) (child : UniIndex) (node : TreeNode) :
    (nodes.insert child node).data.size = max nodes.data.size (child.toNat+1) := by
  simp only [UniValMap.insert,Id.run,pure]
  split <;> simp only [Array.size_set,UniValMap.extendTo,Array.size_append,Array.size_replicate] <;> omega

/-- A zero-size non-Freeze shared root has no associated access. The available
ORIGINAL exposed origin becomes the SAME logical parent of its physical root.
Freshness and original tag order follow from the supplied current runtime;
no Read/Write authority, exposed-root count, noFree or append-only assumption is
supplied. The real allocator may append or reuse a vacant slot. -/
private theorem zero_cell_structural (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (state : GeneralBorrowStructuralHistoryState.State tree)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping global.nextPointerTag)
    (complete : Completes tree completion) (room : tree.nodes.size+1 ≤ 4294967295)
    (origin : UniIndex) (originNode : TreeNode) (originAt : tree.nodes.get origin = some originNode)
    (exposed : originNode.isExposed = true) (older : originNode.tag.value < global.nextPointerTag.value)
    (offset : UInt64) :
    let actual := tree.newChild (Size.ofBytes offset) .wildcard global.nextPointerTag
      (DedupRangeMap.new Size.ZERO TypedRetagSharedNonFreezePolicy.location) .Cell false
    actual.outcome = .ok () ∧ actual.tree.locations = tree.locations ∧
    ∃ child, actual.tree.indexOfTag global.nextPointerTag = some child ∧
      actual.tree.roots = tree.roots.push child ∧
      RootFrame tree actual.tree child origin global.nextPointerTag ∧
      Completes actual.tree (S05ConcreteProtectedChildCompletion.extend completion child origin) := by
  obtain ⟨mapping,child,inserted,graph,_⟩ :=
    GeneralBorrowStructuralHistoryWildcardAllocator.select tree state.toGraphState global.nextPointerTag fresh room .Cell .Write
  have vacant := GeneralBorrowStructuralHistorySifaState.vacant_of_insert tree state global.nextPointerTag fresh room mapping child inserted
  have actual := WildcardHitZeroConstructor.exact tree global.nextPointerTag child mapping inserted
    .Cell .Write false rfl rfl rfl TypedRetagSharedNonFreezePolicy.location offset
  rw [actual]
  let model := WildcardHitZeroConstructor.installed tree mapping child global.nextPointerTag .Cell .Write
  have childAt : model.nodes.get child = some (WildcardHitZeroConstructor.rootNode global.nextPointerTag .Cell .Write) :=
    GeneralBorrowFreshLocation.get_same _ _ _
  have frame : RootFrame tree model child origin global.nextPointerTag := by
    refine ⟨vacant,inserted_size tree.nodes child _,rfl,⟨originNode,originAt⟩,⟨_,childAt,rfl,rfl⟩,?_,?_,
      physical_graph model global.protectedTags graph⟩
    · intro index node present
      have different : index ≠ child := by intro same;rw [same,vacant] at present;cases present
      exact ⟨node,(GeneralBorrowFreshLocation.get_other _ _ _ _ different).trans present,rfl,rfl,rfl⟩
    · intro index node present
      by_cases same : index = child
      · exact Or.inl same
      · exact Or.inr ⟨node,(GeneralBorrowFreshLocation.get_other _ _ _ _ same).symm.trans present,rfl⟩
  obtain ⟨position,root,rootNode,slot,rootAt,path⟩ :=
    CandidateCurrentWindowAuthority.root_path tree state.toGraphState origin originNode originAt
  exact ⟨rfl,rfl,child,graph.allocator.nodeTags child _ childAt,rfl,frame,
    completes_of_root tree model completion complete child origin global.nextPointerTag frame originNode originAt exposed older
      position root slot path⟩

theorem zero_cell_from_origin (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (complete : Completes tree completion) (room : tree.nodes.size+1 ≤ 4294967295)
    (origin : UniIndex) (originNode : TreeNode) (originAt : tree.nodes.get origin = some originNode)
    (exposed : originNode.isExposed = true) (offset : UInt64) :
    let actual := tree.newChild (Size.ofBytes offset) .wildcard global.nextPointerTag
      (DedupRangeMap.new Size.ZERO TypedRetagSharedNonFreezePolicy.location) .Cell false
    actual.outcome = .ok () ∧ actual.tree.locations = tree.locations ∧
    ∃ child, actual.tree.indexOfTag global.nextPointerTag = some child ∧
      actual.tree.roots = tree.roots.push child ∧
      RootFrame tree actual.tree child origin global.nextPointerTag ∧
      Completes actual.tree (S05ConcreteProtectedChildCompletion.extend completion child origin) := by
  have high := GeneralBorrowForestTagHighWater.complete tree _ _ runtime.below runtime.formed.allocator.nodeTags
  obtain ⟨fresh,_,_⟩ := GenericFunctionTagFormation.fresh_above tree _ _ global.nextPointerTag high (Nat.le_refl _)
  exact zero_cell_structural tree global completion runtime.formed.toState fresh complete room origin originNode originAt exposed
    (GeneralBorrowParentTagInvariant.parent_below_fresh tree global runtime origin originNode originAt) offset

/-- Actual zero-byte wildcard resolution selects an exposed allocation. Current
coherence (not State alone) supplies its exposed node, whose age is established
with ORIGINAL allocator/high-water data before allocating the zero-Cell tag.
The resulting physical root's virtual edge uses exactly that returned node.
This conditional finite bridge is not an ordinary-admission claim. -/
theorem resolved_zero_cell (options : Miri.Input.EvalConfigurationCore.Options)
    (limits : ExecutionMachine.Limits) (remaining : Nat) (before : Before)
    (tracker : MachineHooks.BorrowState) (len : UInt64)
    (state : DuplicatePrefixRuntimeInput.State before tracker)
    (resources : DuplicatePrefixCallSpecification.Resources options limits remaining before tracker len)
    (coherent : CandidateCurrentExposureOrigin.ExposureCoherent before)
    (id : AllocId) (allocation : Allocation Provenance BorrowTree)
    (present : Present (ActualWorld before) id allocation) (completion : Completion)
    (complete : Completes allocation.extra completion) (address offset : UInt64)
    (hooks : AllocAddresses.AddressLookupHooks)
    (resolved : before.user.addresses.allocIdFromAddr address 0 hooks = .ok (some id)) :
    ∃ origin originNode, allocation.extra.nodes.get origin = some originNode ∧ originNode.isExposed = true ∧
      originNode.tag.value.toNat < tracker.global.nextPointerTag.value.toNat ∧
      let actual := allocation.extra.newChild (Size.ofBytes offset) .wildcard tracker.global.nextPointerTag
        (DedupRangeMap.new Size.ZERO TypedRetagSharedNonFreezePolicy.location) .Cell false
      actual.outcome = .ok () ∧ actual.tree.locations = allocation.extra.locations ∧
      ∃ child, actual.tree.indexOfTag tracker.global.nextPointerTag = some child ∧
        actual.tree.roots = allocation.extra.roots.push child ∧
        RootFrame allocation.extra actual.tree child origin tracker.global.nextPointerTag ∧
        Completes actual.tree (S05ConcreteProtectedChildCompletion.extend completion child origin) := by
  obtain ⟨origin,node,nodeAt,exposed,older⟩ := CandidateCurrentExposureOrigin.older_origin
    options limits remaining before tracker len state resources coherent id allocation present address hooks resolved
  refine ⟨origin,node,nodeAt,exposed,older,?_⟩
  simp only [Present,ActualWorld,Array.toList_map] at present
  obtain ⟨⟨oldId,entry⟩,member,equal⟩ := List.mem_map.mp present
  rcases Prod.mk.inj equal with ⟨rfl,rfl⟩
  have runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global :=
    ⟨state.formed _ member,state.coherent _ member,state.possible _ member,resources.tagsBelow _ member⟩
  exact zero_cell_from_origin entry.allocation.extra tracker.global completion runtime complete
    (by have bound := resources.nodeRoom _ member;change entry.allocation.extra.nodes.size+16 < 65536 at bound;omega) origin node nodeAt exposed offset

/-- One actual exposure followed by one actual zero-Cell graph construction.
The SAME newly/already exposed original node supplies the virtual parent. All
shape/completion transport and original tag age are derived; there is no
coherence assumption and no access-right premise in this finite sequence. -/
theorem expose_then_zero_cell (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (complete : Completes tree completion)
    (tag : BorTag) (index : UniIndex) (node : TreeNode) (tagged : tree.indexOfTag tag = some index)
    (present : tree.nodes.get index = some node) (room : tree.nodes.size+1 ≤ 4294967295) (offset : UInt64) :
    let exposure := tree.exposeTag global.protectedTags tag
    exposure.outcome = .ok () ∧ ∃ marked,
      exposure.tree.nodes.get index = some marked ∧ marked.tag = node.tag ∧ marked.isExposed = true ∧
      marked.tag.value < global.nextPointerTag.value ∧
      let actual := exposure.tree.newChild (Size.ofBytes offset) .wildcard global.nextPointerTag
        (DedupRangeMap.new Size.ZERO TypedRetagSharedNonFreezePolicy.location) .Cell false
      actual.outcome = .ok () ∧ actual.tree.locations = exposure.tree.locations ∧
      ∃ child, actual.tree.indexOfTag global.nextPointerTag = some child ∧
        actual.tree.roots = exposure.tree.roots.push child ∧
        RootFrame exposure.tree actual.tree child index global.nextPointerTag ∧
        Completes actual.tree (S05ConcreteProtectedChildCompletion.extend completion child index) := by
  obtain ⟨depth⟩ := runtime.formed.depth
  obtain ⟨success,marked,markedAt,markedTag,markedExposed⟩ :=
    expose_tree tree global.protectedTags tag index node tagged present depth
  obtain ⟨shape,afterState,afterComplete⟩ := expose_completed tree global.protectedTags tag index node tagged present
    runtime.formed.toState completion complete
  have high := GeneralBorrowForestTagHighWater.complete tree _ _ runtime.below runtime.formed.allocator.nodeTags
  have fresh := (GenericFunctionTagFormation.fresh_above tree _ _ global.nextPointerTag high (Nat.le_refl _)).1
  have freshAfter : GeneralBorrowTagMap.Fresh (tree.exposeTag global.protectedTags tag).tree.tagMapping global.nextPointerTag := by
    rw [GeneralBorrowFreshMetadata.mapping tree _ shape]
    exact fresh
  have roomAfter : (tree.exposeTag global.protectedTags tag).tree.nodes.size+1 ≤ 4294967295 := by
    rw [GeneralBorrowFreshMetadata.node_size tree _ shape]
    exact room
  have older : marked.tag.value < global.nextPointerTag.value := by
    rw [markedTag]
    exact GeneralBorrowParentTagInvariant.parent_below_fresh tree global runtime index node present
  exact ⟨success,marked,markedAt,markedTag,markedExposed,older,
    zero_cell_structural _ global completion afterState freshAfter afterComplete roomAfter index marked markedAt markedExposed older offset⟩

/-- The finite source-derived machine exposure and graph constructor use the
same installed tree and original node. This is a bounded graph-stage witness;
metadata/type selection, wildcard address resolution and machine installation
of the subsequent retag remain separate from this theorem. No callee type or
query answer is invented here. -/
theorem machine_expose_then_zero_cell {K U : Type} [DecidableEq K]
    (pointers : PointerMachine.Hooks K U) (state : PointerMachine.State K U)
    (tracker : MachineHooks.BorrowState) (enabled : state.machine.borrowTracker = some tracker)
    (mode : state.machine.user.addresses.provenanceMode ≠ .strict)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global)
    (completion : Completion) (complete : Completes entry.allocation.extra completion)
    (tag : BorTag) (index : UniIndex) (node : TreeNode)
    (tagged : entry.allocation.extra.indexOfTag tag = some index)
    (nodeAt : entry.allocation.extra.nodes.get index = some node)
    (room : entry.allocation.extra.nodes.size+1 ≤ 4294967295) (offset : UInt64)
    (globalKind : K) (globals : GlobalAllocationHooks Provenance BorrowTree K
      (PlaceMachine.AccessState K (PointerMachine.User U)))
    (extraWiring : pointers.ensureTreeExtra = GlobalAllocationMachine.ensure globalKind globals)
    (synchronize : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}}) :
    let exposure := entry.allocation.extra.exposeTag tracker.global.protectedTags tag
    let after := {state with machine := {state.machine with
      user := {state.machine.user with addresses := exposedAddresses state.machine.user.addresses id}
      memory := RetagEntry.updatedMemory state.machine.memory id entry exposure.tree}}
    PointerMachine.exposeProvenance pointers (.concrete id tag) state = .ok () after ∧
    after.machine.user.addresses.exposed.contains id = true ∧
    exposure.outcome = .ok () ∧ ∃ marked,
      exposure.tree.nodes.get index = some marked ∧ marked.tag = node.tag ∧ marked.isExposed = true ∧
      marked.tag.value < tracker.global.nextPointerTag.value ∧
      let actual := exposure.tree.newChild (Size.ofBytes offset) .wildcard tracker.global.nextPointerTag
        (DedupRangeMap.new Size.ZERO TypedRetagSharedNonFreezePolicy.location) .Cell false
      actual.outcome = .ok () ∧ actual.tree.locations = exposure.tree.locations ∧
      ∃ child, actual.tree.indexOfTag tracker.global.nextPointerTag = some child ∧
        actual.tree.roots = exposure.tree.roots.push child ∧
        RootFrame exposure.tree actual.tree child index tracker.global.nextPointerTag ∧
        Completes actual.tree (S05ConcreteProtectedChildCompletion.extend completion child index) := by
  obtain ⟨depth⟩ := runtime.formed.depth
  obtain ⟨actual,exposed,_⟩ := expose_machine pointers state tracker enabled mode id entry present tag index node tagged nodeAt
    depth globalKind globals extraWiring synchronize
  exact ⟨actual,exposed,expose_then_zero_cell entry.allocation.extra tracker.global completion runtime complete
    tag index node tagged nodeAt room offset⟩

end DuplicatePrefix.CandidateCurrentExposureCompletion

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CandidateCurrentExposureCompletion." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved bounded current exposure completion dependency {dependency}"
