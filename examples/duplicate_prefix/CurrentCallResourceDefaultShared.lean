import duplicate_prefix.CurrentCallResourceFnEntry
import duplicate_prefix.GeneralBorrowSharedCapabilityConstructor
import duplicate_prefix.GeneralBorrowSharedReadConstructor
import duplicate_prefix.GeneralBorrowSharedChildGraph
import duplicate_prefix.S05SharedChildActivity
import duplicate_prefix.CurrentCallSharedReference
import duplicate_prefix.CurrentCallSharedConstructorFrame

namespace DuplicatePrefix.CurrentCallResourceDefaultShared
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.MIR
open CanonicalConfigFacts ActualReferenceContext RootReferenceInfo RootReferenceTrees
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources OrdinaryBorrowAuthority
open CurrentCallResourceNormalization GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowFnEntryRegistration
open GeneralBorrowProjection GeneralBorrowForest GeneralRangeMapOrigins GeneralBorrowRawSharedExpression
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

private theorem normal_of_authority (tree : BorrowTree) (completion : Completion) (initial : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (fits : tree.nodes.data.size ≤ 4294967296)
    (position : Nat) (root source : UniIndex) (rootNode : TreeNode)
    (rootSlot : tree.roots[position]? = some root) (rootPresent : tree.nodes.get root = some rootNode)
    (sourcePath : Path tree root source)
    (classification : ∀ index node, tree.nodes.get index = some node → Path tree root index →
      (Below completion index source ↔ Path tree index source))
    (localRights : ∀ index node, tree.nodes.get index = some node → Path tree root index →
      Below completion index source → LocalWrite
        ((initial.perms.get index).getD node.defaultLocationState) (protections.contains node.tag))
    (foreignRights : ∀ index node, tree.nodes.get index = some node → Path tree root index →
      ¬Below completion index source → ForeignWrite
        ((initial.perms.get index).getD node.defaultLocationState) (protections.contains node.tag)) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree initial protections source) := by
  obtain ⟨actual,found,parentless⟩ := formed.rootNodes root (Array.mem_toList_iff.mpr (Array.mem_of_getElem? rootSlot))
  have same : actual = rootNode := Option.some.inj (found.symm.trans rootPresent)
  subst actual
  obtain ⟨forest⟩ := formed.forest initial protections
  let topology := (source_normal_projection tree initial protections).topology
  have projectedPath := GeneralBorrowPhysicalRootPath.projection_desc tree initial protections root source sourcePath
  have rootValid : root.toNat < topology.nodes.size := projectedPath.valid.1
  have projectedRoot := projection_topology_node tree initial protections root.toNat root rootNode rfl rootPresent
  change (topology.nodes[root.toNat]?.getD ⟨none,[]⟩) = _ at projectedRoot
  have rootShape : topology.nodes[root.toNat] =
      ⟨rootNode.parent.map UniIndex.toNat,rootNode.children.toList.map UniIndex.toNat⟩ := by
    simpa only [Array.getElem?_eq_getElem rootValid,Option.getD_some] using projectedRoot
  have rootParentless : (topology.nodes[root.toNat]'rootValid).parent = none := by
    rw [rootShape];simp only [parentless,Option.map_none]
  let chosen := GeneralBorrowExposedScopedNormalRoot.component topology forest root.toNat source.toNat
    rootValid rootParentless projectedPath
  refine ⟨⟨chosen,?_⟩⟩
  intro kind slot inside _
  change Desc topology root.toNat slot at inside
  obtain ⟨index,node,indexEq,present,path⟩ := GeneralBorrowProjectedDescPath.desc_path tree initial protections fits
    root rootNode rootPresent slot inside
  obtain ⟨sourceNode,sourcePresent⟩ := sourcePath.present
  let state := (initial.perms.get index).getD node.defaultLocationState
  refine ⟨state,?_,?_⟩
  · rw [←indexEq]
    exact projection_state tree initial protections index.toNat index node (index_self index) rfl present
  · rw [←indexEq,GeneralBorrowNormalPermissionMetadata.held tree initial protections index node present]
    have physical := classification index node present path
    have related := GeneralBorrowProjectedDescPath.relation_local_iff tree initial protections fits depth forest
      source index sourceNode node sourcePresent present
    by_cases localPath : Path tree index source
    · rw [related.mpr localPath]
      exact OrdinaryBorrowAuthorityBridge.local_scalar state _ (localRights index node present path (physical.mpr localPath)) kind
    · have foreignRelation : GeneralBorrowAnchor.relation (source_normal_projection tree initial protections)
          source.toNat index.toNat = .ForeignAccess := by
        cases relation : GeneralBorrowAnchor.relation (source_normal_projection tree initial protections) source.toNat index.toNat with
        | LocalAccess => exact False.elim (localPath (related.mp relation))
        | ForeignAccess => rfl
      rw [foreignRelation]
      have raw := foreignRights index node present path (fun below => localPath (physical.mp below))
      obtain ⟨next,delta,success,_⟩ := S05RawAuthorityStepPreservation.foreign_step state _ kind raw
      exact (DuplicatePrefixScalarAuthorization.compatible_iff state kind .ForeignAccess _ raw.1).mpr ⟨next,delta,success⟩


/-- Selected current q resources consumed by the actual Default shared Read.
No changed-allocation pre-state witness is fabricated. -/
structure Preparation {before tracker data owner id offset length}
    (W : UniformWindow before tracker data owner id offset length .mut)
    (tag : BorTag) (start amount : UInt64)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615) where
  geometry : Geometry W
  completed : (read W.allocation.extra tracker.global.protectedTags tag start amount .VisitChildrenOfAccessed).status = .Completed
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts
    (read W.allocation.extra tracker.global.protectedTags tag start amount .VisitChildrenOfAccessed).tree (advanced tracker.global room)
  parents : ParentInterpretation (read W.allocation.extra tracker.global.protectedTags tag start amount .VisitChildrenOfAccessed).tree W.precise.completion
  owned : OwnedOn (S05CompletedAncestryReadMutable.Authority
    (read W.allocation.extra tracker.global.protectedTags tag start amount .VisitChildrenOfAccessed).tree
    W.precise.completion tracker.global.protectedTags W.pointer.grant) start (start+amount)
    (read W.allocation.extra tracker.global.protectedTags tag start amount .VisitChildrenOfAccessed).tree.locations
  normals : OwnedOn (fun location => Nonempty (DuplicatePrefixBorrowAuthorization.Normal
    (read W.allocation.extra tracker.global.protectedTags tag start amount .VisitChildrenOfAccessed).tree
    location tracker.global.protectedTags W.pointer.grant)) start (start+amount)
    (read W.allocation.extra tracker.global.protectedTags tag start amount .VisitChildrenOfAccessed).tree.locations
  nodes : (read W.allocation.extra tracker.global.protectedTags tag start amount .VisitChildrenOfAccessed).tree.nodes = W.allocation.extra.nodes
  roots : (read W.allocation.extra tracker.global.protectedTags tag start amount .VisitChildrenOfAccessed).tree.roots = W.allocation.extra.roots
  tags : (read W.allocation.extra tracker.global.protectedTags tag start amount .VisitChildrenOfAccessed).tree.tagMapping = W.allocation.extra.tagMapping
  capacity : (read W.allocation.extra tracker.global.protectedTags tag start amount .VisitChildrenOfAccessed).tree.locations.size = W.allocation.extra.locations.size

theorem prepare {before tracker data owner id offset length}
    (W : UniformWindow before tracker data owner id offset length .mut)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (tag : BorTag) (concrete : W.pointer.value.provenance = .concrete id tag)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615)
    (distinct : W.allocation.extra.roots.toList.Nodup) (short : W.allocation.extra.nodes.size < 65536)
    (start amount : UInt64) (startEq : start.toNat = offset) (amountEq : amount.toNat = length)
    (bounds : start.toNat+amount.toNat ≤ W.allocation.extra.locations.size.bytes.toNat) :
    Nonempty (Preparation W tag start amount room) := by
  obtain ⟨G⟩ := geometry_selected W (CandidateCurrentGrantRuntime.tree_rows W.allocation.extra tracker.global runtime) (by rfl)
  have noWrap : start.toNat+amount.toNat < 2^64 := Nat.lt_of_le_of_lt bounds (UInt64.toNat_lt W.allocation.extra.locations.size.bytes)
  have upper : (start+amount).toNat = start.toNat+amount.toNat := by simp only [UInt64.toNat_add,Nat.mod_eq_of_lt noWrap]
  obtain ⟨done,afterRuntime,parents,owned,nodes,roots,tags,capacity⟩ := CurrentCallResourceRead.read_range_runtime W G (by rfl)
    distinct short runtime (Size.ofBytes start) (Size.ofBytes amount) start (start+amount)
    (by omega) (by omega) bounds (Nat.le_refl _) (Nat.le_refl _) .VisitChildrenOfAccessed
  simp only [concrete] at done afterRuntime parents owned nodes roots tags capacity
  let after := read W.allocation.extra tracker.global.protectedTags tag start amount .VisitChildrenOfAccessed
  change DuplicatePrefixBorrowContract.RuntimeFacts after.tree tracker.global at afterRuntime
  change after.tree.nodes = W.allocation.extra.nodes at nodes
  change after.tree.roots = W.allocation.extra.roots at roots
  change after.tree.tagMapping = W.allocation.extra.tagMapping at tags
  change OwnedOn (S05CompletedAncestryReadMutable.Authority after.tree W.precise.completion tracker.global.protectedTags W.pointer.grant)
    start (start+amount) after.tree.locations at owned
  have high := GeneralBorrowForestTagHighWater.complete W.allocation.extra _ _ runtime.below runtime.formed.allocator.nodeTags
  obtain ⟨fresh,_,unheld⟩ := GenericFunctionTagFormation.fresh_above W.allocation.extra _ _ tracker.global.nextPointerTag high (Nat.le_refl _)
  obtain ⟨allocated,actual,below⟩ := GeneralBorrowForestTagHighWaterHistory.allocate W.allocation.extra tracker.global room runtime.below runtime.formed.allocator.nodeTags false
  have equal : advanced tracker.global room = allocated := congrArg Prod.fst
    (Except.ok.inj ((TypedRetagEmpty.allocate_tag tracker.global room).symm.trans actual))
  rw [←equal] at below
  have nextBelow : GeneralBorrowForestTagHighWater.Below W.allocation.extra (advanced tracker.global room).protectedTags (advanced tracker.global room).nextPointerTag := by
    simpa only [GeneralBorrowFreshSharedSequence.registered,Bool.false_eq_true,ite_false] using below
  have nextRuntime : DuplicatePrefixBorrowContract.RuntimeFacts after.tree (advanced tracker.global room) :=
    ⟨afterRuntime.formed,afterRuntime.coherent,afterRuntime.possible,⟨by rw [tags];exact nextBelow.mapping,nextBelow.protectors⟩⟩
  refine ⟨⟨G,done,nextRuntime,parents,owned,?_,nodes,roots,tags,capacity⟩⟩
  intro position valid positive lower upper
  have authority := owned position valid positive lower upper
  have oldAuthority : S05CompletedAncestryReadMutable.Authority W.allocation.extra W.precise.completion tracker.global.protectedTags W.pointer.grant after.tree.locations.entries[position].data := by
    intro index node present
    exact authority index node (by rw [nodes];exact present)
  obtain ⟨depth⟩ := W.parents.graph.depth
  have normal := normal_of_authority W.allocation.extra W.precise.completion after.tree.locations.entries[position].data tracker.global.protectedTags
    W.parents.graph depth W.parents.graph.fits G.selectedPosition G.selectedRoot W.pointer.grant G.selectedNode G.selectedSlot G.selectedAt G.sourcePath G.normalAncestry
    (fun index node present _ below => (oldAuthority index node present).1 below)
    (fun index node present _ outside => (oldAuthority index node present).2 outside)
  have frame := GeneralBorrowFreshReadFrame.frame W.allocation.extra (.concrete tag) (Size.ofBytes start) (Size.ofBytes amount) .Read tracker.global.protectedTags .VisitChildrenOfAccessed
  change after.tree = {W.allocation.extra with locations := after.tree.locations} at frame
  have transport : ∀ location, Nonempty (DuplicatePrefixBorrowAuthorization.Normal W.allocation.extra location tracker.global.protectedTags W.pointer.grant) →
      Nonempty (DuplicatePrefixBorrowAuthorization.Normal after.tree location tracker.global.protectedTags W.pointer.grant) := by
    intro location normal
    rw [frame]
    obtain ⟨normal⟩ := normal
    exact ⟨⟨normal.component,normal.permissions⟩⟩
  exact transport _ normal

/-- SAME actual Read and unprotected Frozen constructor produce current q/r
Read capabilities and r activity, with the actual materialized runtime. -/
theorem construct {before tracker data owner id offset length}
    (W : UniformWindow before tracker data owner id offset length .mut)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (tag : BorTag) (concrete : W.pointer.value.provenance = .concrete id tag)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615)
    (distinct : W.allocation.extra.roots.toList.Nodup) (short : W.allocation.extra.nodes.size < 65536)
    (nodeRoom : W.allocation.extra.nodes.size+1 ≤ 4294967295)
    (start amount : UInt64) (startEq : start.toNat = offset) (amountEq : amount.toNat = length)
    (nonzero : amount ≠ 0) (bounds : start.toNat+amount.toNat ≤ W.allocation.extra.locations.size.bytes.toNat) :
    ∃ _P : Preparation W tag start amount room,
      let actual := child W.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed
      actual.outcome = .ok () ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree (advanced tracker.global room) ∧
      actual.tree.locations.size = W.allocation.extra.locations.size ∧ actual.tree.nodes.size ≤ W.allocation.extra.nodes.size+1 ∧
      ∃ reader, actual.tree.indexOfTag tracker.global.nextPointerTag = some reader ∧
        OwnedOn (GeneralBorrowSharedReadConstructor.Capabilities actual.tree tracker.global.protectedTags W.pointer.grant reader)
          start (start+amount) actual.tree.locations ∧
        GeneralBorrowFreshActiveWithin.ActiveWithin actual.tree reader .Read start (start+amount) := by
  obtain ⟨P⟩ := prepare W runtime tag concrete room distinct short start amount startEq amountEq bounds
  let after := read W.allocation.extra tracker.global.protectedTags tag start amount .VisitChildrenOfAccessed
  have high := GeneralBorrowForestTagHighWater.complete W.allocation.extra _ _ runtime.below runtime.formed.allocator.nodeTags
  obtain ⟨fresh,_,unheld⟩ := GenericFunctionTagFormation.fresh_above W.allocation.extra _ _ tracker.global.nextPointerTag high (Nat.le_refl _)
  have freshAfter : GeneralBorrowTagMap.Fresh after.tree.tagMapping tracker.global.nextPointerTag := by rw [P.tags];exact fresh
  obtain ⟨parent,parentAt,_,binding⟩ := W.binding
  rw [concrete] at binding
  have parentAfter : after.tree.nodeAt W.pointer.grant = some parent := by change after.tree.nodes.get _ = _;rw [P.nodes];exact parentAt
  have tagged : after.tree.indexOfTag tag = some W.pointer.grant := by rw [binding.2];exact P.runtime.formed.allocator.nodeTags _ _ parentAfter
  have capacity : start.toNat+amount.toNat ≤ after.tree.locations.size.bytes.toNat := by rw [P.capacity];exact bounds
  have nodesRoom : after.tree.nodes.size+1 ≤ 4294967295 := by change after.tree.nodes.data.size+1 ≤ _;rw [P.nodes];exact nodeRoom
  have tagBound : tracker.global.nextPointerTag.value.toNat < (advanced tracker.global room).nextPointerTag.value.toNat := by
    have successor := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag room
    change tracker.global.nextPointerTag.value.toNat < (TypedRetagEmpty.successorTag tracker.global.nextPointerTag room).value.toNat
    omega
  have caps := GeneralBorrowSharedCapabilityConstructor.construct after.tree (advanced tracker.global room) P.runtime tag tracker.global.nextPointerTag W.pointer.grant parent
    tagged parentAfter freshAfter nodesRoom tagBound unheld start amount nonzero capacity P.normals
  obtain ⟨reader,lookup,both⟩ := caps.2.2.2.2
  obtain ⟨_,activityReader,activityLookup,activity⟩ := S05SharedChildActivity.construct after.tree (advanced tracker.global room) P.runtime tag tracker.global.nextPointerTag W.pointer.grant parent
    tagged parentAfter freshAfter nodesRoom tagBound false unheld start amount nonzero capacity
  have same : activityReader = reader := Option.some.inj (activityLookup.symm.trans lookup)
  subst activityReader
  have readCaps : OwnedOn (GeneralBorrowSharedReadConstructor.Capabilities
      (child W.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed).tree
      tracker.global.protectedTags W.pointer.grant reader) start (start+amount)
      (child W.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed).tree.locations := by
    intro position valid positive lower upper
    obtain ⟨⟨normal⟩,readerCap⟩ := both position valid positive lower upper
    exact ⟨⟨DuplicatePrefixNormalKind.of_normal _ _ _ _ normal .Read⟩,readerCap⟩
  refine ⟨P,caps.1,caps.2.1,caps.2.2.1.trans P.capacity,?_,reader,lookup,readCaps,activity⟩
  have growth := caps.2.2.2.1
  change _ ≤ after.tree.nodes.data.size+1 at growth
  rw [P.nodes] at growth
  exact growth


/-- The same shared expression retains the current Bool child's disjoint
bytes and extends the optional parent interpretation by precisely r→q. -/
theorem construct_framed {before tracker data owner id offset length}
    (W : UniformWindow before tracker data owner id offset length .mut)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (tag : BorTag) (concrete : W.pointer.value.provenance = .concrete id tag)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615)
    (distinct : W.allocation.extra.roots.toList.Nodup) (short : W.allocation.extra.nodes.size < 65536)
    (nodeRoom : W.allocation.extra.nodes.size+1 ≤ 4294967295)
    (start amount : UInt64) (startEq : start.toNat = offset) (amountEq : amount.toNat = length)
    (nonzero : amount ≠ 0) (bounds : start.toNat+amount.toNat ≤ W.allocation.extra.locations.size.bytes.toNat)
    (target : UniIndex) (targetNode : TreeNode) (targetAt : W.allocation.extra.nodes.get target = some targetNode)
    (lower upper : UInt64)
    (apart : ∀ point : UInt64, lower.toNat ≤ point.toNat → point.toNat < upper.toNat →
      point.toNat < start.toNat ∨ (start+amount).toNat ≤ point.toNat)
    (targetOwned : OwnedOn (S05CompletedAncestryReadMutable.Authority W.allocation.extra W.precise.completion
      tracker.global.protectedTags target) lower upper W.allocation.extra.locations) :
    ∃ _P : Preparation W tag start amount room,
      let actual := child W.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed
      actual.outcome = .ok () ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree (advanced tracker.global room) ∧
      actual.tree.locations.size = W.allocation.extra.locations.size ∧ actual.tree.nodes.size ≤ W.allocation.extra.nodes.size+1 ∧
      ∃ reader, actual.tree.indexOfTag tracker.global.nextPointerTag = some reader ∧
        ParentInterpretation actual.tree (S05ConcreteProtectedChildCompletion.extend W.precise.completion reader W.pointer.grant) ∧
        OwnedOn (GeneralBorrowSharedReadConstructor.Capabilities actual.tree tracker.global.protectedTags W.pointer.grant reader)
          start (start+amount) actual.tree.locations ∧
        GeneralBorrowFreshActiveWithin.ActiveWithin actual.tree reader .Read start (start+amount) ∧
        OwnedOn (S05CompletedAncestryReadMutable.Authority actual.tree
          (S05ConcreteProtectedChildCompletion.extend W.precise.completion reader W.pointer.grant)
          tracker.global.protectedTags target) lower upper actual.tree.locations ∧
        S05ConcreteProtectedChildCompletion.LeafFrame
          (read W.allocation.extra tracker.global.protectedTags tag start amount .VisitChildrenOfAccessed).tree
          actual.tree reader W.pointer.grant := by
  obtain ⟨P,done,afterRuntime,capacity,growth,reader,lookup,caps,activity⟩ := construct W runtime tag concrete room distinct short nodeRoom start amount startEq amountEq nonzero bounds
  let after := read W.allocation.extra tracker.global.protectedTags tag start amount .VisitChildrenOfAccessed
  have high := GeneralBorrowForestTagHighWater.complete W.allocation.extra _ _ runtime.below runtime.formed.allocator.nodeTags
  obtain ⟨fresh,_,unheld⟩ := GenericFunctionTagFormation.fresh_above W.allocation.extra _ _ tracker.global.nextPointerTag high (Nat.le_refl _)
  have freshAfter : GeneralBorrowTagMap.Fresh after.tree.tagMapping tracker.global.nextPointerTag := by rw [P.tags];exact fresh
  obtain ⟨parent,parentAt,_,binding⟩ := W.binding
  rw [concrete] at binding
  have parentAfter : after.tree.nodeAt W.pointer.grant = some parent := by change after.tree.nodes.get _ = _;rw [P.nodes];exact parentAt
  have tagged : after.tree.indexOfTag tag = some W.pointer.grant := by rw [binding.2];exact P.runtime.formed.allocator.nodeTags _ _ parentAfter
  have targetAfter : after.tree.nodes.get target = some targetNode := by rw [P.nodes];exact targetAt
  have boundsAfter : start.toNat+amount.toNat ≤ after.tree.locations.size.bytes.toNat := by rw [P.capacity];exact bounds
  have nodesRoom : after.tree.nodes.size+1 ≤ 4294967295 := by change after.tree.nodes.data.size+1 ≤ _;rw [P.nodes];exact nodeRoom
  have tagBound : tracker.global.nextPointerTag.value.toNat < (advanced tracker.global room).nextPointerTag.value.toNat := by
    have successor := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag room
    change tracker.global.nextPointerTag.value.toNat < (TypedRetagEmpty.successorTag tracker.global.nextPointerTag room).value.toNat
    omega
  have ownedAfter : OwnedOn (S05CompletedAncestryReadMutable.Authority after.tree W.precise.completion
      tracker.global.protectedTags target) lower upper after.tree.locations := by
    have retained := GeneralBorrowRangeOutsideOwned.owned (S05CompletedAncestryReadMutable.Authority W.allocation.extra W.precise.completion tracker.global.protectedTags target)
      W.allocation.extra (.concrete tag) (Size.ofBytes start) (Size.ofBytes amount) .Read tracker.global.protectedTags .VisitChildrenOfAccessed runtime.formed.well bounds lower upper apart targetOwned
    intro position valid positive lower upper index node present
    exact retained position valid positive lower upper index node (by rw [←P.nodes];exact present)
  have primaryLive : ∃ node,after.tree.nodes.get allocationRoot = some node := by
    obtain ⟨node,nodeAt,_⟩ := W.issued.capability.rootNode
    exact ⟨node,by rw [P.nodes];exact nodeAt⟩
  have parentOrder : parent.tag.value ≤ tracker.global.nextPointerTag.value :=
    UInt64.le_of_lt (GeneralBorrowParentTagInvariant.parent_below_fresh W.allocation.extra tracker.global runtime W.pointer.grant parent parentAt)
  obtain ⟨_,_,_,_,other,otherLookup,leaf,parents,retained,old⟩ := CurrentCallSharedConstructorFrame.construct after.tree (advanced tracker.global room) W.precise.completion P.runtime P.parents
    tag tracker.global.nextPointerTag W.pointer.grant target parent targetNode tagged parentAfter targetAfter freshAfter nodesRoom tagBound unheld
    start amount lower upper nonzero boundsAfter apart primaryLive parentOrder ownedAfter
  have same : other = reader := Option.some.inj (otherLookup.symm.trans lookup)
  subst other
  exact ⟨P,done,afterRuntime,capacity,growth,reader,lookup,parents,caps,activity,retained,leaf⟩


/-- Current q resources derive the real shared-reference MIR statement via the existing actual source operation. -/
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
    (data : Identities) (owner : Nat)
    (W : UniformWindow machine tracker data owner id offset.toNat len.toNat .mut)
    (allocationEq : W.allocation = entry.allocation)
    (concrete : W.pointer.value.provenance = .concrete id parentTag)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (distinct : W.allocation.extra.roots.toList.Nodup) (short : W.allocation.extra.nodes.size < 65536)
    (nodeRoom : W.allocation.extra.nodes.size+1 ≤ 4294967295)
    (bounds : offset.toNat+len.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat)
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (localId : MIR.LocalId) (different : localId ≠ 1)
    (validSource : (1 : MIR.LocalId) < frame.locals.size) (validDest : localId < frame.locals.size)
    (sourceLive : frame.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm))
    (sourceCached : frame.locals[1].layout = some ActualReferenceMetadata.reference)
    (destLive : frame.locals[localId].value = .live (.immediate .uninit))
    (destUncached : frame.locals[localId].layout = none)
    (query : CompilerFrameContext.computeLocalLayout PreparedReflection.actual.compiler localId
      (Storage.withCurrent frames frame machine) = .ok (layout true) (Storage.withCurrent frames frame machine))
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false) :
    let inner := config options remaining span
    let value := RetagReferencePlace.sliceValue inner.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len (layout true)
    let resultMachine := {ReferenceBorrowDriver.allocatedMachine machine tracker fresh with
      memory := RetagEntry.updatedMemory machine.memory id entry (child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree}
    evalRvalueIntoPlace (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      (.Ref region (RootReferenceRvalue.borrowKind true) ⟨1,#[.Deref]⟩) ⟨localId,#[]⟩ (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames (ActualLocalCopy.written frame localId (layout true) validDest value.imm) resultMachine) := by
  have lenNonzero : len ≠ 0 := by intro zero;rw [zero] at positive;cases positive
  obtain ⟨P,sharedDone,_,_,_,reader,lookup,caps,activity⟩ := construct W runtime parentTag concrete fresh distinct short nodeRoom
    offset len rfl rfl lenNonzero (by rw [allocationEq];exact bounds)
  have readDone := P.completed
  rw [allocationEq] at readDone sharedDone
  exact CurrentCallSharedReference.rvalue_of_steps options limits remaining span ctx debugOff cmp region dynamicFuel validityFuel fuelEq validationFuel
    base offset len id entry positive nonzero signedFits frames frame machine tracker enabled defaultMode fresh parentTag bounds readDone sharedDone capacity
    localId different validSource validDest sourceLive sourceCached destLive destUncached query noClocks ghost shallow cachedAddress present race metadata notConstructed

end
end DuplicatePrefix.CurrentCallResourceDefaultShared
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallResourceDefaultShared.").length != 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved current Default shared dependency {dependency}"
