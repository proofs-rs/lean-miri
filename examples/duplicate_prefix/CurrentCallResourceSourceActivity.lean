import duplicate_prefix.CurrentCallResourceSourceInitialActivity
import duplicate_prefix.CurrentCallProtectedConstructorOldFacets
import duplicate_prefix.CurrentCallRootActivity
import duplicate_prefix.S02HiddenLeafQuietWildcardRange

namespace DuplicatePrefix.CurrentCallResourceSourceActivity
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization GeneralBorrowFnEntryRegistration CurrentCallResourceEntryBody
open GeneralRangeMapOrigins
open GeneralBorrowExposedNonleafPrimaryPath OrdinaryBorrowAuthority GeneralBorrowProjection GeneralBorrowForest
open GeneralBorrowWildcardParentTagOrder GeneralBorrowExposureCardinality BorrowRangeAccess GeneralRangeMapState
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

private theorem window_normals {before tracker data owner id offset length mode}
    (Q : UniformWindow before tracker data owner id offset length mode) (G : Geometry Q)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts Q.allocation.extra tracker.global)
    (exclusive : demandOf mode=.exclusive) (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
    (bounds : start.toNat+amount.toNat≤Q.allocation.extra.locations.size.bytes.toNat) :
    OwnedOn (fun location=>Nonempty (DuplicatePrefixBorrowAuthorization.Normal Q.allocation.extra location tracker.global.protectedTags Q.pointer.grant)) start (start+amount) Q.allocation.extra.locations := by
  have noWrap : start.toNat+amount.toNat<2^64 := Nat.lt_of_le_of_lt bounds (UInt64.toNat_lt _)
  have endEq : (start+amount).toNat=start.toNat+amount.toNat := by rw [UInt64.toNat_add,Nat.mod_eq_of_lt noWrap]
  intro position valid positive beforeUpper afterLower
  have segmentPositive := (GeneralRangeMapGeometry.facts Q.allocation.extra.locations runtime.formed.well (by omega)).2.1 position valid
  have member : Q.allocation.extra.locations.entries[position]∈Q.allocation.extra.locations.entries.toList := Array.mem_toList_iff.mpr (Array.getElem_mem valid)
  have obtainNormal : ∀ byte,Window id offset length byte → Q.allocation.extra.locations.entries[position].range.start.toNat≤byte.2 → byte.2<Q.allocation.extra.locations.entries[position].range.stop.toNat → Nonempty (DuplicatePrefixBorrowAuthorization.Normal Q.allocation.extra Q.allocation.extra.locations.entries[position].data tracker.global.protectedTags Q.pointer.grant) := by
    intro byte inside lower upper
    exact CurrentCallResourceAccess.selected_normal Q G exclusive byte inside _ member lower upper (runtime.formed.profile position valid) (runtime.possible position valid)
  by_cases earlier : start.toNat≤Q.allocation.extra.locations.entries[position].range.start.toNat
  · exact obtainNormal (id,Q.allocation.extra.locations.entries[position].range.start.toNat) ⟨rfl,by omega,by omega⟩ (Nat.le_refl _) segmentPositive
  · exact obtainNormal (id,start.toNat) ⟨rfl,by omega,by omega⟩ (by omega) afterLower

private theorem fnentry_frame {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (frame : FrameState) (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (exclusive : demandOf mode=.exclusive) (distinct : W.allocation.extra.roots.toList.Nodup)
    (short : W.allocation.extra.nodes.size<65536) (nodeRoom : W.allocation.extra.nodes.size+1≤4294967295)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length) (nonzero : amount≠0)
    (bounds : start.toNat+amount.toNat≤W.allocation.extra.locations.size.bytes.toNat)
    (output : GeneralBorrowForestFnEntry.Output)
    (actual : CandidateCurrentFnEntryRaw.operation W.allocation.extra tracker.global frame id W.pointer.value.provenance start amount=.ok output)
    (target : UniIndex) (node : TreeNode) (present : W.allocation.extra.nodes.get target=some node)
    (leaf : node.children=#[]) (hidden : node.isExposed=false) (different : target≠W.pointer.grant)
    (lower upper : UInt64) (active : GeneralBorrowFreshActiveWithin.ActiveWithin W.allocation.extra target .Write lower upper) :
    ∃ next,output.child.tree.nodes.get target=some next ∧ next.tag=node.tag ∧ next.parent=node.parent ∧
      next.children=node.children ∧ next.isExposed=node.isExposed ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin output.child.tree target .Write lower upper := by
  have literalEq : output=CurrentCallTypedFnEntry.literal W.allocation.extra tracker.global frame id room W.pointer.value.provenance start amount := by
    exact Except.ok.inj (actual.symm.trans (CurrentCallTypedFnEntry.literal_operation _ _ _ _ room _ _ _))
  obtain ⟨_,held,_,_,_,freshTag⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare W.allocation.extra tracker.global frame id room runtime
  let registration := registered tracker.global frame id room
  obtain ⟨_,afterRuntime,_,_,nodes,_,tags,bytes⟩ := CurrentCallResourceFnEntry.prepare_read_selected W runtime frame room exclusive
    distinct short start amount startEq amountEq bounds
  change DuplicatePrefixBorrowContract.RuntimeFacts (CurrentCallTypedFnEntry.literal W.allocation.extra tracker.global frame id room W.pointer.value.provenance start amount).access.tree registration.1 at afterRuntime
  rw [←literalEq] at afterRuntime
  change (CurrentCallTypedFnEntry.literal W.allocation.extra tracker.global frame id room W.pointer.value.provenance start amount).access.tree.nodes=W.allocation.extra.nodes at nodes
  change (CurrentCallTypedFnEntry.literal W.allocation.extra tracker.global frame id room W.pointer.value.provenance start amount).access.tree.tagMapping=W.allocation.extra.tagMapping at tags
  change (CurrentCallTypedFnEntry.literal W.allocation.extra tracker.global frame id room W.pointer.value.provenance start amount).access.tree.locations.size=W.allocation.extra.locations.size at bytes
  rw [←literalEq] at nodes tags bytes
  have freshAfter : GeneralBorrowTagMap.Fresh output.access.tree.tagMapping tracker.global.nextPointerTag := by rw [tags];exact freshTag
  have nodeCapacity : output.access.tree.nodes.size+1≤4294967295 := by rw [nodes];exact nodeRoom
  have childBounds : start.toNat+amount.toNat≤output.access.tree.locations.size.bytes.toNat := by rw [bytes];exact bounds
  have tagBound : tracker.global.nextPointerTag.value.toNat<registration.1.nextPointerTag.value.toNat := by
    have successor := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag room
    change tracker.global.nextPointerTag.value.toNat<(TypedRetagEmpty.successorTag tracker.global.nextPointerTag room).value.toNat
    omega
  have tagHeld : registration.1.protectedTags.contains tracker.global.nextPointerTag=true := by unfold ProtectedTags.contains;rw [held];rfl
  have childEq : output.child=output.access.tree.newChild (Size.ofBytes start) (CandidateCurrentWindowPointerChecks.extraOf W.pointer.value.provenance)
    tracker.global.nextPointerTag (DedupRangeMap.new (Size.ofBytes amount) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true := by rw [literalEq];rfl
  have registeredRuntime := (GeneralBorrowFnEntryRegistrationRuntime.prepare W.allocation.extra tracker.global frame id room runtime).2.2.2.1
  obtain ⟨G⟩ := CurrentCallResourceFnEntry.registered_geometry_selected W runtime frame room exclusive
  have normals := window_normals (CurrentCallResourceFnEntry.registered_window W runtime frame room) G registeredRuntime exclusive start amount startEq amountEq bounds
  have targetAfter : output.access.tree.nodes.get target=some node := by rw [nodes];exact present
  cases prov : W.pointer.value.provenance with
  | concrete actualId parentTag =>
    obtain ⟨parentNode,parentAt,_,binds⟩ := W.binding
    rw [prov] at binds
    have taggedOld : W.allocation.extra.indexOfTag parentTag=some W.pointer.grant := by rw [binds.2];exact runtime.formed.allocator.nodeTags _ _ parentAt
    have activityRead := CurrentCallRootActivity.concrete_of_normal W.allocation.extra registration.1 registeredRuntime parentTag W.pointer.grant target parentNode parentAt
      start amount bounds normals taggedOld node present leaf hidden different lower upper active .Read .VisitChildrenOfAccessed
    have activeAfter : GeneralBorrowFreshActiveWithin.ActiveWithin output.access.tree target .Write lower upper := by
      rw [literalEq]
      simpa only [CurrentCallTypedFnEntry.literal,prov,CandidateCurrentWindowPointerChecks.extraOf] using activityRead
    have parentAfter : output.access.tree.nodeAt W.pointer.grant=some parentNode := by change output.access.tree.nodes.get _=_;rw [nodes];exact parentAt
    have tagged : output.access.tree.indexOfTag parentTag=some W.pointer.grant := by rw [binds.2];exact afterRuntime.formed.allocator.nodeTags _ _ parentAfter
    have result := CurrentCallProtectedConstructorOldFacets.concrete output.access.tree registration.1 afterRuntime parentTag tracker.global.nextPointerTag W.pointer.grant target parentNode node
      tagged parentAfter targetAfter different freshAfter nodeCapacity start amount nonzero childBounds .Write lower upper activeAfter
    obtain ⟨next,found,tagEq,parentEq,childrenEq,hiddenEq⟩ := result.1
    rw [childEq]
    simpa only [prov,CandidateCurrentWindowPointerChecks.extraOf] using (Exists.intro next (And.intro found (And.intro tagEq (And.intro parentEq (And.intro childrenEq (And.intro hiddenEq result.2))))))
  | wildcard =>
    have activityRead := S02HiddenLeafQuietWildcardRange.wildcard W.allocation.extra registration.1 registeredRuntime start amount bounds target node present leaf hidden lower upper active .Read .VisitChildrenOfAccessed
    have activeAfter : GeneralBorrowFreshActiveWithin.ActiveWithin output.access.tree target .Write lower upper := by
      rw [literalEq]
      simpa only [CurrentCallTypedFnEntry.literal,prov,CandidateCurrentWindowPointerChecks.extraOf] using activityRead
    have result := CurrentCallProtectedConstructorOldFacets.wildcard output.access.tree registration.1 afterRuntime tracker.global.nextPointerTag target node targetAfter freshAfter nodeCapacity start amount nonzero childBounds .Write lower upper activeAfter
    obtain ⟨next,found,tagEq,parentEq,childrenEq,hiddenEq⟩ := result.1
    rw [childEq]
    simpa only [prov,CandidateCurrentWindowPointerChecks.extraOf] using (Exists.intro next (And.intro found (And.intro tagEq (And.intro parentEq (And.intro childrenEq (And.intro hiddenEq result.2))))))

private theorem same_root_ancestor {tree completion} (model : ParentInterpretation tree completion)
    {root query source : UniIndex} {rootNode queryNode : TreeNode}
    (rootAt : tree.nodes.get root = some rootNode) (parentless : rootNode.parent = none)
    (queryAt : tree.nodes.get query = some queryNode) (queryPath : Path tree root query)
    (sourcePath : Path tree root source) (below : Below completion query source) : Path tree query source := by
  rcases model.physical_or_attachment queryAt below with physical | attachment
  · exact physical
  · obtain ⟨origin,next,originNode,nextNode,path,originAt,_,nextAt,nextNone,edge,after⟩ := attachment
    have nextRoot : Below completion next root := by
      rcases model.physical_suffix sourcePath after with above | physicalNext
      · exact above
      · have same := CompletedBorrowAncestry.physical_roots_unique rootAt parentless nextAt nextNone
          physicalNext (.refl _ nextNode nextAt)
        subst next
        exact .refl root
    have rootOrigin := model.physical_below (CompletedBorrowAncestry.path_trans queryPath path)
    have before := UInt64.le_iff_toNat_le.mp (model.tag_le rootAt originAt rootOrigin)
    have afterTag := UInt64.le_iff_toNat_le.mp (model.tag_le nextAt rootAt nextRoot)
    obtain ⟨actual,actualAt,_,older⟩ := model.virtual_parent nextAt nextNone edge
    have same := Option.some.inj (originAt.symm.trans actualAt)
    subst actual
    have strict := UInt64.lt_iff_toNat_lt.mp older
    omega

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

private theorem write_frame (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (model : ParentInterpretation tree completion)
    (source target : UniIndex) (sourceNode targetNode : TreeNode)
    (sourceAt : tree.nodes.get source=some sourceNode) (targetAt : tree.nodes.get target=some targetNode)
    (leaf : targetNode.children=#[]) (hidden : targetNode.isExposed=false) (different : target≠source)
    (start amount lower upper : UInt64) (bounds : start.toNat+amount.toNat≤tree.locations.size.bytes.toNat)
    (owned : OwnedOn (S05CompletedAncestryReadMutable.Authority tree completion global.protectedTags source) start (start+amount) tree.locations)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree target .Write lower upper) :
    GeneralBorrowFreshActiveWithin.ActiveWithin (tree.performBorrowAccessRange (.concrete sourceNode.tag) (Size.ofBytes start) (Size.ofBytes amount) .Write global.protectedTags .VisitChildrenOfAccessed).tree target .Write lower upper := by
  obtain ⟨rootPosition,root,rootNode,slot,rootAt,path⟩ := CandidateCurrentWindowAuthority.root_path tree runtime.formed.toGraphState source sourceNode sourceAt
  obtain ⟨actual,actualAt,parentless⟩ := model.graph.rootNodes root (Array.mem_toList_iff.mpr (Array.mem_of_getElem? slot))
  have eqNode : actual=rootNode := Option.some.inj (actualAt.symm.trans rootAt)
  subst actual
  have classification : ∀ index node,tree.nodes.get index=some node → GeneralBorrowExposedNonleafPrimaryPath.Path tree root index → (Below completion index source ↔ GeneralBorrowExposedNonleafPrimaryPath.Path tree index source) := by
    intro index node present queryPath
    exact ⟨same_root_ancestor model rootAt parentless present queryPath path,model.physical_below⟩
  obtain ⟨depth⟩ := runtime.formed.depth
  have normals : OwnedOn (fun location=>Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree location global.protectedTags source)) start (start+amount) tree.locations := by
    intro position valid positive low high
    have authority:=owned position valid positive low high
    exact normal_of_authority tree completion _ global.protectedTags runtime.formed.toGraphState depth runtime.formed.fits rootPosition root source rootNode slot rootAt path classification
      (fun index node found _ =>(authority index node found).1) (fun index node found _ =>(authority index node found).2)
  exact CurrentCallRootActivity.concrete_of_normal tree global runtime sourceNode.tag source target sourceNode sourceAt start amount bounds normals
    (runtime.formed.allocator.nodeTags _ _ sourceAt) targetNode targetAt leaf hidden different lower upper active .Write .VisitChildrenOfAccessed

private theorem window_runtime {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode)
    (state : DuplicatePrefixRuntimeInput.State before tracker)
    (highwater : ∀ row∈before.memory.live.toList,GeneralBorrowForestTagHighWater.Below row.2.allocation.extra tracker.global.protectedTags tracker.global.nextPointerTag) :
    DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global ∧ W.allocation.extra.roots.toList.Nodup := by
  have present := W.present
  simp only [Present,ActualWorld,Array.toList_map] at present
  obtain ⟨⟨actualId,entry⟩,member,equal⟩ := List.mem_map.mp present
  rcases Prod.mk.inj equal with ⟨rfl,equal⟩
  have treeEq : entry.allocation.extra=W.allocation.extra := congrArg Allocation.extra equal
  exact ⟨⟨by simpa only [treeEq] using state.formed (actualId,entry) member,
    by simpa only [treeEq] using state.coherent (actualId,entry) member,
    by simpa only [treeEq] using state.possible (actualId,entry) member,
    by simpa only [treeEq] using highwater (actualId,entry) member⟩,
    by simpa only [treeEq] using state.roots (actualId,entry) member⟩

variable {options remaining span frames root before tracker data owner id offset len W place limits count}
    {C : Conditions options remaining span frames root before tracker data owner id offset len W place}
    (out : Output limits C count)

include out in
private theorem source_bounds : (UInt64.ofNat offset).toNat=offset ∧
    (UInt64.ofNat offset).toNat+len.toNat≤W.allocation.extra.locations.size.bytes.toNat := by
  have last := (out.sourceWitness.window (id,offset+len.toNat-1) ⟨rfl,by have p:=C.positive;omega,by have p:=C.positive;omega⟩).1
  have positive := C.positive
  have extent := W.issued.capability.extent
  have treeExtent := W.issued.capability.treeExtent
  have bounded := UInt64.toNat_lt W.allocation.byteSize.bytes
  have fits : offset<2^64 := by omega
  have start : (UInt64.ofNat offset).toNat=offset := by simp only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt fits]
  exact ⟨start,by rw [start,treeExtent,←extent];omega⟩

private def rolePrecise : PreciseAllocation := {C.V.precise with completion:=out.R.completion}
private def roleData : Identities :=
  {data with interpretation:={data.interpretation with precise:=data.interpretation.precise.push (C.physical.id,rolePrecise out)}}
private def boolRole : UniformWindow out.sourceMachine ⟨out.sourceOutput.global,tracker.retagMode⟩ (roleData out)
    C.returnOwner C.physical.id C.physical.offset.toNat 1 .ret where
  loan:=C.V.loan
  pointer:=C.V.pointer
  allocation:=C.V.allocation.setExtra out.R.tree
  precise:=rolePrecise out
  loanAt:=C.V.loanAt
  pointerAt:=C.V.pointerAt
  pointerId:=C.V.pointerId
  present:=out.R.present
  preciseAt:=Array.mem_toList_iff.mpr (Array.mem_push.mpr (.inr rfl))
  binding:=out.R.binding
  issued:=out.R.issued
  parents:=out.R.parents
  window:=out.R.window

private theorem role_runtime : DuplicatePrefixBorrowContract.RuntimeFacts out.R.tree out.sourceOutput.global ∧
    out.R.tree.roots.toList.Nodup ∧ out.R.tree.nodes.size<65536 := by
  by_cases same : C.physical.id=id
  · have trees:=out.sameTree same
    have growth:=CurrentCallResourceEntryFacets.source_growth out
    have room:=C.boolRoom
    rw [C.sameAllocation same] at room
    rw [trees.1]
    refine ⟨out.sourceWitness.runtime,?_,by omega⟩
    obtain ⟨runtime,distinct⟩ := window_runtime W C.state C.highwater
    exact CurrentCallResourceSourceKeyOrigin.roots W runtime C.state C.highwater C.borrowFrame C.fresh (by rfl) distinct C.sourceShort
      (by have h:=C.sourceShort;omega) (UInt64.ofNat offset) len (source_bounds out).1 rfl
      (by intro zero;have p:=C.positive;rw [zero] at p;cases p) (source_bounds out).2 out.sourceOutput out.sourceActual
  · obtain ⟨runtime,distinct⟩ := window_runtime C.V C.state C.highwater
    have current := (GeneralBorrowFnEntryRegistrationRuntime.prepare C.V.allocation.extra tracker.global C.borrowFrame id C.fresh runtime).2.2.2.1
    rw [(out.otherTree same).1]
    refine ⟨?_,distinct,by have room:=C.boolRoom;omega⟩
    rw [out.sourceGlobal]
    exact current


private theorem same_current (same : out.physical.id=id) :
    ∃ node,out.updated.extra.nodes.get out.sourceChild=some node ∧ node.tag=out.sourceOutput.tag ∧
      node.children=#[] ∧ node.isExposed=false ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin out.updated.extra out.sourceChild .Write (UInt64.ofNat offset) (UInt64.ofNat offset+len) := by
  let B:=boolRole out
  have originalSame:=out.physicalId.symm.trans same
  have treeEq : B.allocation.extra=out.sourceOutput.child.tree := (out.sameTree originalSame).1
  have actual : CandidateCurrentFnEntryRaw.operation B.allocation.extra out.sourceOutput.global out.sourceOutput.frame C.physical.id B.pointer.value.provenance out.physical.offset 1=.ok out.boolOutput := by
    simpa only [B,boolRole,Allocation.setExtra,Allocation.mapExtra,out.physicalId] using out.boolActual
  have bounds : out.physical.offset.toNat+1≤B.allocation.extra.locations.size.bytes.toNat := by
    have first := (B.window (C.physical.id,out.physical.offset.toNat) ⟨rfl,by rw [out.physicalOffset];exact Nat.le_refl _,by rw [out.physicalOffset];omega⟩).1
    rw [B.issued.capability.treeExtent,←B.issued.capability.extent]
    omega
  have short : B.allocation.extra.nodes.size<65536 := (role_runtime out).2.2
  obtain ⟨qnode,qAt,qTag,qLeaf,qHidden,qActive⟩ := CurrentCallResourceSourceInitialActivity.initial out
  have targetAt : B.allocation.extra.nodes.get out.sourceChild=some qnode := by rw [treeEq];exact qAt
  have targetActive : GeneralBorrowFreshActiveWithin.ActiveWithin B.allocation.extra out.sourceChild .Write (UInt64.ofNat offset) (UInt64.ofNat offset+len) := by rw [treeEq];exact qActive
  have different : out.sourceChild≠B.pointer.grant := by
    change out.sourceChild≠C.V.pointer.grant
    obtain ⟨oldNode,oldAt,_,_⟩ := C.V.binding
    have oldAtW : W.allocation.extra.nodes.get C.V.pointer.grant=some oldNode := by rw [←C.sameAllocation originalSame];exact oldAt
    obtain ⟨next,nextAt,tagEq,_,_,_⟩ := out.sourceWitness.oldNodes C.V.pointer.grant oldNode oldAtW
    intro equal
    have actualAt : out.sourceOutput.child.tree.nodes.get out.sourceChild=some next := by rw [equal];exact nextAt
    have eqNode : next=qnode := Option.some.inj (actualAt.symm.trans qAt)
    have originalRuntime:=(window_runtime C.V C.state C.highwater).1
    have older:=GeneralBorrowParentTagInvariant.parent_below_fresh C.V.allocation.extra tracker.global originalRuntime C.V.pointer.grant oldNode oldAt
    have tags : oldNode.tag=tracker.global.nextPointerTag := tagEq.symm.trans ((congrArg TreeNode.tag eqNode).trans (qTag.trans out.sourceTag))
    rw [tags] at older
    exact (UInt64.lt_irrefl _ older)
  obtain ⟨next,nextAt,nextTag,nextParent,nextChildren,nextHidden,nextActive⟩ := fnentry_frame B (role_runtime out).1 out.sourceOutput.frame out.returnRoom (by rfl)
    (role_runtime out).2.1 short (by omega) out.physical.offset 1 (congrArg UInt64.toNat out.physicalOffset) rfl (by decide) bounds out.boolOutput actual
    out.sourceChild qnode targetAt qLeaf qHidden different (UInt64.ofNat offset) (UInt64.ofNat offset+len) targetActive
  obtain ⟨output,child,operation,tag,global,frame,readDone,childDone,lookup,⟨witness⟩⟩ := CurrentCallResourceFnEntry.correlated_borrow_selected B (role_runtime out).1 out.sourceOutput.frame out.returnRoom (by rfl)
    (role_runtime out).2.1 short (by omega) out.physical.offset 1 (congrArg UInt64.toNat out.physicalOffset) rfl (by decide) bounds
  have eqOutput : output=out.boolOutput := Except.ok.inj (operation.symm.trans actual)
  subst output
  have ownLookup : out.boolOutput.child.tree.indexOfTag out.boolOutput.tag=some out.boolChild := by
    rw [←out.boolNodeTag]
    exact witness.runtime.formed.allocator.nodeTags _ _ out.boolNodeAt
  have eqChild : child=out.boolChild := Option.some.inj (lookup.symm.trans ownLookup)
  subst child
  have childDifferent : out.sourceChild≠out.boolChild := by
    intro equal
    have actualAt : out.boolOutput.child.tree.nodes.get out.boolChild=some next := by rw [←equal];exact nextAt
    have eqNode : next=out.boolNode := Option.some.inj (actualAt.symm.trans out.boolNodeAt)
    have eqTag : out.sourceOutput.tag=out.sourceOutput.global.nextPointerTag := qTag.symm.trans (nextTag.symm.trans ((congrArg TreeNode.tag eqNode).trans (out.boolNodeTag.trans out.boolTag)))
    have first:=GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag C.fresh
    have numeric:=congrArg (fun tag : BorTag=>tag.value.toNat) eqTag
    rw [out.sourceGlobal,out.sourceTag] at numeric
    change tracker.global.nextPointerTag.value.toNat=(TypedRetagEmpty.successorTag tracker.global.nextPointerTag C.fresh).value.toNat at numeric
    omega
  have afterBounds : out.physical.offset.toNat+1≤out.boolOutput.child.tree.locations.size.bytes.toNat := by rw [witness.capacity];exact bounds
  have active := write_frame out.boolOutput.child.tree out.boolOutput.global _ witness.runtime witness.parents out.boolChild out.sourceChild out.boolNode next out.boolNodeAt nextAt
    (nextChildren.trans qLeaf) (nextHidden.trans qHidden) childDifferent out.physical.offset 1 (UInt64.ofNat offset) (UInt64.ofNat offset+len) afterBounds witness.owned nextActive
  refine ⟨next,?_,nextTag.trans qTag,nextChildren.trans qLeaf,nextHidden.trans qHidden,?_⟩
  · rw [out.updatedNodes];exact nextAt
  · rw [out.updatedExtra,←out.boolTag,←out.boolNodeTag]
    exact active

/-- The current q child retains its own exact activity window through the
actual entry Bool Read, constructor and Write, in both allocation cases. -/
theorem current : ∃ node,(CurrentCallResourceSourceFinal.entry out).allocation.extra.nodes.get out.sourceChild=some node ∧
    node.tag=out.sourceOutput.tag ∧ node.children=#[] ∧ node.isExposed=false ∧
    GeneralBorrowFreshActiveWithin.ActiveWithin (CurrentCallResourceSourceFinal.entry out).allocation.extra out.sourceChild .Write (UInt64.ofNat offset) (UInt64.ofNat offset+len) := by
  by_cases same : out.physical.id=id
  · simpa only [CurrentCallResourceSourceFinal.entry,ite_eq_left same] using same_current out same
  · simpa only [CurrentCallResourceSourceFinal.entry,ite_eq_right same,out.sourceAllocation,Allocation.setExtra,Allocation.mapExtra] using CurrentCallResourceSourceInitialActivity.initial out

end
end DuplicatePrefix.CurrentCallResourceSourceActivity
