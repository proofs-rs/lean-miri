import duplicate_prefix.CurrentCallSpatialEntry
import duplicate_prefix.CurrentCallProtectedConstructorOldFacets
import duplicate_prefix.CurrentCallRootActivity
import duplicate_prefix.S02HiddenLeafQuietWildcardRange
import duplicate_prefix.S03ReturnChildMetadata
import duplicate_prefix.GeneralBorrowConstructorChildActivity
import duplicate_prefix.GeneralBorrowWildcardRootConstructorActivity
import duplicate_prefix.GeneralBorrowEffectfulRetagCausalOrder

/-! Current q metadata and Write activity after the actual spatial source
FnEntry and actual Bool operation. No whole-window source origin is chosen. -/
namespace DuplicatePrefix.CurrentCallSpatialEntryActivity
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization GeneralBorrowFnEntryRegistration CurrentCallSpatialEntry
open CurrentCallSpatialCover CurrentCallSpatialJointInstall
open GeneralRangeMapOrigins GeneralBorrowExposedNonleafPrimaryPath OrdinaryBorrowAuthority GeneralBorrowProjection GeneralBorrowForest
open GeneralBorrowWildcardParentTagOrder GeneralBorrowExposureCardinality BorrowRangeAccess GeneralRangeMapState
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
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


private theorem spatial_facets {before tracker ctx mode offset length}
    (role : RoleCover before tracker ctx mode offset length)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (frame : FrameState) (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (exclusive : demandOf mode=.exclusive) (distinct : role.backing.allocation.extra.roots.toList.Nodup)
    (short : role.backing.allocation.extra.nodes.size<65536) (nodeRoom : role.backing.allocation.extra.nodes.size+1≤4294967295)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length) (nonzero : amount≠0)
    (bounds : start.toNat+amount.toNat≤role.backing.allocation.extra.locations.size.bytes.toNat) :
    let output := CurrentCallSpatialEntryRead.output role frame room start amount
    DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree output.global ∧
    output.child.tree.locations.size=role.backing.allocation.extra.locations.size ∧
    ∃ child node, output.child.tree.indexOfTag tracker.global.nextPointerTag=some child ∧
      output.child.tree.nodeAt child=some node ∧ node.tag=tracker.global.nextPointerTag ∧
      node.children=#[] ∧ node.isExposed=false ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin output.child.tree child .Write start (start+amount) := by
  let output := CurrentCallSpatialEntryRead.output role frame room start amount
  change DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree output.global ∧
    output.child.tree.locations.size=role.backing.allocation.extra.locations.size ∧
    ∃ child node, output.child.tree.indexOfTag tracker.global.nextPointerTag=some child ∧
      output.child.tree.nodeAt child=some node ∧ node.tag=tracker.global.nextPointerTag ∧
      node.children=#[] ∧ node.isExposed=false ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin output.child.tree child .Write start (start+amount)
  obtain ⟨_,held,_,_,_,freshTag⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare role.backing.allocation.extra tracker.global frame role.backing.id room runtime
  let registration := registered tracker.global frame role.backing.id room
  have outputGlobal : output.global=registration.1 := rfl
  rw [outputGlobal]
  obtain ⟨contract,afterRuntime,_⟩ := CurrentCallSpatialEntryRead.invoke role exclusive runtime distinct short frame room start amount startEq amountEq nonzero bounds
  have nodes := contract.nodes
  have tags := contract.tags
  have bytes := contract.capacity
  change DuplicatePrefixBorrowContract.RuntimeFacts output.access.tree registration.1 at afterRuntime
  change output.access.tree.nodes=role.backing.allocation.extra.nodes at nodes
  change output.access.tree.tagMapping=role.backing.allocation.extra.tagMapping at tags
  change output.access.tree.locations.size=role.backing.allocation.extra.locations.size at bytes
  have positive : 0<length := by
    have nonzeroNat : amount.toNat≠0 := by intro zero;exact nonzero (UInt64.toNat_inj.mp zero)
    omega
  have request : Window role.backing.id offset length (role.backing.id,offset) := ⟨rfl,Nat.le_refl _,by omega⟩
  obtain ⟨selected,inside⟩ := role.covered _ request
  have overlap : ∃byte,Window role.backing.id offset length byte ∧
      Window role.backing.id role.backing.cells[selected].offset role.backing.cells[selected].length byte := ⟨_,request,inside⟩
  have freshAfter : GeneralBorrowTagMap.Fresh output.access.tree.tagMapping tracker.global.nextPointerTag := by rw [tags];exact freshTag
  have nodeCapacity : output.access.tree.nodes.size+1≤4294967295 := by rw [nodes];exact nodeRoom
  have childBounds : start.toNat+amount.toNat≤output.access.tree.locations.size.bytes.toNat := by rw [bytes];exact bounds
  have tagBound : tracker.global.nextPointerTag.value.toNat<registration.1.nextPointerTag.value.toNat := by
    have successor := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag room
    change tracker.global.nextPointerTag.value.toNat<(TypedRetagEmpty.successorTag tracker.global.nextPointerTag room).value.toNat
    omega
  have tagHeld : registration.1.protectedTags.contains tracker.global.nextPointerTag=true := by unfold ProtectedTags.contains;rw [held];rfl
  have childEq : output.child=output.access.tree.newChild (Size.ofBytes start) (CandidateCurrentWindowPointerChecks.extraOf role.family.value.provenance)
    tracker.global.nextPointerTag (DedupRangeMap.new (Size.ofBytes amount) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true := rfl
  cases prov : role.family.value.provenance with
  | concrete id parentTag =>
    obtain ⟨parentNode,parentAt,_,binds⟩ := (role.roles selected overlap).binding
    have parentBinding : id=role.family.allocation ∧ parentTag=parentNode.tag := by
      simpa only [Family.at,prov] using binds
    have parentAfter : output.access.tree.nodeAt (role.roles selected overlap).grant=some parentNode := by change output.access.tree.nodes.get _=_;rw [nodes];exact parentAt
    have tagged : output.access.tree.indexOfTag parentTag=some (role.roles selected overlap).grant := by rw [parentBinding.2];exact afterRuntime.formed.allocator.nodeTags _ _ parentAfter
    have ctor := GeneralBorrowProtectedConstructorRuntime.construct output.access.tree registration.1 afterRuntime parentTag tracker.global.nextPointerTag (role.roles selected overlap).grant parentNode
      tagged parentAfter freshAfter nodeCapacity tagBound tagHeld start amount nonzero childBounds
    obtain ⟨child,node,lookup,present,nodeTag,parent,leaf,hidden,old⟩ := S03ReturnChildMetadata.construct output.access.tree registration.1 afterRuntime parentTag tracker.global.nextPointerTag (role.roles selected overlap).grant parentNode tagged parentAfter freshAfter nodeCapacity start amount nonzero childBounds
    obtain ⟨activeChild,activeLookup,active⟩ := GeneralBorrowConstructorChildActivity.Protected.construct output.access.tree registration.1 afterRuntime parentTag tracker.global.nextPointerTag (role.roles selected overlap).grant parentNode tagged parentAfter freshAfter nodeCapacity start amount nonzero childBounds
    have eqChild : activeChild=child := Option.some.inj (activeLookup.symm.trans lookup)
    subst activeChild
    rw [childEq]
    simpa only [prov,CandidateCurrentWindowPointerChecks.extraOf] using
      And.intro ctor.2.1 (And.intro (ctor.2.2.1.trans bytes) ⟨child,node,lookup,present,nodeTag,leaf,hidden,active⟩)

  | wildcard =>
    have ctor := GeneralBorrowWildcardConstructorRuntime.protected_mutable output.access.tree registration.1 afterRuntime tracker.global.nextPointerTag freshAfter nodeCapacity tagBound tagHeld
      start amount nonzero childBounds
    obtain ⟨mapping,index,inserted,rows,vacant,graph,monotone,growth⟩ := GeneralBorrowWildcardConstructorSlot.select output.access.tree registration.1 afterRuntime tracker.global.nextPointerTag freshAfter nodeCapacity (.ReservedFrz false) .None
    have exactTree := GeneralBorrowWildcardConstructorExact.exact output.access.tree afterRuntime.formed.toState tracker.global.nextPointerTag freshAfter nodeCapacity mapping index inserted
      (.ReservedFrz false) .None GeneralBorrowFreshChild.inside true rfl rfl rfl rfl rfl start amount nonzero childBounds
    have present : (GeneralBorrowPositiveWildcardConstructor.result output.access.tree mapping index tracker.global.nextPointerTag (.ReservedFrz false) .None GeneralBorrowFreshChild.inside start amount).nodeAt index = some (WildcardHitZeroConstructor.rootNode tracker.global.nextPointerTag (.ReservedFrz false) .None) := GeneralBorrowFreshLocation.get_same output.access.tree.nodes index _
    have lookup := graph.allocator.nodeTags index _ present
    obtain ⟨activeChild,activeLookup,active⟩ := GeneralBorrowWildcardRootConstructorActivity.construct output.access.tree registration.1 afterRuntime tracker.global.nextPointerTag freshAfter nodeCapacity start amount nonzero childBounds
    rw [exactTree] at activeLookup active
    have eqChild : activeChild=index := Option.some.inj (activeLookup.symm.trans lookup)
    subst activeChild
    rw [childEq]
    simp only [prov,CandidateCurrentWindowPointerChecks.extraOf]
    refine ⟨ctor.2.1,ctor.2.2.1.trans bytes,?_⟩
    rw [exactTree]
    exact ⟨index,_,lookup,present,rfl,rfl,rfl,active⟩

private theorem backing_runtime {before tracker}
    (backing : AllocationCover before) (state : DuplicatePrefixRuntimeInput.State before tracker)
    (highwater : ∀ row∈before.memory.live.toList,GeneralBorrowForestTagHighWater.Below row.2.allocation.extra tracker.global.protectedTags tracker.global.nextPointerTag) :
    DuplicatePrefixBorrowContract.RuntimeFacts backing.allocation.extra tracker.global ∧ backing.allocation.extra.roots.toList.Nodup := by
  have present := backing.live
  simp only [Present,ActualWorld,Array.toList_map] at present
  obtain ⟨⟨actualId,entry⟩,member,equal⟩ := List.mem_map.mp present
  rcases Prod.mk.inj equal with ⟨rfl,equal⟩
  have treeEq : entry.allocation.extra=backing.allocation.extra := congrArg Allocation.extra equal
  exact ⟨⟨by simpa only [treeEq] using state.formed (backing.id,entry) member,
    by simpa only [treeEq] using state.coherent (backing.id,entry) member,
    by simpa only [treeEq] using state.possible (backing.id,entry) member,
    by simpa only [treeEq] using highwater (backing.id,entry) member⟩,
    by simpa only [treeEq] using state.roots (backing.id,entry) member⟩

variable {options remaining span frames root before tracker ctx offset len source returnOffset ret place}
    {C : Conditions options remaining span frames root before tracker ctx offset len source returnOffset ret place}
    {limits count} (out : Output C limits count)

include out in
private theorem source_bounds : (UInt64.ofNat offset).toNat=offset ∧
    (UInt64.ofNat offset).toNat+len.toNat≤source.backing.allocation.extra.locations.size.bytes.toNat := by
  obtain ⟨entry,base,found,_,extent,_,bound,_⟩ := C.binding
  have same : entry=out.entry := (Prod.mk.inj (Option.some.inj (found.symm.trans out.sourceLive))).2
  subst entry
  have fits : offset<2^64 := by have h:=UInt64.toNat_lt out.entry.allocation.byteSize.bytes;omega
  have startEq : (UInt64.ofNat offset).toNat=offset := by simp only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt fits]
  have treeLength := C.state.treeLength (source.backing.id,out.entry) (Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some out.sourceLive))
  exact ⟨startEq,by rw [startEq,←out.allocation,treeLength,←extent];exact bound⟩

/-- The one actual spatial source constructor creates a hidden Write-active
leaf over its entire source request, independently of the cell parent maps. -/
theorem initial : ∃ node,(sourceOutput C).child.tree.nodes.get out.child=some node ∧
    node.tag=(sourceOutput C).tag ∧ node.children=#[] ∧ node.isExposed=false ∧
    GeneralBorrowFreshActiveWithin.ActiveWithin (sourceOutput C).child.tree out.child .Write
      (UInt64.ofNat offset) (UInt64.ofNat offset+len) := by
  obtain ⟨runtime,distinct⟩ := backing_runtime source.backing C.state C.highwater
  have short : source.backing.allocation.extra.nodes.size<65536 := by have h:=C.sourceRoom;omega
  have nodeRoom : source.backing.allocation.extra.nodes.size+1≤4294967295 := by have h:=C.sourceRoom;omega
  have nonzero : len≠0 := by intro zero;have h:=C.positive;rw [zero] at h;cases h
  obtain ⟨_,_,child,node,lookup,present,tag,leaf,hidden,active⟩ := spatial_facets source runtime C.borrowFrame C.fresh (by rfl)
    distinct short nodeRoom (UInt64.ofNat offset) len (source_bounds out).1 rfl nonzero (source_bounds out).2
  have ownLookup : (sourceOutput C).child.tree.indexOfTag tracker.global.nextPointerTag=some out.child := out.sourceLookup
  have same : child=out.child := Option.some.inj (lookup.symm.trans ownLookup)
  subst child
  exact ⟨node,present,tag,leaf,hidden,active⟩

/-- The source's actual allocation after the Bool operation. Its heap lookup
and storage fields are installed by the entry output, not a fabricated world. -/
def tree : BorrowTree := if out.physical.id=source.backing.id then out.updated.extra else (sourceOutput C).child.tree

private theorem same_current (same : out.physical.id=source.backing.id) :
    ∃ node,out.updated.extra.nodes.get out.child=some node ∧ node.tag=(sourceOutput C).tag ∧
      node.children=#[] ∧ node.isExposed=false ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin out.updated.extra out.child .Write (UInt64.ofNat offset) (UInt64.ofNat offset+len) := by
  let B := CurrentCallSpatialBoolActivation.window out.dst out.physical out.physicalId out.physicalOffset
  have coverEq := (CurrentCallSpatialJointInstall.context source C.positive C.borrowFrame C.fresh
    (UInt64.ofNat offset) len out.entry out.allocation out.child out.models).same_backing
    out.dst.backingAt (CurrentCallSpatialJointInstall.source_member source C.positive C.borrowFrame C.fresh
      (UInt64.ofNat offset) len out.entry out.allocation out.child out.models)
    (out.physicalId.symm.trans same)
  have treeEq : B.allocation.extra=(sourceOutput C).child.tree := by
    change out.dst.backing.allocation.extra=(sourceOutput C).child.tree
    rw [coverEq]
    rfl
  have runtime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra (sourceOutput C).global := by
    rw [treeEq];exact out.sourceRuntime
  have presentPhysical : Present (ActualWorld (CurrentCallSpatialSourceInstall.copiedMachine source C.borrowFrame C.fresh (UInt64.ofNat offset) len out.entry))
      out.physical.id out.physical.entry.allocation := by
    simp only [Present,ActualWorld,Array.toList_map]
    exact List.mem_map.mpr ⟨(out.physical.id,out.physical.entry),Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some out.physical.live),rfl⟩
  have ids : ((ActualWorld (CurrentCallSpatialSourceInstall.copiedMachine source C.borrowFrame C.fresh (UInt64.ofNat offset) len out.entry)).toList.map Prod.fst).Nodup := by
    simpa only [ActualWorld,Array.toList_map,List.map_map,Function.comp_def] using out.sourceTracked.allocationIds
  have allocationEq : out.physical.entry.allocation=B.allocation := CandidateCurrentUniformOwnerWindow.same_id _ ids _ _ _ presentPhysical B.present
  have distinct : B.allocation.extra.roots.toList.Nodup := by
    rw [←allocationEq]
    exact out.sourceTracked.roots _ (Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some out.physical.live))
  have short : B.allocation.extra.nodes.size<65536 := by rw [treeEq];have h:=out.sourceGrowth;have room:=C.sourceRoom;omega
  have bounds : out.physical.offset.toNat+1≤B.allocation.extra.locations.size.bytes.toNat := by
    have first := (B.window (out.physical.id,out.physical.offset.toNat) ⟨rfl,Nat.le_refl _,by omega⟩).1
    rw [B.issued.capability.treeExtent,←B.issued.capability.extent]
    omega
  obtain ⟨qnode,qAt,qTag,qLeaf,qHidden,qActive⟩ := initial out
  have targetAt : B.allocation.extra.nodes.get out.child=some qnode := by rw [treeEq];exact qAt
  have targetActive : GeneralBorrowFreshActiveWithin.ActiveWithin B.allocation.extra out.child .Write (UInt64.ofNat offset) (UInt64.ofNat offset+len) := by rw [treeEq];exact qActive
  have pointerValue : B.pointer.value=ret.family.value := congrArg Family.value out.returnFamily
  have different : out.child≠B.pointer.grant := by
    intro equal
    obtain ⟨node,nodeAt,_,binding⟩ := B.binding
    have actualAt : B.allocation.extra.nodes.get out.child=some node :=
      (congrArg (fun index : UniIndex=>B.allocation.extra.nodes.get index) equal).trans nodeAt
    have nodeEq : node=qnode := Option.some.inj (actualAt.symm.trans targetAt)
    subst node
    cases prov : B.pointer.value.provenance with
    | wildcard =>
      have exposed : qnode.isExposed=true := by simpa only [prov] using binding
      rw [qHidden] at exposed
      cases exposed
    | concrete pointerId pointerTag =>
      have bits : ret.family.value.provenance=.concrete pointerId pointerTag := by rw [←pointerValue];exact prov
      let old := CurrentCallSpatialReturnFrame.returnWindow ret
      obtain ⟨oldNode,oldAt,_,oldBinding⟩ := old.binding
      have oldProvenance : old.pointer.value.provenance=.concrete pointerId pointerTag := bits
      have oldBits : pointerId=old.pointer.allocation ∧ pointerTag=oldNode.tag := by
        simpa only [oldProvenance] using oldBinding
      have newBits : pointerId=B.pointer.allocation ∧ pointerTag=qnode.tag := by simpa only [prov] using binding
      have oldRuntime := (backing_runtime ret.backing C.state C.highwater).1
      have older := GeneralBorrowParentTagInvariant.parent_below_fresh ret.backing.allocation.extra tracker.global oldRuntime old.pointer.grant oldNode oldAt
      have tags : oldNode.tag=tracker.global.nextPointerTag := oldBits.2.symm.trans (newBits.2.trans qTag)
      rw [tags] at older
      exact UInt64.lt_irrefl _ older
  obtain ⟨next,nextAt,nextTag,nextParent,nextChildren,nextHidden,nextActive⟩ := fnentry_frame B runtime (sourceOutput C).frame out.fresh (by rfl)
    distinct short (by omega) out.physical.offset 1 rfl rfl (by decide) bounds out.boolOutput out.boolActual
    out.child qnode targetAt qLeaf qHidden different (UInt64.ofNat offset) (UInt64.ofNat offset+len) targetActive
  obtain ⟨witness⟩ := out.boolWitness
  have childDifferent : out.child≠out.boolChild := by
    intro equal
    have actualAt : out.boolOutput.child.tree.nodes.get out.boolChild=some next :=
      (congrArg (fun index : UniIndex=>out.boolOutput.child.tree.nodes.get index) equal.symm).trans nextAt
    have nodeEq : next=witness.node := Option.some.inj (actualAt.symm.trans witness.nodeAt)
    have tagEq : (sourceOutput C).tag=(sourceOutput C).global.nextPointerTag := qTag.symm.trans (nextTag.symm.trans ((congrArg TreeNode.tag nodeEq).trans (witness.tag.trans out.boolTag)))
    have numeric := congrArg (fun tag : BorTag=>tag.value.toNat) tagEq
    change tracker.global.nextPointerTag.value.toNat=(TypedRetagEmpty.successorTag tracker.global.nextPointerTag C.fresh).value.toNat at numeric
    rw [GenericFunctionEntryNumerics.successor_value] at numeric
    omega
  have afterBounds : out.physical.offset.toNat+1≤out.boolOutput.child.tree.locations.size.bytes.toNat := by rw [witness.capacity];exact bounds
  have active := write_frame out.boolOutput.child.tree out.boolOutput.global _ witness.runtime witness.parents out.boolChild out.child witness.node next witness.nodeAt nextAt
    (nextChildren.trans qLeaf) (nextHidden.trans qHidden) childDifferent out.physical.offset 1 (UInt64.ofNat offset) (UInt64.ofNat offset+len) afterBounds witness.owned nextActive
  have updatedNodes : out.updated.extra.nodes=out.boolOutput.child.tree.nodes := by
    rw [out.updatedExtra]
    exact (GeneralBorrowEffectfulRetagCausalOrder.access_frame _ _ _ _ _ _ _).1
  refine ⟨next,?_,nextTag.trans qTag,nextChildren.trans qLeaf,nextHidden.trans qHidden,?_⟩
  · rw [updatedNodes];exact nextAt
  · rw [out.updatedExtra,←out.boolTag,←witness.tag]
    exact active

/-- Actual q activity and metadata survive the entry Bool Read, constructor,
and Write in both allocation cases. This is not a later q-leaf assumption. -/
theorem current : ∃ node,(tree out).nodes.get out.child=some node ∧ node.tag=(sourceOutput C).tag ∧
    node.children=#[] ∧ node.isExposed=false ∧
    GeneralBorrowFreshActiveWithin.ActiveWithin (tree out) out.child .Write (UInt64.ofNat offset) (UInt64.ofNat offset+len) := by
  by_cases same : out.physical.id=source.backing.id
  · simpa only [tree,ite_eq_left same] using same_current out same
  · simpa only [tree,ite_eq_right same] using initial out

end
end DuplicatePrefix.CurrentCallSpatialEntryActivity
