import duplicate_prefix.GeneralBorrowExposedScopedInactiveLeafSeed
import duplicate_prefix.GeneralBorrowExposedInactiveConstructor
import duplicate_prefix.GeneralBorrowExposedConstructorUnique
import duplicate_prefix.GeneralBorrowExposedScopedSharedConstructor
import duplicate_prefix.GeneralBorrowExposedScopedChildComponent
import duplicate_prefix.GeneralBorrowExposedScopedSharedFlags
import duplicate_prefix.GeneralBorrowExposedScopedSharedOld
import duplicate_prefix.GeneralBorrowSharedConstructorExposureCache
import duplicate_prefix.GeneralBorrowFreshMetadataChildOld
import duplicate_prefix.GeneralBorrowFreshSharedPaths
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveSharedConstructor
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open GeneralBorrowFreshMetadataChildShared
open GeneralBorrowExposedKnownRootState (Scope)
open GeneralBorrowExposedScopedMixedShape (Mixed)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Graph and initial stored-row resources of one exposed-leaf family. The
selected component may retain exposed Unique ancestors and an arbitrary shared/mutable history. -/
structure Resources (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (writable : Nat → Bool) where
  forest : GeneralBorrowForest.Forest (source_normal_projection input.tree default protections).topology
  component : GeneralBorrowExposedScopedNormal.Component (source_normal_projection input.tree default protections).topology input.parent.toNat
  selectedNode : TreeNode
  selectedPresent : input.tree.nodeAt selected = some selectedNode
  roots : input.tree.roots = (head::tail).toArray
  rootPath : ((source_normal_projection input.tree default protections).topology.ancestorPath input.parent.toNat).getLast! = selected.toNat
  exposures : GeneralRangeMapState.Every (fun location => GeneralBorrowExposedInactiveConstructor.Profile input.tree location input.parent component.support) input.tree.locations
  separate : ∀ index,area.support index → ¬component.support index.toNat
  tags : ∀ index node,area.support index → input.tree.nodeAt index = some node → node.tag.value ≤ selectedNode.tag.value
  leaves : ∀ index,area.support index → ∃ node,input.tree.nodeAt index = some node ∧ node.children = #[] ∧ node.isExposed = true
  unique : ∀ index,area.support index → GeneralBorrowSifaUniqueFrame.UniqueAt input.tree index
  first : head ≠ selected → area.support head
  rest : ∀ root ∈ tail,root ≠ selected → area.support root
  coherent : GeneralRangeMapState.Every (fun location => GeneralBorrowExposureCardinality.LocationCoherent input.tree location protections) input.tree.locations
  owned : GeneralRangeMapOrigins.OwnedOn (Mixed input.tree protections input.parent component.support writable)
    input.offset (input.offset+input.len) input.tree.locations
  room : input.tree.nodes.size+1 < 65536

/-- The actual shared constructor forms complete child Read inputs, including
its exposed ancestor profile, selected root, exposed old leaves, exact counters and
mixed ownership. All resources refer to the initial tree; no poststate
coherence, ownership or operation-success premise is accepted. -/
theorem construct (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (writable : Nat → Bool) (raw : Resources input protections selected head tail writable) :
    let child := result input
    let support := fun position => raw.component.support position ∨ position = (index input).toNat
    (input.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshAnchor.sharedState) .Frozen input.isProtected).outcome = .ok () ∧
    ∃ context : GeneralBorrowExposedKnownRootRangeData.Context child (index input) selected head tail,
      GeneralRangeMapOrigins.OwnedOn (fun location => Nonempty (GeneralBorrowExposedScopedInactiveRangeData.Data child location protections
        (index input) selected head tail support))
        input.offset (input.offset+input.len) child.locations := by
  let metadata := GeneralBorrowFreshMetadataChildShared.append input
  let child := result input
  have oldSize : (source_normal_projection input.tree default protections).topology.nodes.size = (index input).toNat := by
    rw [at_end input]
    unfold_general_projection
    unfold_general_topology
    simp only [Array.size_map]
  let extension := metadata.extension default default protections
  let newRaw := GeneralBorrowExposedScopedChildComponent.append _ _ input.parent.toNat extension raw.component
  let component : GeneralBorrowExposedScopedNormal.Component (source_normal_projection child default protections).topology (index input).toNat := {
    support := fun position => raw.component.support position ∨ position = (index input).toNat
    anchor := Or.inr rfl
    parents := by simpa only [newRaw,GeneralBorrowExposedScopedChildComponent.append,oldSize] using newRaw.parents
    children := by simpa only [newRaw,GeneralBorrowExposedScopedChildComponent.append,oldSize] using newRaw.children }
  have forest := GeneralBorrowFreshTopology.extended_forest _ _ input.parent.toNat extension raw.forest
  have separate : ∀ query,area.support query → ¬component.support query.toNat := by
    intro query included supported
    rcases supported with old | fresh
    · exact raw.separate query included old
    · obtain ⟨node,present,_,_⟩ := raw.leaves query included
      have bounded := GeneralBorrowNodeUpdate.lookup_valid input.tree.nodes query node present
      rw [fresh,at_end input] at bounded
      omega
  have exposures := GeneralBorrowExposedInactiveConstructor.shared input raw.component.support raw.forest raw.exposures
  obtain ⟨newNode,newPresent,newTag,newParent,newChildren,newPermission,newHidden⟩ := metadata.newNode
  obtain ⟨selectedNode,selectedPresent,selectedTag,selectedFlag⟩ := GeneralBorrowFreshMetadataChildOld.append input selected raw.selectedNode raw.selectedPresent
  have other : ∀ query,area.support query → ∃ old next,input.tree.nodeAt query = some old ∧ child.nodeAt query = some next ∧
      next.tag = old.tag ∧ next.children = #[] ∧ next.isExposed = true := by
    intro query included
    obtain ⟨old,present,leaf,exposed⟩ := raw.leaves query included
    have different : query ≠ input.parent := by
      intro same
      subst query
      exact raw.separate input.parent included raw.component.anchor
    obtain ⟨next,found,tag,parent,children,permission,flag⟩ := GeneralBorrowExposedScopedSharedOld.outside_parent input query old present different
    exact ⟨old,next,present,found,tag,children.trans leaf,flag.trans exposed⟩
  let context : GeneralBorrowExposedKnownRootRangeData.Context child (index input) selected head tail := {
    anchorNode := newNode
    selectedNode := selectedNode
    anchorPresent := newPresent
    selectedPresent := selectedPresent
    roots := metadata.roots.trans raw.roots
    depth := metadata.certificates.depth
    children := metadata.certificates.children
    tags := by
      intro query node included present
      obtain ⟨old,next,oldPresent,found,tag,leaf,exposed⟩ := other query included
      have same := Option.some.inj (found.symm.trans present)
      subst node
      rw [tag,selectedTag]
      exact raw.tags query old included oldPresent }
  have rootPath : ((source_normal_projection child default protections).topology.ancestorPath (index input).toNat).getLast! = selected.toNat := by
    have path := (GeneralBorrowFreshSharedPaths.of_append _ _ input.parent.toNat extension raw.forest).childPath
    rw [oldSize] at path
    rw [path]
    have nonempty : (source_normal_projection input.tree default protections).topology.ancestorPath input.parent.toNat ≠ [] := by
      intro empty
      have member := GeneralBorrowFreshSharedPaths.ancestor_self (source_normal_projection input.tree default protections).topology input.parent.toNat
      rw [empty] at member
      cases member
    simpa only [List.getLast!_eq_getLast?_getD,List.getLast?_cons_of_ne_nil nonempty] using raw.rootPath
  have cache := GeneralBorrowSharedConstructorExposureCache.append input protections raw.coherent
  have mixed := GeneralBorrowExposedScopedSharedConstructor.append_owned input.tree input.depth input.parentTag input.newTag input.parent input.parentNode
    input.parentTagPresent input.parentPresent input.fresh input.noFree input.aligned input.fits input.isProtected input.offset input.len input.nonzero
    input.well input.bounds protections raw.component.support writable raw.forest raw.owned
  have short : child.nodes.size < 65536 := by rw [metadata.size];exact raw.room
  refine ⟨metadata.success,context,?_⟩
  intro position valid positive lower upper
  let location := (child.locations.entries[position]'valid).data
  have coherent := cache.2 position valid
  have mixedHere := mixed.2 position valid positive lower upper
  have leaves : ∀ query,area.support query → ∃ node,child.nodes.get query = some node ∧ node.children = #[] ∧ node.isExposed = true ∧
      GeneralBorrowExposureCardinality.supports (GeneralBorrowExposureCardinality.effective location protections query node) .Read = true ∧
      (GeneralBorrowWildcardVirtualLeaf.effective location query node).possible = true := by
    intro query included
    obtain ⟨old,next,oldPresent,found,tag,leaf,exposed⟩ := other query included
    have unique := GeneralBorrowExposedScopedSharedOld.unique input query old oldPresent (raw.unique query included)
    have stored := unique position valid
    change location.perms.get query = some GeneralBorrowWildcardLeaf.unique at stored
    refine ⟨next,found,leaf,exposed,?_,?_⟩
    · simp only [GeneralBorrowExposureCardinality.effective,stored,Option.getD_some,GeneralBorrowWildcardLeaf.unique,
        Permission.strongestAllowedLocalAccess,GeneralBorrowExposureCardinality.supports,GeneralBorrowExposureAncestorFold.supportsRead]
    · simp only [GeneralBorrowWildcardVirtualLeaf.effective,stored,Option.getD_some,GeneralBorrowWildcardLeaf.unique,LocationState.possible,Bool.true_or]
  have ancestors : ∀ query node state,component.support query.toNat → child.nodeAt query=some node → node.isExposed=true →
      child.locationStateAt location query=some state →
      (query.toNat ∈ (source_normal_projection child location protections).topology.ancestorPath (index input).toNat ∧ state.permission=.Unique) ∨
      (query.toNat ∉ (source_normal_projection child location protections).topology.ancestorPath (index input).toNat ∧ state.permission=.Disabled) := by
    intro query node state member present exposed statePresent
    have included : GeneralBorrowExposedConstructorAncestry.extended raw.component.support (index input) query.toNat := by
      rcases member with old | fresh
      · exact Or.inr old
      · exact Or.inl fresh
    have stateEq : ((location.perms.get query).getD node.defaultLocationState)=state := by
      simpa only [BorrowTree.locationStateAt,present,bind,pure,Option.bind_some,Option.some.injEq] using statePresent
    have current := exposures position valid query node included present exposed
    rw [stateEq] at current
    exact current
  exact ⟨GeneralBorrowExposedScopedInactiveLeafSeed.seed child location protections (index input) selected head tail component.support
    (GeneralBorrowFreshMixedChild.extend writable (index input).toNat) context forest component rfl mixedHere rootPath ancestors separate coherent short leaves raw.first raw.rest⟩
end DuplicatePrefix.GeneralBorrowExposedScopedInactiveSharedConstructor
