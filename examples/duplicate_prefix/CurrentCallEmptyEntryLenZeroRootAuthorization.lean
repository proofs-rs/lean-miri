import duplicate_prefix.CurrentCallEmptyEntryLenZeroTransport
import duplicate_prefix.CurrentCallEmptyEntryZeroRootQueries
import duplicate_prefix.S05RawForeignAuthorizationBridge
import duplicate_prefix.GeneralBorrowSharedAuthorizationGeometry
namespace DuplicatePrefix.CurrentCallEmptyEntryLenZeroRootAuthorization
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowProjection GeneralBorrowExposedNonleafPrimaryPath
open GeneralBorrowExposureCardinality DuplicatePrefixResidualSupportAuthorization
open GeneralBorrowFreshGraph GeneralBorrowView
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency true
set_option backward.dsimp.instances false
noncomputable section

private theorem old_node {tree : BorrowTree} {parentTag tag : BorTag}
    (input : EmptyForestSharedPool.Input tree parentTag tag) (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index=some node) :
    ∃ next,input.after.nodes.get index=some next ∧ next.parent=node.parent ∧ next.isExposed=node.isExposed ∧
      next.children=(if index=input.parent then node.children.push input.index else node.children) := by
  let staged := S04ZeroReadSharedAttach.liftNode input.parent input.index index node
  have atStage : input.stage.nodeAt index=some staged := S04ZeroReadSharedAttach.old_lookup tree input.index input.parent
    input.parentNode (GeneralBorrowFreshAnchor.sharedNode tag input.parent) input.vacant input.present index node present
  obtain ⟨next,found,_,parent,children,_,hidden⟩ := GeneralBorrowFreshMetadataChildSifa.node_fields
    input.stage input.parent .Read index staged atStage
  refine ⟨next,found,?_,?_,?_⟩
  · exact parent.trans (by by_cases same : index=input.parent <;> simp [staged,S04ZeroReadSharedAttach.liftNode,same])
  · exact hidden.trans (by by_cases same : index=input.parent <;> simp [staged,S04ZeroReadSharedAttach.liftNode,same])
  · exact children.trans (by by_cases same : index=input.parent <;> simp [staged,S04ZeroReadSharedAttach.liftNode,same])

private theorem new_node {tree : BorrowTree} {parentTag tag : BorTag}
    (input : EmptyForestSharedPool.Input tree parentTag tag) :
    ∃ node,input.after.nodes.get input.index=some node ∧ node.parent=some input.parent ∧
      node.isExposed=false ∧ node.children=#[] := by
  obtain ⟨node,present,_,parent,children,_,hidden⟩ := GeneralBorrowFreshMetadataChildSifa.node_fields
    input.stage input.parent .Read input.index (GeneralBorrowFreshAnchor.sharedNode tag input.parent) input.stage_new
  exact ⟨node,present,parent,hidden,children⟩

/-- Exact current nodes of the REAL q→Shared→len Shared chain. SIFA may
change caches; the actual stored nodes and their child/parent fields are kept. -/
private theorem chain {tree : BorrowTree} {parentTag firstTag secondTag : BorTag}
    (first : EmptyForestSharedPool.Input tree parentTag firstTag)
    (second : EmptyForestSharedPool.Input first.after firstTag secondTag)
    (q : UniIndex) (node : TreeNode) (present : tree.nodes.get q=some node)
    (hidden : node.isExposed=false) (parentless : node.parent=none) (leaf : node.children=#[])
    (firstParent : first.parent=q) (secondParent : second.parent=first.index) :
    ∃ qNode firstNode secondNode,
      second.after.nodes.get q=some qNode ∧ qNode.parent=none ∧ qNode.isExposed=false ∧ qNode.children=#[first.index] ∧
      second.after.nodes.get first.index=some firstNode ∧ firstNode.parent=some q ∧ firstNode.isExposed=false ∧ firstNode.children=#[second.index] ∧
      second.after.nodes.get second.index=some secondNode ∧ secondNode.parent=some first.index ∧ secondNode.isExposed=false ∧ secondNode.children=#[] := by
  have different : q≠first.index := by intro same;rw [same,first.vacant] at present;cases present
  obtain ⟨middleQ,qAt,qParent,qHidden,qChildren⟩ := old_node first q node present
  obtain ⟨middleFirst,firstAt,firstEdge,firstHidden,firstChildren⟩ := new_node first
  obtain ⟨finalQ,finalQAt,finalQParent,finalQHidden,finalQChildren⟩ := old_node second q middleQ qAt
  obtain ⟨finalFirst,finalFirstAt,finalFirstParent,finalFirstHidden,finalFirstChildren⟩ := old_node second first.index middleFirst firstAt
  obtain ⟨finalSecond,finalSecondAt,finalSecondParent,finalSecondHidden,finalSecondChildren⟩ := new_node second
  refine ⟨finalQ,finalFirst,finalSecond,finalQAt,finalQParent.trans (qParent.trans parentless),finalQHidden.trans (qHidden.trans hidden),?_,
    finalFirstAt,?_,finalFirstHidden.trans firstHidden,?_,finalSecondAt,?_,finalSecondHidden,finalSecondChildren⟩
  · rw [finalQChildren,secondParent,ite_eq_right different,qChildren,firstParent,ite_eq_left rfl,leaf]
    rfl
  · exact finalFirstParent.trans (firstEdge.trans (congrArg some firstParent))
  · rw [finalFirstChildren,secondParent,ite_eq_left rfl,firstChildren]
    rfl
  · exact finalSecondParent.trans (congrArg some secondParent)

private theorem path_cases (tree : BorrowTree) (q first second : UniIndex)
    (qNode firstNode secondNode : TreeNode)
    (qAt : tree.nodes.get q=some qNode) (qChildren : qNode.children=#[first])
    (firstAt : tree.nodes.get first=some firstNode) (firstChildren : firstNode.children=#[second])
    (secondAt : tree.nodes.get second=some secondNode) (secondChildren : secondNode.children=#[])
    (reciprocal : Reciprocal tree) (query : UniIndex) (path : Path tree q query) : query=q ∨ query=first ∨ query=second := by
  induction path with
  | refl => exact .inl rfl
  | @step parent child earlier node present edge induction =>
    obtain ⟨parentNode,parentAt,member⟩ := reciprocal child node present parent edge
    rcases induction with same | same | same
    · subst parent
      have equal : parentNode=qNode := Option.some.inj (parentAt.symm.trans qAt)
      rw [equal,qChildren] at member
      exact .inr (.inl (by simpa using member))
    · subst parent
      have equal : parentNode=firstNode := Option.some.inj (parentAt.symm.trans firstAt)
      rw [equal,firstChildren] at member
      exact .inr (.inr (by simpa using member))
    · subst parent
      have equal : parentNode=secondNode := Option.some.inj (parentAt.symm.trans secondAt)
      rw [equal,secondChildren] at member
      cases member

/-- Every ACTUAL q-subtree path after the two helpers ends at q or one
of those helpers. Reciprocity is the current physical graph fact; no old
malformed-graph exclusion is inferred from the constructor inputs alone. -/
theorem qPath_cases {tree : BorrowTree} {parentTag firstTag secondTag : BorTag}
    (first : EmptyForestSharedPool.Input tree parentTag firstTag)
    (second : EmptyForestSharedPool.Input first.after firstTag secondTag)
    (q : UniIndex) (qNode : TreeNode) (qAt : tree.nodes.get q=some qNode)
    (qHidden : qNode.isExposed=false) (qParentless : qNode.parent=none) (qLeaf : qNode.children=#[])
    (firstParent : first.parent=q) (secondParent : second.parent=first.index)
    (reciprocal : Reciprocal second.after) (query : UniIndex) (path : Path second.after q query) :
    query=q ∨ query=first.index ∨ query=second.index := by
  obtain ⟨currentQ,currentFirst,currentSecond,currentQAt,_,_,currentQChildren,
    currentFirstAt,_,_,currentFirstChildren,currentSecondAt,_,_,currentSecondChildren⟩ :=
    chain first second q qNode qAt qHidden qParentless qLeaf firstParent secondParent
  exact path_cases second.after q first.index second.index currentQ currentFirst currentSecond currentQAt currentQChildren
    currentFirstAt currentFirstChildren currentSecondAt currentSecondChildren reciprocal query path

private theorem hidden_count (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (location : LocationTree) (protections : ProtectedTags) (root query : UniIndex)
    (path : Path tree root query)
    (hidden : ∀ index node,tree.nodes.get index=some node → Path tree root index → node.isExposed=false)
    (removed : List UniIndex) : residualCount tree location protections .Write removed query=0 := by
  apply List.length_eq_zero_iff.mpr
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro row member
  obtain ⟨contributed,_⟩ := List.mem_filter.mp member
  obtain ⟨listed,contributed⟩ := List.mem_filter.mp contributed
  have present := (GeneralBorrowFreshReuseProtection.entries_get tree.nodes row.1 row.2).mp listed
  simp only [contributes,Bool.and_eq_true] at contributed
  have walked : query∈GeneralBorrowExposureAncestorFold.walk tree.nodes (tree.nodes.size+1) row.1 :=
    List.contains_iff_mem.mp contributed.2
  have tail := GeneralBorrowWildcardControlWitness.path_of_walk tree depth query row.1 row.2 present _ walked
  have completePath := GeneralBorrowSharedAuthorizationGeometry.path_trans path tail
  have invisible := hidden row.1 row.2 present completePath
  have exposed := contributed.1.1
  rw [invisible] at exposed
  cases exposed

/-- The ACTUAL orphan q→Shared→len subtree supplies its whole repaired
Foreign Write callback, including every finite residual-removal query.
The selected old-root cutoff is retained without an extra order gate. -/
theorem two_helpers_consistent {tree : BorrowTree} {parentTag firstTag secondTag : BorTag}
    (first : EmptyForestSharedPool.Input tree parentTag firstTag)
    (second : EmptyForestSharedPool.Input first.after firstTag secondTag)
    (q : UniIndex) (qNode : TreeNode) (qAt : tree.nodes.get q=some qNode)
    (qHidden : qNode.isExposed=false) (qParentless : qNode.parent=none) (qLeaf : qNode.children=#[])
    (firstParent : first.parent=q) (secondParent : second.parent=first.index)
    (global : GlobalState) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts second.after global)
    (position : Nat) (rootSlot : second.after.roots[position]?=some q) (later : 0<position)
    (maximum : Option BorTag) (location : LocationTree)
    (consistent : ∀ index node,second.after.nodes.get index=some node → Path second.after q index →
      GeneralBorrowSifaPermissionConsistency.Consistent ((location.perms.get index).getD node.defaultLocationState) (global.protectedTags.contains node.tag))
    (foreign : ∀ index node,second.after.nodes.get index=some node → Path second.after q index →
      OrdinaryBorrowAuthority.ForeignWrite (RawState location index node) (global.protectedTags.contains node.tag)) :
    DuplicatePrefixResidualWriteRepaired.Authorization second.after location global.protectedTags q position maximum .Write
      (fun query=>Path second.after q query) ∧
    ∀ removed query node,Path second.after q query → second.after.nodes.get query=some node →
      residualRelation second.after location global.protectedTags q query node maximum .Write position removed=some .ForeignAccess := by
  obtain ⟨currentQ,currentFirst,currentSecond,currentQAt,currentQParent,currentQHidden,currentQChildren,
    currentFirstAt,currentFirstParent,currentFirstHidden,currentFirstChildren,currentSecondAt,currentSecondParent,currentSecondHidden,currentSecondChildren⟩ :=
    chain first second q qNode qAt qHidden qParentless qLeaf firstParent secondParent
  let depth := Classical.choice runtime.formed.depth
  obtain ⟨forest⟩ := runtime.formed.forest location global.protectedTags
  have reciprocal := GeneralBorrowExposedScopedReciprocal.of_forest second.after location global.protectedTags forest depth
  have casesPath (query : UniIndex) (path : Path second.after q query) : query=q ∨ query=first.index ∨ query=second.index :=
    path_cases second.after q first.index second.index currentQ currentFirst currentSecond currentQAt currentQChildren
      currentFirstAt currentFirstChildren currentSecondAt currentSecondChildren reciprocal query path
  have hidden : ∀ index node,second.after.nodes.get index=some node → Path second.after q index → node.isExposed=false := by
    intro index node present path
    rcases casesPath index path with same | same | same
    · subst index
      have equal : node=currentQ := Option.some.inj (present.symm.trans currentQAt)
      exact equal.symm ▸ currentQHidden
    · subst index
      have equal : node=currentFirst := Option.some.inj (present.symm.trans currentFirstAt)
      exact equal.symm ▸ currentFirstHidden
    · subst index
      have equal : node=currentSecond := Option.some.inj (present.symm.trans currentSecondAt)
      exact equal.symm ▸ currentSecondHidden
  have rootPath : Path second.after q q := .refl q currentQ currentQAt
  have firstPath : Path second.after q first.index := .step rootPath currentFirst currentFirstAt currentFirstParent
  have secondPath : Path second.after q second.index := .step firstPath currentSecond currentSecondAt currentSecondParent
  have relation (removed : List UniIndex) (query : UniIndex) (node : TreeNode)
      (path : Path second.after q query) (_present : second.after.nodes.get query=some node) :
      residualRelation second.after location global.protectedTags q query node maximum .Write position removed=some .ForeignAccess := by
    unfold residualRelation
    rw [hidden_count second.after depth location global.protectedTags q q rootPath hidden removed,
      hidden_count second.after depth location global.protectedTags q query path hidden removed]
    apply S04ZeroLeafCallbackData.zero_foreign
    simp [show position≠0 by omega]
  refine ⟨?_,relation⟩
  constructor
  case rooted =>
    obtain ⟨actual,present,_⟩ := runtime.formed.rootNodes q (Array.mem_toList_iff.mpr (Array.mem_of_getElem? rootSlot))
    exact .refl q actual present
  case present => intro index path;exact path.present
  case children =>
    intro index node path present child member
    rcases casesPath index path with same | same | same
    · subst index
      have equal : node=currentQ := Option.some.inj (present.symm.trans currentQAt)
      rw [equal,currentQChildren] at member
      have same : child=first.index := by simpa using member
      exact same.symm ▸ firstPath
    · subst index
      have equal : node=currentFirst := Option.some.inj (present.symm.trans currentFirstAt)
      rw [equal,currentFirstChildren] at member
      have same : child=second.index := by simpa using member
      exact same.symm ▸ secondPath
    · subst index
      have equal : node=currentSecond := Option.some.inj (present.symm.trans currentSecondAt)
      rw [equal,currentSecondChildren] at member
      cases member
  case covers => intro index path;exact GeneralBorrowSharedAuthorizationGeometry.covers_of_path second.after depth q index path
  case possible => intro index node path present;exact (foreign index node present path).1
  case queries =>
    intro before after _ _ _ index node path present _
    rw [relation before index node path present,relation after index node path present]
    exact S05RawForeignAuthorizationBridge.foreign_write_authorized _ _ _ (consistent index node present path) (foreign index node present path)
  case witness => intro impossible;omega


theorem two_helpers {tree : BorrowTree} {parentTag firstTag secondTag : BorTag}
    (first : EmptyForestSharedPool.Input tree parentTag firstTag)
    (second : EmptyForestSharedPool.Input first.after firstTag secondTag)
    (q : UniIndex) (qNode : TreeNode) (qAt : tree.nodes.get q=some qNode)
    (qHidden : qNode.isExposed=false) (qParentless : qNode.parent=none) (qLeaf : qNode.children=#[])
    (firstParent : first.parent=q) (secondParent : second.parent=first.index)
    (global : GlobalState) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts second.after global)
    (position : Nat) (rootSlot : second.after.roots[position]?=some q) (later : 0<position)
    (maximum : Option BorTag) (location : LocationTree)
    (profile : GeneralBorrowLocationSifaConsistency.Profile second.after location global.protectedTags)
    (foreign : ∀ index node,second.after.nodes.get index=some node → Path second.after q index →
      OrdinaryBorrowAuthority.ForeignWrite (RawState location index node) (global.protectedTags.contains node.tag)) :
    DuplicatePrefixResidualWriteRepaired.Authorization second.after location global.protectedTags q position maximum .Write
      (fun query=>Path second.after q query) ∧
    ∀ removed query node,Path second.after q query → second.after.nodes.get query=some node →
      residualRelation second.after location global.protectedTags q query node maximum .Write position removed=some .ForeignAccess := by
  exact two_helpers_consistent first second q qNode qAt qHidden qParentless qLeaf firstParent secondParent global runtime position rootSlot later maximum location
    (fun index node present _ => profile.present index node present) foreign


end
end DuplicatePrefix.CurrentCallEmptyEntryLenZeroRootAuthorization

open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallEmptyEntryLenZeroRootAuthorization" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual len-zero-root authorization dependency {dependency}"
