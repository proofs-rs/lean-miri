import duplicate_prefix.S05CutoffOwnershipGeometry
import duplicate_prefix.S05WriteCacheContributorOwnership
import duplicate_prefix.BoolDestinationWriteOnlyAdapter

namespace DuplicatePrefix.S05RetainedConeOwnership
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowExposureAncestorFold GeneralBorrowExposureCardinality GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowWildcardParentTagOrder
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization DuplicatePrefixCallbackVisitAuthorization
open S05CutoffOwnershipGeometry S05WriteCacheContributorOwnership
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- An actual cutoff-eligible exposed Write contributor below a query.
It is retained by every legal mask, independent of traversal or success. -/
def RetainedBelow (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (maximum : Option BorTag) (query : UniIndex) : Prop :=
  ∃ witness node, tree.nodes.get witness = some node ∧
    Supports location protections witness node maximum .Write ∧ Path tree query witness

/-- Raw ownership with foreign rights only at clamped queries or cones lacking
an eligible retained supporter. Local permission requirements are unchanged.
No callback classification, removal mask or successful operation is a field. -/
structure Ownership (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) where
  area : GeneralBorrowWildcardControlStack.Support tree root
  covers : ∀ query, area.contains query → Covers tree.nodes root query
  possible : ∀ query node, area.contains query → tree.nodes.get query = some node →
    ((location.perms.get query).getD node.defaultLocationState).possible = true
  foreign : ∀ query node, area.contains query → tree.nodes.get query = some node →
    (aboveMaximum node maximum = true ∨ ¬ RetainedBelow tree location protections maximum query) →
    DuplicatePrefixScalarAuthorization.Compatible
      ((location.perms.get query).getD node.defaultLocationState) .Write .ForeignAccess (protections.contains node.tag)
  localRights : ∀ query node, area.contains query → tree.nodes.get query = some node →
    ∀ witness witnessNode,tree.nodes.get witness = some witnessNode → witnessNode.isExposed = true →
      query ∈ walk tree.nodes (tree.nodes.size+1) witness → ∀ kind,
      supports (effective location protections witness witnessNode) kind = true →
      DuplicatePrefixScalarAuthorization.Compatible
        ((location.perms.get query).getD node.defaultLocationState) kind .LocalAccess (protections.contains node.tag)
  cutoff : CutoffWitness tree location protections root position maximum area.contains

/-- Generalized formation removes only the conflicted protected reservation
ban from virtual-component Write ancestry. Both access kinds retain all other
local scalar clauses; Disabled/Frozen Write barriers remain excluded.
This is not a definition of ordinary reference validity. -/
structure GeneralizedOwnership (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) where
  area : GeneralBorrowWildcardControlStack.Support tree root
  covers : ∀ query, area.contains query → Covers tree.nodes root query
  possible : ∀ query node, area.contains query → tree.nodes.get query = some node →
    ((location.perms.get query).getD node.defaultLocationState).possible = true
  foreign : ∀ query node, area.contains query → tree.nodes.get query = some node →
    (aboveMaximum node maximum = true ∨ ¬ RetainedBelow tree location protections maximum query) →
    DuplicatePrefixScalarAuthorization.Compatible
      ((location.perms.get query).getD node.defaultLocationState) .Write .ForeignAccess (protections.contains node.tag)
  primaryLocal : position = 0 → ∀ query node, area.contains query → tree.nodes.get query = some node →
    ∀ witness witnessNode,tree.nodes.get witness = some witnessNode → witnessNode.isExposed = true →
      query ∈ walk tree.nodes (tree.nodes.size+1) witness → ∀ kind,
      supports (effective location protections witness witnessNode) kind = true →
      DuplicatePrefixScalarAuthorization.Compatible
        ((location.perms.get query).getD node.defaultLocationState) kind .LocalAccess (protections.contains node.tag)
  virtualLive : position ≠ 0 → ∀ query node, area.contains query → tree.nodes.get query = some node →
    ∀ witness witnessNode, tree.nodes.get witness = some witnessNode → witnessNode.isExposed = true →
      query ∈ walk tree.nodes (tree.nodes.size+1) witness → ∀ kind,
      supports (effective location protections witness witnessNode) kind = true →
      DuplicatePrefixScalarAuthorization.Compatible
        ((location.perms.get query).getD node.defaultLocationState) kind .LocalAccess false
  cutoff : CutoffWitness tree location protections root position maximum area.contains

/-- Compatibility packet retained unchanged. The fieldless formation core below
needs only the Write part of primaryLocal; its Read part is not required for
Row/Positive formation. This is not ordinary-validity coverage. -/
structure CallbackOwnership (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) where
  area : GeneralBorrowWildcardControlStack.Support tree root
  covers : ∀ query, area.contains query → Covers tree.nodes root query
  possible : ∀ query node, area.contains query → tree.nodes.get query = some node →
    ((location.perms.get query).getD node.defaultLocationState).possible = true
  foreign : ∀ query node, area.contains query → tree.nodes.get query = some node →
    (aboveMaximum node maximum = true ∨ ¬ RetainedBelow tree location protections maximum query) →
    DuplicatePrefixScalarAuthorization.Compatible
      ((location.perms.get query).getD node.defaultLocationState) .Write .ForeignAccess (protections.contains node.tag)
  primaryLocal : position = 0 → ∀ query node, area.contains query → tree.nodes.get query = some node →
    ∀ witness witnessNode,tree.nodes.get witness = some witnessNode → witnessNode.isExposed = true →
      query ∈ walk tree.nodes (tree.nodes.size+1) witness → ∀ kind,
      supports (effective location protections witness witnessNode) kind = true →
      DuplicatePrefixScalarAuthorization.Compatible
        ((location.perms.get query).getD node.defaultLocationState) kind .LocalAccess (protections.contains node.tag)
  virtualWriteLive : position ≠ 0 → ∀ query node, area.contains query → tree.nodes.get query = some node →
    ∀ witness witnessNode, tree.nodes.get witness = some witnessNode → witnessNode.isExposed = true →
      query ∈ walk tree.nodes (tree.nodes.size+1) witness →
      supports (effective location protections witness witnessNode) .Write = true →
      ((location.perms.get query).getD node.defaultLocationState).permission ≠ .Disabled ∧
      ((location.perms.get query).getD node.defaultLocationState).permission ≠ .Frozen
  cutoff : CutoffWitness tree location protections root position maximum area.contains

def Ownership.toCallbackOwnership {tree : BorrowTree} {location : LocationTree} {protections : ProtectedTags}
    {root : UniIndex} {position : Nat} {maximum : Option BorTag}
    (rights : Ownership tree location protections root position maximum) :
    CallbackOwnership tree location protections root position maximum := {
  area := rights.area, covers := rights.covers, possible := rights.possible,
  foreign := rights.foreign, cutoff := rights.cutoff,
  primaryLocal := fun _ => rights.localRights,
  virtualWriteLive := by
    intro _ query node inside present witness witnessNode found exposed walked supported
    have scalar := rights.localRights query node inside present witness witnessNode found exposed walked .Write supported
    exact ⟨scalar.2.1,scalar.2.2.1⟩ }

def GeneralizedOwnership.toCallbackOwnership {tree : BorrowTree} {location : LocationTree} {protections : ProtectedTags}
    {root : UniIndex} {position : Nat} {maximum : Option BorTag}
    (rights : GeneralizedOwnership tree location protections root position maximum) :
    CallbackOwnership tree location protections root position maximum := {
  area := rights.area, covers := rights.covers, possible := rights.possible,
  foreign := rights.foreign, cutoff := rights.cutoff, primaryLocal := rights.primaryLocal,
  virtualWriteLive := by
    intro virtual query node inside present witness witnessNode found exposed walked supported
    have scalar := rights.virtualLive virtual query node inside present witness witnessNode found exposed walked .Write supported
    exact ⟨scalar.2.1,scalar.2.2.1⟩ }

/-- Every previous ownership packet supplies the generalized formation data. -/
def Ownership.generalize {tree : BorrowTree} {location : LocationTree} {protections : ProtectedTags}
    {root : UniIndex} {position : Nat} {maximum : Option BorTag}
    (rights : Ownership tree location protections root position maximum) :
    GeneralizedOwnership tree location protections root position maximum := {
  area := rights.area, covers := rights.covers, possible := rights.possible,
  foreign := rights.foreign, cutoff := rights.cutoff,
  primaryLocal := fun _ => rights.localRights,
  virtualLive := by
    intro _ query node inside present witness witnessNode found exposed walked kind supported
    have localPerm := rights.localRights query node inside present witness witnessNode found exposed walked kind supported
    cases kind with
    | Read => exact localPerm
    | Write => exact ⟨localPerm.1,localPerm.2.1,localPerm.2.2.1,by intro impossible; cases impossible⟩ }

/-- The numeric adapter needs exactly these two live-cone barriers. -/
theorem CallbackOwnership.liveRights {tree : BorrowTree} {location : LocationTree} {protections : ProtectedTags}
    {root : UniIndex} {position : Nat} {maximum : Option BorTag}
    (rights : CallbackOwnership tree location protections root position maximum)
    (query : UniIndex) (node : TreeNode) (inside : rights.area.contains query)
    (present : tree.nodes.get query = some node) (witness : UniIndex) (witnessNode : TreeNode)
    (found : tree.nodes.get witness = some witnessNode) (exposed : witnessNode.isExposed = true)
    (walked : query ∈ walk tree.nodes (tree.nodes.size+1) witness)
    (supported : supports (effective location protections witness witnessNode) .Write = true) :
    ((location.perms.get query).getD node.defaultLocationState).permission ≠ .Disabled ∧
    ((location.perms.get query).getD node.defaultLocationState).permission ≠ .Frozen := by
  by_cases primary : position = 0
  · have localPerm :=  rights.primaryLocal primary query node inside present witness witnessNode found exposed walked .Write supported
    exact ⟨localPerm.2.1,localPerm.2.2.1⟩
  · exact rights.virtualWriteLive primary query node inside present witness witnessNode found exposed walked supported

theorem GeneralizedOwnership.liveRights {tree : BorrowTree} {location : LocationTree} {protections : ProtectedTags}
    {root : UniIndex} {position : Nat} {maximum : Option BorTag}
    (rights : GeneralizedOwnership tree location protections root position maximum)
    (query : UniIndex) (node : TreeNode) (inside : rights.area.contains query)
    (present : tree.nodes.get query = some node) (witness : UniIndex) (witnessNode : TreeNode)
    (found : tree.nodes.get witness = some witnessNode) (exposed : witnessNode.isExposed = true)
    (walked : query ∈ walk tree.nodes (tree.nodes.size+1) witness)
    (supported : supports (effective location protections witness witnessNode) .Write = true) :
    ((location.perms.get query).getD node.defaultLocationState).permission ≠ .Disabled ∧
    ((location.perms.get query).getD node.defaultLocationState).permission ≠ .Frozen := by
  exact rights.toCallbackOwnership.liveRights query node inside present witness witnessNode found exposed walked supported

private theorem unclamped_some (rootCount localCount : Nat) (virtual : Bool)
    (positive : 0 < rootCount + if virtual then 1 else 0) :
    classify rootCount localCount virtual false ≠ none := by
  cases virtual <;> by_cases rootZero : rootCount = 0 <;> by_cases same : rootCount = localCount <;>
    by_cases plusSame : rootCount+1 = localCount <;> by_cases localZero : localCount = 0 <;>
    simp_all [classify]

private theorem local_positive (rootCount localCount : Nat) (virtual foreign : Bool)
    (classified : classify rootCount localCount virtual foreign = some .LocalAccess) : 0 < localCount := by
  cases foreign <;> cases virtual <;> by_cases rootZero : rootCount = 0 <;> by_cases same : rootCount = localCount <;>
    by_cases plusSame : rootCount+1 = localCount <;> by_cases localZero : localCount = 0 <;>
    simp_all [classify] <;> omega

private theorem foreign_zero (rootCount localCount : Nat) (virtual : Bool)
    (classified : classify rootCount localCount virtual false = some .ForeignAccess) : localCount = 0 := by
  cases virtual <;> by_cases rootZero : rootCount = 0 <;> by_cases same : rootCount = localCount <;>
    by_cases plusSame : rootCount+1 = localCount <;> by_cases localZero : localCount = 0 <;>
    simp_all [classify]

private theorem zero_foreign (rootCount : Nat) (virtual : Bool)
    (positive : 0 < rootCount + if virtual then 1 else 0) :
    classify rootCount 0 virtual false = some .ForeignAccess := by
  cases virtual <;> by_cases rootZero : rootCount = 0 <;> simp_all [classify]

private theorem total_positive (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag)
    (area : GeneralBorrowWildcardControlStack.Support tree root)
    (covers : ∀ query, area.contains query → Covers tree.nodes root query)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (witness : CutoffWitness tree location protections root position maximum area.contains)
    (kind : AccessKind) (removed : List UniIndex) (legal : Removal tree location protections maximum kind removed) :
    0 < residualCount tree location protections kind removed root + if position != 0 then 1 else 0 := by
  by_cases primary : position = 0
  · obtain ⟨index,node,inside,present,eligible⟩ := witness_kind tree location protections root position maximum area.contains witness kind primary
    have path := GeneralBorrowWildcardControlWitness.path_of_covers tree depth root index node present (covers index inside)
    have positive := GeneralBorrowResidualPrimaryWitness.positive tree location protections depth maximum kind removed legal root index node present eligible path
    simpa only [primary,bne_self_eq_false,Bool.false_eq_true,ite_false,Nat.add_zero] using positive
  · simp only [show (position != 0) = true by simp [primary],ite_true]
    omega

private theorem clamped_gap (rootCount localCount : Nat) (virtual : Bool)
    (gap : localCount < rootCount + if virtual then 1 else 0) :
    classify rootCount localCount virtual true = some .ForeignAccess := by
  cases virtual <;> by_cases rootZero : rootCount = 0 <;> by_cases same : rootCount = localCount <;>
    by_cases plusSame : rootCount+1 = localCount <;> by_cases localZero : localCount = 0 <;>
    simp_all [classify] <;> omega

/-- Cutoff-eligible primary ownership and parent-tag order rule out clamped
absent relations without using Authorization itself. This is the geometric
half of the concrete residual-pair bridge. -/
private theorem clamped_foreign (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag)
    (area : GeneralBorrowWildcardControlStack.Support tree root)
    (covers : ∀ query, area.contains query → Covers tree.nodes root query)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (witness : CutoffWitness tree location protections root position maximum area.contains)
    (query : UniIndex) (node : TreeNode) (inside : area.contains query) (present : tree.nodes.get query = some node)
    (above : aboveMaximum node maximum = true)
    (kind : AccessKind) (removed : List UniIndex) (legal : Removal tree location protections maximum kind removed) :
    residualRelation tree location protections root query node maximum kind position removed = some .ForeignAccess := by
  have bound : residualCount tree location protections kind removed query ≤ residualCount tree location protections kind removed root := by
    rw [DuplicatePrefixResidualCountModel.count_as_cardinality,DuplicatePrefixResidualCountModel.count_as_cardinality]
    exact cardinality_dominates _ _ _ _ kind (covers query inside)
  have gap : residualCount tree location protections kind removed query <
      residualCount tree location protections kind removed root + if position != 0 then 1 else 0 := by
    by_cases primary : position = 0
    · obtain ⟨index,witnessNode,included,found,eligible⟩ := witness_kind tree location protections root position maximum area.contains witness kind primary
      have path := GeneralBorrowWildcardControlWitness.path_of_covers tree depth root index witnessNode found (covers index included)
      have outside : query ∉ walk tree.nodes (tree.nodes.size+1) index := by
        intro walked
        have localPath := GeneralBorrowWildcardControlWitness.path_of_walk tree depth query index witnessNode found _ walked
        have notAbove := path_not_above tree order location protections maximum kind query index node witnessNode present found localPath eligible
        rw [above] at notAbove
        cases notAbove
      have strict := residual_strict tree location protections depth root query index witnessNode found maximum kind removed legal eligible path outside (covers query inside)
      simpa only [primary,bne_self_eq_false,Bool.false_eq_true,ite_false,Nat.add_zero] using strict
    · simp only [show (position != 0) = true by simp [primary],ite_true]
      omega
  simpa only [residualRelation,above] using clamped_gap _ _ _ gap


private theorem relation_present (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag)
    (area : GeneralBorrowWildcardControlStack.Support tree root)
    (covers : ∀ query, area.contains query → Covers tree.nodes root query)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (witness : CutoffWitness tree location protections root position maximum area.contains)
    (query : UniIndex) (node : TreeNode) (inside : area.contains query) (present : tree.nodes.get query = some node)
    (kind : AccessKind) (removed : List UniIndex) (legal : Removal tree location protections maximum kind removed) :
    residualRelation tree location protections root query node maximum kind position removed ≠ none := by
  cases above : aboveMaximum node maximum with
  | true => rw [clamped_foreign tree location protections root position maximum area covers depth order witness query node inside present above kind removed legal];simp
  | false =>
    simpa only [residualRelation,above] using unclamped_some
      (residualCount tree location protections kind removed root) (residualCount tree location protections kind removed query)
      (position != 0) (total_positive tree location protections root position maximum area covers depth witness kind removed legal)

private theorem local_of_count (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (_maximum : Option BorTag) (area : GeneralBorrowWildcardControlStack.Support tree root)
    (_covers : ∀ query, area.contains query → Covers tree.nodes root query)
    (primaryWrite : position = 0 → ∀ query node, area.contains query → tree.nodes.get query = some node →
      ∀ witness witnessNode, tree.nodes.get witness = some witnessNode → witnessNode.isExposed = true →
      query ∈ walk tree.nodes (tree.nodes.size+1) witness →
      supports (effective location protections witness witnessNode) .Write = true →
      DuplicatePrefixScalarAuthorization.Compatible
        ((location.perms.get query).getD node.defaultLocationState) .Write .LocalAccess (protections.contains node.tag))
    (query : UniIndex) (node : TreeNode) (inside : area.contains query)
    (present : tree.nodes.get query = some node)
    (primary : position = 0)
    (positive : 0 < cardinality tree.nodes (effective location protections) query .Write) :
    DuplicatePrefixScalarAuthorization.Compatible
      ((location.perms.get query).getD node.defaultLocationState) .Write .LocalAccess (protections.contains node.tag) := by
  have member : ∃ row,row ∈ tree.nodes.entries.toList.filter
      (contributes tree.nodes (effective location protections) query .Write) := by
    cases rows : tree.nodes.entries.toList.filter (contributes tree.nodes (effective location protections) query .Write) with
    | nil => simp only [cardinality,rows,List.length_nil,Nat.lt_irrefl] at positive
    | cons row rest => exact ⟨row,by simp⟩
  obtain ⟨⟨witness,witnessNode⟩,member⟩ := member
  obtain ⟨entry,contributing⟩ := List.mem_filter.mp member
  have found := (GeneralBorrowFreshReuseProtection.entries_get tree.nodes witness witnessNode).mp entry
  simp only [contributes,Bool.and_eq_true,List.contains_iff_mem] at contributing
  exact primaryWrite primary query node inside present witness witnessNode found contributing.1.1 contributing.2 contributing.1.2


private theorem local_compatible (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag)
    (area : GeneralBorrowWildcardControlStack.Support tree root)
    (covers : ∀ query, area.contains query → Covers tree.nodes root query)
    (primaryWrite : position = 0 → ∀ query node, area.contains query → tree.nodes.get query = some node →
      ∀ witness witnessNode, tree.nodes.get witness = some witnessNode → witnessNode.isExposed = true →
      query ∈ walk tree.nodes (tree.nodes.size+1) witness →
      supports (effective location protections witness witnessNode) .Write = true →
      DuplicatePrefixScalarAuthorization.Compatible
        ((location.perms.get query).getD node.defaultLocationState) .Write .LocalAccess (protections.contains node.tag))
    (query : UniIndex) (node : TreeNode) (inside : area.contains query) (present : tree.nodes.get query = some node)
    (removed : List UniIndex)
    (classified : residualRelation tree location protections root query node maximum .Write position removed = some .LocalAccess) :
    DuplicatePrefixScalarAuthorization.Compatible
      ((location.perms.get query).getD node.defaultLocationState) .Write .LocalAccess (protections.contains node.tag) := by
  have primary : position = 0 := by
    by_cases virtual : position = 0
    · exact virtual
    · apply False.elim
      have dominated : residualCount tree location protections .Write removed query ≤
          residualCount tree location protections .Write removed root := by
        rw [DuplicatePrefixResidualCountModel.count_as_cardinality,DuplicatePrefixResidualCountModel.count_as_cardinality]
        exact GeneralBorrowExposureCardinality.cardinality_dominates _ _ _ _ .Write (covers query inside)
      have classifiedVirtual := DuplicatePrefixResidualWriteSkip.classify_virtual
        (residualCount tree location protections .Write removed root)
        (residualCount tree location protections .Write removed query) (aboveMaximum node maximum) dominated
      have same : (position != 0) = true := by simp [virtual]
      simp only [residualRelation,same] at classified
      rw [classifiedVirtual] at classified
      split at classified <;> cases classified
  have positive := local_positive _ _ _ _ classified
  have bound : residualCount tree location protections .Write removed query ≤
      cardinality tree.nodes (effective location protections) query .Write := List.length_filter_le _ _
  exact local_of_count tree location protections root position maximum area covers primaryWrite query node inside present primary (by omega)

/-- A Foreign exit cannot occur in an unclamped retained cone. -/
private theorem foreign_compatible (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag)
    (area : GeneralBorrowWildcardControlStack.Support tree root)
    (foreign : ∀ query node, area.contains query → tree.nodes.get query = some node →
      (aboveMaximum node maximum = true ∨ ¬ RetainedBelow tree location protections maximum query) →
      DuplicatePrefixScalarAuthorization.Compatible
        ((location.perms.get query).getD node.defaultLocationState) .Write .ForeignAccess (protections.contains node.tag))
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (query : UniIndex) (node : TreeNode) (inside : area.contains query) (present : tree.nodes.get query = some node)
    (removed : List UniIndex) (legal : Removal tree location protections maximum .Write removed)
    (classified : residualRelation tree location protections root query node maximum .Write position removed = some .ForeignAccess) :
    DuplicatePrefixScalarAuthorization.Compatible
      ((location.perms.get query).getD node.defaultLocationState) .Write .ForeignAccess (protections.contains node.tag) := by
  apply foreign query node inside present
  cases above : aboveMaximum node maximum with
  | true => exact Or.inl rfl
  | false =>
    apply Or.inr
    intro retained
    obtain ⟨witness,witnessNode,found,eligible,path⟩ := retained
    have positive := GeneralBorrowResidualPrimaryWitness.positive tree location protections depth maximum .Write removed legal
      query witness witnessNode found eligible path
    have zero := foreign_zero _ _ _ (by simpa only [residualRelation,above] using classified)
    omega

/-- Canonical fieldless Write formation. No primary Read ancestry is assumed.
Conservative removal pairs use the existing cutoff and skip-stability facts;
no Row, Authorization, operation outcome or NoUB is assumed. -/
theorem write_authorization_of_fields (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag)
    (area : GeneralBorrowWildcardControlStack.Support tree root)
    (covers : ∀ query, area.contains query → Covers tree.nodes root query)
    (possible : ∀ query node, area.contains query → tree.nodes.get query = some node →
      ((location.perms.get query).getD node.defaultLocationState).possible = true)
    (foreign : ∀ query node, area.contains query → tree.nodes.get query = some node →
      (aboveMaximum node maximum = true ∨ ¬ RetainedBelow tree location protections maximum query) →
      DuplicatePrefixScalarAuthorization.Compatible
        ((location.perms.get query).getD node.defaultLocationState) .Write .ForeignAccess (protections.contains node.tag))
    (primaryWrite : position = 0 → ∀ query node, area.contains query → tree.nodes.get query = some node →
      ∀ witness witnessNode, tree.nodes.get witness = some witnessNode → witnessNode.isExposed = true →
      query ∈ walk tree.nodes (tree.nodes.size+1) witness →
      supports (effective location protections witness witnessNode) .Write = true →
      DuplicatePrefixScalarAuthorization.Compatible
        ((location.perms.get query).getD node.defaultLocationState) .Write .LocalAccess (protections.contains node.tag))
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (witness : CutoffWitness tree location protections root position maximum area.contains)
    (stable : SkipStable tree location protections maximum area.contains) :
    Authorization tree location protections root position maximum .Write area.contains := by
  refine ⟨area.rooted,area.present,area.children,covers,?_,?_,witness_kind tree location protections root position maximum area.contains witness .Write⟩
  · intro query node inside present
    exact possible query node inside present
  · intro before after legalBefore legalAfter _ query node inside present _
    let state := (location.perms.get query).getD node.defaultLocationState
    have statePossible : state.possible = true := possible query node inside present
    refine ⟨statePossible,?_⟩
    by_cases skipped : entrySkip state .Write (residualRelation tree location protections root query node maximum .Write position before) = true
    · exact Or.inl skipped
    · apply Or.inr
      have nonabsent := relation_present tree location protections root position maximum area covers depth order witness query node inside present .Write after legalAfter
      cases classified : residualRelation tree location protections root query node maximum .Write position after with
      | none => exact False.elim (nonabsent classified)
      | some related =>
        cases related with
        | EitherAccess => trivial
        | LocalAccess =>
          exact ⟨by simp [skip,AccessRelatedness.isForeign],
            local_compatible tree location protections root position maximum area covers primaryWrite query node inside present after classified⟩
        | ForeignAccess =>
          refine ⟨?_,foreign_compatible tree location protections root position maximum area foreign depth query node inside present after legalAfter classified⟩
          cases skipForeign : skip state .Write .ForeignAccess with
          | false => rfl
          | true =>
            have entryForeign : residualRelation tree location protections root query node maximum .Write position before = some .ForeignAccess := by
              cases above : aboveMaximum node maximum with
              | true => exact clamped_foreign tree location protections root position maximum area covers depth order witness query node inside present above .Write before legalBefore
              | false =>
                have zero := foreign_zero _ _ _ (by simpa only [residualRelation,above] using classified)
                have beforeStable := residual_stable tree location protections maximum area.contains stable query node inside present skipForeign before legalBefore
                have afterStable := residual_stable tree location protections maximum area.contains stable query node inside present skipForeign after legalAfter
                have beforeZero : residualCount tree location protections .Write before query = 0 := by omega
                have positive := total_positive tree location protections root position maximum area covers depth witness .Write before legalBefore
                simpa only [residualRelation,above,beforeZero] using zero_foreign _ _ positive
            exact False.elim (skipped (by simpa only [entryForeign,entrySkip] using skipForeign))

/-- Full existing Row from fieldless Write data. Protector Read is derived by
the existing WriteReadSnapshot adapter, without primary Read ancestry. The
numeric adapter below derives the unchanged SkipStable condition from numeric
cache soundness. No operation success or ordinary-validity claim is assumed. -/
theorem row_of_write_fields (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (source selectedRoot : Option UniIndex) (maximum : Option BorTag)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (tagOrder : ParentTagOrder tree)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (short : tree.nodes.size < 65536)
    (wildcard : source = none → selectedRoot = none)
    (rootPath : ∀ anchor, source = some anchor →
      ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast? =
        selectedRoot.map UniIndex.toNat)
    (rootPresent : ∀ root, selectedRoot = some root → ∃ node, tree.nodeAt root = some node)
    (cutoff : maximum = selectedRoot.bind (fun root => (tree.nodeAt root).map TreeNode.tag))
    (normal : ∀ anchor, source = some anchor →
      ∃ component : GeneralBorrowExposedScopedNormal.Component
          (source_normal_projection tree default protections).topology anchor.toNat,
        ∀ index, component.support index → index < tree.nodes.data.size →
          ∃ state, (source_normal_projection tree location protections).stateAt index = some state ∧
            DuplicatePrefixScalarAuthorization.Compatible state .Write
              (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) anchor.toNat index)
              ((source_normal_projection tree location protections).protectedNodes.contains index))
    (ownership : ∀ position, (valid : position < tree.roots.size) →
      selectedRoot ≠ some tree.roots[position] →
      ∃ area : GeneralBorrowWildcardControlStack.Support tree tree.roots[position],
        (∀ query, area.contains query → Covers tree.nodes tree.roots[position] query) ∧
        (∀ query node, area.contains query → tree.nodes.get query = some node →
      ((location.perms.get query).getD node.defaultLocationState).possible = true) ∧
        (∀ query node, area.contains query → tree.nodes.get query = some node →
      (aboveMaximum node maximum = true ∨ ¬ RetainedBelow tree location protections maximum query) →
      DuplicatePrefixScalarAuthorization.Compatible
        ((location.perms.get query).getD node.defaultLocationState) .Write .ForeignAccess (protections.contains node.tag)) ∧
        (position = 0 → ∀ query node, area.contains query → tree.nodes.get query = some node →
      ∀ witness witnessNode, tree.nodes.get witness = some witnessNode → witnessNode.isExposed = true →
      query ∈ walk tree.nodes (tree.nodes.size+1) witness →
      supports (effective location protections witness witnessNode) .Write = true →
      DuplicatePrefixScalarAuthorization.Compatible
        ((location.perms.get query).getD node.defaultLocationState) .Write .LocalAccess (protections.contains node.tag)) ∧
        CutoffWitness tree location protections tree.roots[position] position maximum area.contains ∧
        SkipStable tree location protections maximum area.contains) :
    DuplicatePrefixBorrowAuthorization.Row tree location protections source selectedRoot maximum := by
  apply BoolDestinationWriteOnlyAdapter.WriteRow.complete (coherent := coherent) (short := short)
  refine {
    wildcard := wildcard
    rootPath := rootPath
    rootPresent := rootPresent
    cutoff := cutoff
    normal := ?_
    callbacks := ?_ }
  · intro anchor selected
    obtain ⟨component, permissions⟩ := normal anchor selected
    exact ⟨⟨component, permissions⟩⟩
  · intro position valid other
    obtain ⟨area,covers,possible,foreign,primaryWrite,witness,stable⟩ := ownership position valid other
    exact ⟨area.contains,write_authorization_of_fields tree location protections _ position maximum
      area covers possible foreign primaryWrite depth tagOrder witness stable⟩

theorem callback_write_authorization (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag)
    (rights : CallbackOwnership tree location protections root position maximum)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (witness : CutoffWitness tree location protections root position maximum rights.area.contains)
    (stable : SkipStable tree location protections maximum rights.area.contains) :
    Authorization tree location protections root position maximum .Write rights.area.contains := by
  exact write_authorization_of_fields tree location protections root position maximum
    rights.area rights.covers rights.possible rights.foreign
    (fun primary query node inside present witness witnessNode found exposed walked supported =>
      rights.primaryLocal primary query node inside present witness witnessNode found exposed walked .Write supported)
    depth order witness stable

theorem callback_row (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (source selectedRoot : Option UniIndex) (maximum : Option BorTag)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (tagOrder : ParentTagOrder tree)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (short : tree.nodes.size < 65536)
    (wildcard : source = none → selectedRoot = none)
    (rootPath : ∀ anchor, source = some anchor →
      ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast? =
        selectedRoot.map UniIndex.toNat)
    (rootPresent : ∀ root, selectedRoot = some root → ∃ node, tree.nodeAt root = some node)
    (cutoff : maximum = selectedRoot.bind (fun root => (tree.nodeAt root).map TreeNode.tag))
    (normal : ∀ anchor, source = some anchor →
      ∃ component : GeneralBorrowExposedScopedNormal.Component
          (source_normal_projection tree default protections).topology anchor.toNat,
        ∀ index, component.support index → index < tree.nodes.data.size →
          ∃ state, (source_normal_projection tree location protections).stateAt index = some state ∧
            DuplicatePrefixScalarAuthorization.Compatible state .Write
              (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) anchor.toNat index)
              ((source_normal_projection tree location protections).protectedNodes.contains index))
    (ownership : ∀ position, (valid : position < tree.roots.size) →
      selectedRoot ≠ some tree.roots[position] →
      ∃ rights : CallbackOwnership tree location protections tree.roots[position] position maximum,
        SkipStable tree location protections maximum rights.area.contains) :
    DuplicatePrefixBorrowAuthorization.Row tree location protections source selectedRoot maximum := by
  apply row_of_write_fields tree location protections source selectedRoot maximum
    depth tagOrder coherent short wildcard rootPath rootPresent cutoff normal
  intro position valid other
  obtain ⟨rights,stable⟩ := ownership position valid other
  exact ⟨rights.area,rights.covers,rights.possible,rights.foreign,
    (fun primary query node inside present witness witnessNode found exposed walked supported =>
      rights.primaryLocal primary query node inside present witness witnessNode found exposed walked .Write supported),
    rights.cutoff,stable⟩

theorem generalized_write_authorization (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag)
    (rights : GeneralizedOwnership tree location protections root position maximum)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (witness : CutoffWitness tree location protections root position maximum rights.area.contains)
    (stable : SkipStable tree location protections maximum rights.area.contains) :
    Authorization tree location protections root position maximum .Write rights.area.contains := by
  exact callback_write_authorization tree location protections root position maximum rights.toCallbackOwnership
    depth order witness stable

theorem generalized_row (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (source selectedRoot : Option UniIndex) (maximum : Option BorTag)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (tagOrder : ParentTagOrder tree)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (short : tree.nodes.size < 65536)
    (wildcard : source = none → selectedRoot = none)
    (rootPath : ∀ anchor, source = some anchor →
      ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast? =
        selectedRoot.map UniIndex.toNat)
    (rootPresent : ∀ root, selectedRoot = some root → ∃ node, tree.nodeAt root = some node)
    (cutoff : maximum = selectedRoot.bind (fun root => (tree.nodeAt root).map TreeNode.tag))
    (normal : ∀ anchor, source = some anchor →
      ∃ component : GeneralBorrowExposedScopedNormal.Component
          (source_normal_projection tree default protections).topology anchor.toNat,
        ∀ index, component.support index → index < tree.nodes.data.size →
          ∃ state, (source_normal_projection tree location protections).stateAt index = some state ∧
            DuplicatePrefixScalarAuthorization.Compatible state .Write
              (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) anchor.toNat index)
              ((source_normal_projection tree location protections).protectedNodes.contains index))
    (ownership : ∀ position, (valid : position < tree.roots.size) →
      selectedRoot ≠ some tree.roots[position] →
      ∃ rights : GeneralizedOwnership tree location protections tree.roots[position] position maximum,
        SkipStable tree location protections maximum rights.area.contains) :
    DuplicatePrefixBorrowAuthorization.Row tree location protections source selectedRoot maximum := by
  apply callback_row tree location protections source selectedRoot maximum depth tagOrder coherent short
    wildcard rootPath rootPresent cutoff normal
  intro position valid other
  obtain ⟨rights,stable⟩ := ownership position valid other
  exact ⟨rights.toCallbackOwnership,stable⟩

theorem write_authorization (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag)
    (rights : Ownership tree location protections root position maximum)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (witness : CutoffWitness tree location protections root position maximum rights.area.contains)
    (stable : SkipStable tree location protections maximum rights.area.contains) :
    Authorization tree location protections root position maximum .Write rights.area.contains := by
  exact callback_write_authorization tree location protections root position maximum rights.toCallbackOwnership
    depth order witness stable

theorem row (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (source selectedRoot : Option UniIndex) (maximum : Option BorTag)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (tagOrder : ParentTagOrder tree)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (short : tree.nodes.size < 65536)
    (wildcard : source = none → selectedRoot = none)
    (rootPath : ∀ anchor, source = some anchor →
      ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast? =
        selectedRoot.map UniIndex.toNat)
    (rootPresent : ∀ root, selectedRoot = some root → ∃ node, tree.nodeAt root = some node)
    (cutoff : maximum = selectedRoot.bind (fun root => (tree.nodeAt root).map TreeNode.tag))
    (normal : ∀ anchor, source = some anchor →
      ∃ component : GeneralBorrowExposedScopedNormal.Component
          (source_normal_projection tree default protections).topology anchor.toNat,
        ∀ index, component.support index → index < tree.nodes.data.size →
          ∃ state, (source_normal_projection tree location protections).stateAt index = some state ∧
            DuplicatePrefixScalarAuthorization.Compatible state .Write
              (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) anchor.toNat index)
              ((source_normal_projection tree location protections).protectedNodes.contains index))
    (ownership : ∀ position, (valid : position < tree.roots.size) →
      selectedRoot ≠ some tree.roots[position] →
      ∃ rights : Ownership tree location protections tree.roots[position] position maximum,
        SkipStable tree location protections maximum rights.area.contains) :
    DuplicatePrefixBorrowAuthorization.Row tree location protections source selectedRoot maximum := by
  apply callback_row tree location protections source selectedRoot maximum depth tagOrder coherent short
    wildcard rootPath rootPresent cutoff normal
  intro position valid other
  obtain ⟨rights,stable⟩ := ownership position valid other
  exact ⟨rights.toCallbackOwnership,stable⟩

end DuplicatePrefix.S05RetainedConeOwnership
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05RetainedConeOwnership." then
      for ax in (←collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
          throwError "unapproved axiom {ax}"
