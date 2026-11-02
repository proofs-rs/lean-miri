import duplicate_prefix.S05ZeroCellCurrentCorrelation
import duplicate_prefix.CompletedBorrowAncestry
import duplicate_prefix.GeneralBorrowSharedAuthorizationGeometry

/-! One explicit finite completion for the current eleven-node accepted
packet. This is sufficient proof-model data, not an adopted ordinary-input
predicate or a theorem for arbitrary borrow histories. -/
namespace DuplicatePrefix.S05ZeroCellCompletedBorrowModel
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open S05ZeroCellTypedGeneratedPrefix CandidateStableCallOwnership
open GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowWildcardParentTagOrder
open S05ZeroCellCurrentCorrelation (raw precise node sourceAncestor)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option cbv.maxSteps 1000000
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

def completion : Completion where
  parents := S05ZeroCellCurrentCorrelation.precise.nodes.data.map (fun node => node.bind TreeNode.parent)
  depths := #[0,1,2,1,3,2,3,4,5,4,5]

private def graphRows : Array (BorTag × Option UniIndex × Array UniIndex × Bool) :=
  #[(tag 1,none,#[],true),(tag 2,none,#[ix 2],false),
    (tag 3,some (ix 1),#[ix 4],false),(tag 4,none,#[ix 5],false),
    (tag 5,some (ix 2),#[],true),(tag 6,some (ix 3),#[ix 6],false),
    (tag 8,some (ix 5),#[ix 7,ix 9],false),(tag 10,some (ix 6),#[ix 8],false),
    (tag 11,some (ix 7),#[],false),(tag 12,some (ix 6),#[ix 10],false),
    (tag 13,some (ix 9),#[],false)]

private theorem graph_table :
    S05ZeroCellCurrentCorrelation.raw.nodes.data.map (Option.map (fun node =>
      (node.tag,node.parent,node.children,node.isExposed))) = graphRows.map some := by cbv

private theorem ix_nat (i : Fin 11) : (ix i.val).toNat = i.val := by
  simp only [ix,UniIndex.toNat]
  exact Nat.mod_eq_of_lt (by have bound := i.isLt; omega)

theorem node_present (i : Fin 11) :
    S05ZeroCellCurrentCorrelation.raw.nodes.get (ix i.val) = some (S05ZeroCellCurrentCorrelation.node S05ZeroCellCurrentCorrelation.raw i) := by
  have size := S05ZeroCellCurrentCorrelation.endpoint_identity.1
  have all := S05ZeroCellCurrentCorrelation.endpoint_identity.2.2.1
  have bound : i.val < S05ZeroCellCurrentCorrelation.raw.nodes.data.size := by rw [size]; exact i.isLt
  have occupied := Array.all_eq_true.mp all i.val bound
  cases cell : S05ZeroCellCurrentCorrelation.raw.nodes.data[i.val] with
  | none => simp [cell] at occupied
  | some actual =>
    have lookup : S05ZeroCellCurrentCorrelation.raw.nodes.get (ix i.val) = some actual := by
      simp only [UniValMap.get,ix_nat,Array.getElem?_eq_getElem bound,cell]
    simp only [S05ZeroCellCurrentCorrelation.node,BorrowTree.nodeAt,lookup,Option.getD_some]

private theorem projection (i : Fin 11) :
    let node := S05ZeroCellCurrentCorrelation.node S05ZeroCellCurrentCorrelation.raw i
    (node.tag,node.parent,node.children,node.isExposed) = graphRows[i.val]'(by exact i.isLt) := by
  have present := node_present i
  have slot : S05ZeroCellCurrentCorrelation.raw.nodes.data[i.val]? = some (some (S05ZeroCellCurrentCorrelation.node S05ZeroCellCurrentCorrelation.raw i)) := by
    unfold UniValMap.get at present
    rw [ix_nat] at present
    cases cell : S05ZeroCellCurrentCorrelation.raw.nodes.data[i.val]? with
    | none => simp [cell] at present
    | some entry => simpa only [cell] using congrArg some present
  have graphSlot : graphRows[i.val]? = some (graphRows[i.val]'(by exact i.isLt)) :=
    Array.getElem?_eq_getElem i.isLt
  have projected := congrArg (fun rows => rows[i.val]?) graph_table
  simpa only [Array.getElem?_map,slot,graphSlot,Option.map_some,Option.some.injEq] using projected

private def row (i : Fin 11) := graphRows[i.val]'(by exact i.isLt)
private def parentsData : Array (Option UniIndex) :=
  #[none,some (ix 0),some (ix 1),some (ix 0),some (ix 2),some (ix 3),
    some (ix 5),some (ix 6),some (ix 7),some (ix 6),some (ix 9)]
private def parentAt (i : Fin 11) := parentsData[i.val]'(by exact i.isLt)
private def depthAt (i : Fin 11) := completion.depths[i.val]'(by exact i.isLt)
private def mapping : UniKeyMap BorTag :=
  {mapping := #[(tag 1,ix 0),(tag 2,ix 1),(tag 3,ix 2),(tag 4,ix 3),(tag 5,ix 4),
    (tag 6,ix 5),(tag 8,ix 6),(tag 10,ix 7),(tag 11,ix 8),(tag 12,ix 9),(tag 13,ix 10)]}

private theorem parents_table : completion.parents = parentsData := by cbv
theorem roots : raw.roots = #[ix 0,ix 1,ix 3] := by cbv
private theorem mapping_table : raw.tagMapping = mapping := by cbv

private instance rowParentDecidable (i : Fin 11) : Decidable (match (row i).2.1 with
    | none => True | some parent => ∃ j : Fin 11, parent = ix j.val) := by
  cases (row i).2.1 <;> infer_instance
private instance completedParentDecidable (i : Fin 11) : Decidable (match parentAt i with
    | none => True | some parent => ∃ j : Fin 11, parent = ix j.val) := by
  cases parentAt i <;> infer_instance

private theorem finite_reflection :
    (∀ i : Fin 11, mapping.get (row i).1 = some (ix i.val)) ∧
    (∀ i : Fin 11, ((row i).2.2.1.toList.all
      (fun child => decide (∃ j : Fin 11, child = ix j.val))) = true) ∧
    (∀ i j : Fin 11, ix j.val ∈ (row i).2.2.1.toList ↔ (row j).2.1 = some (ix i.val)) ∧
    (∀ i : Fin 11, match (row i).2.1 with | none => True | some parent => ∃ j : Fin 11, parent = ix j.val) ∧
    (∀ i j : Fin 11, (row i).2.1 = some (ix j.val) → parentAt i = some (ix j.val)) ∧
    (∀ i : Fin 11, (row i).2.1 = none ↔ ix i.val ∈ [ix 0,ix 1,ix 3]) ∧
    (∀ i : Fin 11, match parentAt i with | none => True | some parent => ∃ j : Fin 11, parent = ix j.val) ∧
    (∀ i j : Fin 11, parentAt i = some (ix j.val) → depthAt j < depthAt i) ∧
    (∀ i j : Fin 11, (row i).2.1 = some (ix j.val) → (row j).1.value ≤ (row i).1.value) := by
  decide +kernel

private theorem index_self (index : UniIndex) : index = ix index.toNat := by
  cases index
  simp [ix,UniIndex.toNat]

private theorem present_fin {index : UniIndex} {actual : TreeNode}
    (present : raw.nodes.get index = some actual) :
    ∃ i : Fin 11, index = ix i.val ∧ actual = node raw i := by
  have bound : index.toNat < raw.nodes.data.size := by
    by_cases inside : index.toNat < raw.nodes.data.size
    · exact inside
    · have absent : raw.nodes.data[index.toNat]? = none := Array.getElem?_eq_none (by omega)
      simp only [UniValMap.get,absent] at present
      contradiction
  let i : Fin 11 := ⟨index.toNat,by rw [S05ZeroCellCurrentCorrelation.endpoint_identity.1] at bound; exact bound⟩
  have sameIndex : index = ix i.val := index_self index
  have sameNode : actual = node raw i := Option.some.inj (present.symm.trans (sameIndex ▸ node_present i))
  exact ⟨i,sameIndex,sameNode⟩

private theorem parent_field (i : Fin 11) : (node raw i).parent = (row i).2.1 :=
  congrArg (fun fields => fields.2.1) (projection i)
private theorem tag_field (i : Fin 11) : (node raw i).tag = (row i).1 :=
  congrArg Prod.fst (projection i)
private theorem children_field (i : Fin 11) : (node raw i).children = (row i).2.2.1 :=
  congrArg (fun fields => fields.2.2.1) (projection i)

private theorem reciprocal (i : Fin 11) (child : UniIndex) :
    child ∈ (node raw i).children.toList ↔
      ∃ childNode, raw.nodes.get child = some childNode ∧ childNode.parent = some (ix i.val) := by
  rw [children_field]
  constructor
  · intro member
    have available := List.all_eq_true.mp (finite_reflection.2.1 i) child member
    obtain ⟨j,same⟩ := of_decide_eq_true available
    subst child
    exact ⟨node raw j,node_present j,(parent_field j).trans ((finite_reflection.2.2.1 i j).mp member)⟩
  · rintro ⟨childNode,present,parent⟩
    obtain ⟨j,sameIndex,sameNode⟩ := present_fin present
    subst child
    subst childNode
    exact (finite_reflection.2.2.1 i j).mpr ((parent_field j).symm.trans parent)

private theorem root_cases {position : Nat} {root : UniIndex} (slot : raw.roots[position]? = some root) :
    (position = 0 ∧ root = ix 0) ∨ (position = 1 ∧ root = ix 1) ∨ (position = 2 ∧ root = ix 3) := by
  rw [roots] at slot
  have bound : position < 3 := (Array.getElem?_eq_some_iff.mp slot).1
  have cases : position=0 ∨ position=1 ∨ position=2 := by omega
  rcases cases with rfl | rfl | rfl
  · exact .inl ⟨rfl,(Option.some.inj slot).symm⟩
  · exact .inr (.inl ⟨rfl,(Option.some.inj slot).symm⟩)
  · exact .inr (.inr ⟨rfl,(Option.some.inj slot).symm⟩)

private theorem parent_lookup (i : Fin 11) : completion.parents[(ix i.val).toNat]? = some (parentAt i) := by
  rw [parents_table,ix_nat]
  exact Array.getElem?_eq_getElem i.isLt

private theorem completed_edge_fin {child parent : UniIndex}
    (edge : completion.parents[child.toNat]? = some (some parent)) :
    ∃ i j : Fin 11, child = ix i.val ∧ parent = ix j.val ∧ parentAt i = some (ix j.val) := by
  have bound : child.toNat < 11 := by
    rw [parents_table] at edge
    exact (Array.getElem?_eq_some_iff.mp edge).1
  let i : Fin 11 := ⟨child.toNat,bound⟩
  have same : child = ix i.val := index_self child
  have atParent : parentAt i = some parent := Option.some.inj ((parent_lookup i).symm.trans (same ▸ edge))
  have available := finite_reflection.2.2.2.2.2.2.1 i
  rw [atParent] at available
  obtain ⟨j,parentSame⟩ := available
  exact ⟨i,j,same,parentSame,atParent.trans (congrArg some parentSame)⟩

private theorem depth_lookup (i : Fin 11) :
    (completion.depths[(ix i.val).toNat]?).getD 0 = depthAt i := by
  rw [ix_nat,Array.getElem?_eq_getElem i.isLt]
  rfl

/-- The candidate's finite graph clauses hold for the actual current raw
tree and the fixed precise completion, without scalar refinement premises. -/
theorem complete : Completes raw completion := by
  rcases finite_reflection with ⟨mappingOK,_,_,parentsAvailable,preserve,rootOK,_,strict,_⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · rw [parents_table,S05ZeroCellCurrentCorrelation.endpoint_identity.1]
    rfl
  · rw [S05ZeroCellCurrentCorrelation.endpoint_identity.1]
    rfl
  · rw [roots]
    decide +kernel
  · intro position root slot
    rcases root_cases slot with ⟨_,rfl⟩ | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact ⟨node raw ⟨0,by decide⟩,node_present ⟨0,by decide⟩,parent_field ⟨0,by decide⟩⟩
    · exact ⟨node raw ⟨1,by decide⟩,node_present ⟨1,by decide⟩,parent_field ⟨1,by decide⟩⟩
    · exact ⟨node raw ⟨3,by decide⟩,node_present ⟨3,by decide⟩,parent_field ⟨3,by decide⟩⟩
  · intro index actual present
    obtain ⟨i,rfl,rfl⟩ := present_fin present
    refine ⟨?_,reciprocal i,?_,?_⟩
    · rw [tag_field,mapping_table]
      exact mappingOK i
    · intro parent edge
      have rowEdge : (row i).2.1 = some parent := (parent_field i).symm.trans edge
      have available := parentsAvailable i
      rw [rowEdge] at available
      obtain ⟨j,rfl⟩ := available
      exact (parent_lookup i).trans (congrArg some (preserve i j rowEdge))
    · rw [parent_field,roots]
      exact rootOK i
  · intro position root slot
    rcases root_cases slot with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · change completion.parents[(ix 0).toNat]? = some none
      exact parent_lookup ⟨0,by decide⟩
    · refine ⟨0,ix 0,ix 0,node raw ⟨1,by decide⟩,node raw ⟨0,by decide⟩,
        by decide,?_,node_present ⟨1,by decide⟩,node_present ⟨0,by decide⟩,?_,?_,
        .refl _ _ (node_present ⟨0,by decide⟩),?_⟩
      · rw [roots]; rfl
      · exact congrArg (fun fields => fields.2.2.2) (projection ⟨0,by decide⟩)
      · rw [tag_field,tag_field]; decide +kernel
      · exact parent_lookup ⟨1,by decide⟩
    · refine ⟨0,ix 0,ix 0,node raw ⟨3,by decide⟩,node raw ⟨0,by decide⟩,
        by decide,?_,node_present ⟨3,by decide⟩,node_present ⟨0,by decide⟩,?_,?_,
        .refl _ _ (node_present ⟨0,by decide⟩),?_⟩
      · rw [roots]; rfl
      · exact congrArg (fun fields => fields.2.2.2) (projection ⟨0,by decide⟩)
      · rw [tag_field,tag_field]; decide +kernel
      · exact parent_lookup ⟨3,by decide⟩
  · intro child parent edge
    obtain ⟨i,j,rfl,rfl,chosen⟩ := completed_edge_fin edge
    exact ⟨⟨node raw i,node_present i⟩,⟨node raw j,node_present j⟩,
      by rw [depth_lookup,depth_lookup]; exact strict i j chosen⟩

theorem order : ParentTagOrder raw := by
  intro child childNode childPresent parent parentNode edge parentPresent
  obtain ⟨i,rfl,rfl⟩ := present_fin childPresent
  obtain ⟨j,rfl,rfl⟩ := present_fin parentPresent
  rw [tag_field,tag_field]
  exact finite_reflection.2.2.2.2.2.2.2.2 i j ((parent_field i).symm.trans edge)

def depth : GeneralBorrowExposure.ParentDepth raw.nodes where
  depth index := (completion.depths[index.toNat]?).getD 0
  bounded index actual present := by
    obtain ⟨i,rfl,rfl⟩ := present_fin present
    rw [depth_lookup]
    change depthAt i ≤ raw.nodes.data.size
    rw [S05ZeroCellCurrentCorrelation.endpoint_identity.1]
    have finite : ∀ i : Fin 11, depthAt i ≤ 11 := by decide +kernel
    exact finite i
  parent index actual present parent edge := by
    have chosen := (complete.2.2.2.2.1 index actual present).2.2.1 parent edge
    obtain ⟨_,⟨earlier,earlierPresent⟩,smaller⟩ := complete.2.2.2.2.2.2 index parent chosen
    exact ⟨earlier,earlierPresent,smaller⟩

theorem slots : raw.roots[0]? = some (ix 0) ∧ raw.roots[1]? = some (ix 1) ∧
    raw.roots[2]? = some (ix 3) := by rw [roots]; exact ⟨rfl,rfl,rfl⟩

theorem source_path : Path raw (ix 3) (ix 10) := by
  have p3 : Path raw (ix 3) (ix 3) := .refl _ _ (node_present ⟨3,by decide⟩)
  have p5 : Path raw (ix 3) (ix 5) := .step p3 _ (node_present ⟨5,by decide⟩) (parent_field ⟨5,by decide⟩)
  have p6 : Path raw (ix 3) (ix 6) := .step p5 _ (node_present ⟨6,by decide⟩) (parent_field ⟨6,by decide⟩)
  have p9 : Path raw (ix 3) (ix 9) := .step p6 _ (node_present ⟨9,by decide⟩) (parent_field ⟨9,by decide⟩)
  exact .step p9 _ (node_present ⟨10,by decide⟩) (parent_field ⟨10,by decide⟩)

theorem selected_tag : (node raw ⟨3,by decide⟩).tag = tag 4 := tag_field ⟨3,by decide⟩

theorem query_covers {root query : UniIndex} (path : Path raw root query) :
    GeneralBorrowExposureCardinality.Covers raw.nodes root query :=
  GeneralBorrowSharedAuthorizationGeometry.covers_of_path raw depth root query path

private def sourceIndices : List UniIndex := [ix 0,ix 3,ix 5,ix 6,ix 9,ix 10]
private theorem ancestor_reflection :
    (∀ i : Fin 11, sourceAncestor i ↔ ix i.val ∈ sourceIndices) ∧
    (∀ i j : Fin 11, parentAt i = some (ix j.val) →
      ix i.val ∈ sourceIndices → ix j.val ∈ sourceIndices) := by decide +kernel

private theorem below_member {query last : UniIndex} (below : Below completion query last)
    (member : last ∈ sourceIndices) : query ∈ sourceIndices := by
  induction below with
  | refl => exact member
  | @step parent child edge prior ih =>
    obtain ⟨i,j,rfl,rfl,chosen⟩ := completed_edge_fin edge
    exact ih (ancestor_reflection.2 i j chosen member)

/-- The endpoint table's finite ancestry split is exactly completed ancestry
of the actual source helper, not an unrelated selection of indices. -/
theorem source_ancestor_iff (i : Fin 11) :
    Below completion (ix i.val) (ix 10) ↔ sourceAncestor i := by
  constructor
  · intro below
    exact (ancestor_reflection.1 i).mpr (below_member below (by decide +kernel))
  · intro ancestor
    have b10 : Below completion (ix 10) (ix 10) := .refl _
    have b9 : Below completion (ix 9) (ix 10) := .step (parent_lookup ⟨10,by decide⟩) (.refl _)
    have b6 : Below completion (ix 6) (ix 10) := CompletedBorrowAncestry.below_trans
      (.step (parent_lookup ⟨9,by decide⟩) (.refl _)) b9
    have b5 : Below completion (ix 5) (ix 10) := CompletedBorrowAncestry.below_trans
      (.step (parent_lookup ⟨6,by decide⟩) (.refl _)) b6
    have b3 : Below completion (ix 3) (ix 10) := CompletedBorrowAncestry.below_trans
      (.step (parent_lookup ⟨5,by decide⟩) (.refl _)) b5
    have b0 : Below completion (ix 0) (ix 10) := CompletedBorrowAncestry.below_trans
      (.step (parent_lookup ⟨3,by decide⟩) (.refl _)) b3
    rcases i with ⟨i,bound⟩
    change i=0 ∨ i=3 ∨ i=5 ∨ i=6 ∨ i=9 ∨ i=10 at ancestor
    rcases ancestor with rfl | rfl | rfl | rfl | rfl | rfl
    · exact b0
    · exact b3
    · exact b5
    · exact b6
    · exact b9
    · exact b10

def location : LocationTree := ((raw.locations.entries[0]?).map (·.data)).getD default

theorem local_rights {index : UniIndex} {actual : TreeNode}
    (present : raw.nodes.get index = some actual) (ancestor : Below completion index (ix 10)) :
    OrdinaryBorrowAuthority.LocalWrite ((location.perms.get index).getD actual.defaultLocationState)
      (S05ZeroCellCurrentCorrelation.held.contains actual.tag) := by
  obtain ⟨i,rfl,rfl⟩ := present_fin present
  have selected := (source_ancestor_iff i).mp ancestor
  have rights := (S05ZeroCellCurrentCorrelation.current_rights i).2
  change OrdinaryBorrowAuthority.LocalWrite (S05ZeroCellCurrentCorrelation.state raw i)
    (S05ZeroCellCurrentCorrelation.held.contains (node raw i).tag)
  simpa only [S05ZeroCellCurrentCorrelation.WriteRight,selected,ite_true] using rights

theorem foreign_rights {index : UniIndex} {actual : TreeNode}
    (present : raw.nodes.get index = some actual) (outside : ¬ Below completion index (ix 10)) :
    OrdinaryBorrowAuthority.ForeignWrite ((location.perms.get index).getD actual.defaultLocationState)
      (S05ZeroCellCurrentCorrelation.held.contains actual.tag) := by
  obtain ⟨i,rfl,rfl⟩ := present_fin present
  have unselected : ¬ sourceAncestor i := fun selected => outside ((source_ancestor_iff i).mpr selected)
  have rights := (S05ZeroCellCurrentCorrelation.current_rights i).2
  change OrdinaryBorrowAuthority.ForeignWrite (S05ZeroCellCurrentCorrelation.state raw i)
    (S05ZeroCellCurrentCorrelation.held.contains (node raw i).tag)
  simpa only [S05ZeroCellCurrentCorrelation.WriteRight,unselected,ite_false] using rights

private def scalarBound (i : Fin 11) : Bool :=
  let state := S05ZeroCellCurrentCorrelation.state raw i
  match state.permission.strongestIdempotentForeignAccess
      (S05ZeroCellCurrentCorrelation.held.contains (node raw i).tag) with
  | .Access strongest => decide (state.idempotentForeignAccess.rank ≤ strongest.rank)
  | .ImpossibleProtectedReservedIM => false

private theorem scalar_bounds : ((List.finRange 11).all scalarBound) = true := by cbv

/-- The actual current row independently satisfies the SIFA bound at every
present query. No callback success is a premise. -/
theorem consistent {index : UniIndex} {actual : TreeNode}
    (present : raw.nodes.get index = some actual) :
    GeneralBorrowSifaPermissionConsistency.Consistent
      ((location.perms.get index).getD actual.defaultLocationState)
      (S05ZeroCellCurrentCorrelation.held.contains actual.tag) := by
  obtain ⟨i,rfl,rfl⟩ := present_fin present
  have bound := List.all_eq_true.mp scalar_bounds i (List.mem_finRange i)
  change GeneralBorrowSifaPermissionConsistency.Consistent
    (S05ZeroCellCurrentCorrelation.state raw i)
    (S05ZeroCellCurrentCorrelation.held.contains (node raw i).tag)
  cases rule : (S05ZeroCellCurrentCorrelation.state raw i).permission.strongestIdempotentForeignAccess
      (S05ZeroCellCurrentCorrelation.held.contains (node raw i).tag) with
  | Access strongest =>
    exact ⟨strongest,rule,of_decide_eq_true (by simpa only [scalarBound,rule] using bound)⟩
  | ImpossibleProtectedReservedIM =>
    simp only [scalarBound,rule] at bound
    contradiction

end DuplicatePrefix.S05ZeroCellCompletedBorrowModel

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05ZeroCellCompletedBorrowModel." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved current completion dependency {dependency}"
