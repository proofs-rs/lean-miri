import duplicate_prefix.GeneralBorrowGcDfsShape
import duplicate_prefix.GeneralBorrowWildcardForestWeights

namespace DuplicatePrefix.GeneralBorrowGcDfsFormation
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowGcDfsShape DuplicatePrefix.GeneralBorrowProjection
open DuplicatePrefix.GeneralBorrowForest
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- Finite unfolding of ORIGINAL child metadata. No GC execution is evaluated. -/
def unroll (original : BorrowTree) : Nat → UniIndex → Shape
  | 0, index => .node index []
  | fuel+1, index => match original.nodes.get index with
    | none => .node index []
    | some node => .node index (node.children.toList.map (unroll original fuel))

theorem unroll_root (original : BorrowTree) (fuel : Nat) (index : UniIndex) :
    (unroll original fuel index).root = index := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp only [unroll];split <;> rfl

private theorem sum_member (rows : List UniIndex) (weight : UniIndex → Nat) (index : UniIndex)
    (member : index ∈ rows) : weight index ≤ (rows.map weight).sum := by
  induction rows with
  | nil => simp at member
  | cons head tail ih =>
    simp only [List.map_cons,List.sum_cons]
    rcases List.mem_cons.mp member with same | later
    · subst index;omega
    · have bound := ih later;omega

private theorem sum_mono {α : Type} (rows : List α) (left right : α → Nat)
    (bound : ∀ item ∈ rows, left item ≤ right item) : (rows.map left).sum ≤ (rows.map right).sum := by
  induction rows with
  | nil => exact Nat.le_refl _
  | cons head tail ih =>
    have first := bound head (by simp)
    have rest := ih (by intro item member;exact bound item (List.mem_cons_of_mem _ member))
    simp only [List.map_cons,List.sum_cons];omega

/-- A source child-sum potential supplies sufficient unfolding fuel, including
all present child lookups. It is a graph-data potential, not a successful walk. -/
theorem unroll_valid (original : BorrowTree) (weights : GeneralBorrowWildcardSubtreeData.Weights original)
    (children : GeneralBorrowGraph.ChildNodes original) (fuel : Nat) (index : UniIndex) (node : TreeNode)
    (present : original.nodes.get index = some node) (enough : weights.weight index ≤ fuel) :
    (unroll original fuel index).Valid original := by
  induction fuel generalizing index node with
  | zero => have bound := weights.children index node present;omega
  | succ fuel ih =>
    simp only [unroll,present,Shape.Valid]
    refine ⟨node,rfl,?_,?_⟩
    · simp [List.map_map,Function.comp_def,unroll_root]
    · intro child member
      obtain ⟨childIndex,childMember,rfl⟩ := List.mem_map.mp member
      obtain ⟨childNode,childPresent⟩ := children index node present childIndex childMember
      have sumBound := sum_member node.children.toList weights.weight childIndex childMember
      have parentBound := weights.children index node present
      exact ih childIndex childNode childPresent (by omega)

private theorem source_node (original : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (index : UniIndex) (node : TreeNode) (present : original.nodes.get index = some node) :
    ∃ valid : index.toNat < (source_normal_projection original location protections).topology.nodes.size,
      (source_normal_projection original location protections).topology.nodes[index.toNat] =
        ⟨node.parent.map UniIndex.toNat,node.children.toList.map UniIndex.toNat⟩ := by
  have valid : index.toNat < (source_normal_projection original location protections).topology.nodes.size := by
    have bounded := GeneralBorrowNodeUpdate.lookup_valid original.nodes index node present
    unfold_general_projection;unfold_general_topology
    simpa only [Array.size_map] using bounded
  refine ⟨valid,?_⟩
  have shape := projection_topology_node original location protections index.toNat index node rfl present
  simpa only [Array.getElem?_eq_getElem valid,Option.getD_some] using shape

/-- Actual reciprocal Forest metadata makes every finite source-order unfolding
node-distinct. No unrolled traversal or GC success is assumed. -/
theorem order_properties (original : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (forest : Forest (source_normal_projection original location protections).topology)
    (shape : Shape) : shape.Valid original →
      (∀ index ∈ shape.order, Desc (source_normal_projection original location protections).topology shape.root.toNat index.toNat) ∧
      shape.order.Nodup := by
  let property := fun shape : Shape => shape.Valid original →
    (∀ index ∈ shape.order, Desc (source_normal_projection original location protections).topology shape.root.toNat index.toNat) ∧ shape.order.Nodup
  apply Shape.rec (motive_1 := property) (motive_2 := fun rows => ∀ shape ∈ rows, property shape)
  · intro index children childrenIH valid
    simp only [Shape.Valid] at valid
    obtain ⟨node,present,childrenEq,childValid⟩ := valid
    obtain ⟨rootValid,shapeEq⟩ := source_node original location protections index node present
    have childMember : ∀ child ∈ children, child.root.toNat ∈
        (source_normal_projection original location protections).topology.nodes[index.toNat].children := by
      intro child member
      rw [shapeEq]
      apply List.mem_map.mpr
      exact ⟨child.root,by rw [←childrenEq];exact List.mem_map.mpr ⟨child,member,rfl⟩,rfl⟩
    have childData := fun child member => childrenIH child member (childValid child member)
    have rootDistinct : (children.map (fun child => child.root.toNat)).Nodup := by
      have distinct := forest.childrenDistinct index.toNat rootValid
      rw [shapeEq] at distinct
      simpa only [←childrenEq,List.map_map,Function.comp_def] using distinct
    have descendants : ∀ query ∈ children.flatMap Shape.order,
        Desc (source_normal_projection original location protections).topology index.toNat query.toNat := by
      intro query member
      obtain ⟨child,inChildren,inChild⟩ := List.mem_flatMap.mp member
      obtain ⟨valid,edge⟩ := forest.childParent index.toNat rootValid child.root.toNat (childMember child inChildren)
      exact (Desc.step (Desc.refl index.toNat rootValid) valid edge).trans ((childData child inChildren).1 query inChild)
    have parentOutside : index ∉ children.flatMap Shape.order := by
      intro member
      obtain ⟨child,inChildren,inChild⟩ := List.mem_flatMap.mp member
      have lower := ((childData child inChildren).1 index inChild).rank_le forest
      obtain ⟨valid,edge⟩ := forest.childParent index.toNat rootValid child.root.toNat (childMember child inChildren)
      have higher := (forest.parents child.root.toNat valid index.toNat edge).2
      omega
    simp only [Shape.order,Shape.root]
    refine ⟨?_,?_⟩
    · intro query member
      rcases List.mem_append.mp member with nested | here
      · exact descendants query nested
      · have same : query = index := by simpa using here
        subst query;exact Desc.refl index.toNat rootValid
    · apply List.nodup_append.mpr
      refine ⟨?_,by simp,?_⟩
      · apply List.pairwise_flatMap.mpr
        refine ⟨fun child member => (childData child member).2,?_⟩
        apply (List.pairwise_map.mp rootDistinct).imp_of_mem
        intro left right leftMember rightMember different first inFirst second inSecond same
        apply siblings_disjoint forest index.toNat left.root.toNat right.root.toNat first.toNat rootValid
          (childMember left leftMember) (childMember right rightMember) different
        exact ⟨(childData left leftMember).1 first inFirst,by rw [same];exact (childData right rightMember).1 second inSecond⟩
      · intro query member other singleton same
        have equal : other = index := by simpa using singleton
        exact parentOutside (same.trans equal ▸ member)
  · intro shape member;simp at member
  · intro head tail headIH tailIH shape member
    rcases List.mem_cons.mp member with same | later
    · subst shape;exact headIH
    · exact tailIH shape later

/-- The raw source child-sum potential bounds the number of postorder nodes. -/
theorem order_bounded (original : BorrowTree) (weights : GeneralBorrowWildcardSubtreeData.Weights original)
    (shape : Shape) : shape.Valid original → shape.order.length ≤ weights.weight shape.root := by
  let property := fun shape : Shape => shape.Valid original → shape.order.length ≤ weights.weight shape.root
  apply Shape.rec (motive_1 := property) (motive_2 := fun rows => ∀ shape ∈ rows, property shape)
  · intro index children childrenIH valid
    simp only [Shape.Valid] at valid
    obtain ⟨node,present,childrenEq,childValid⟩ := valid
    have bound := weights.children index node present
    have sums := sum_mono children (fun child => child.order.length) (fun child => weights.weight child.root)
      (by intro child member;exact childrenIH child member (childValid child member))
    rw [←childrenEq,List.map_map] at bound
    simp only [Shape.order,List.length_append,List.length_singleton,List.length_flatMap,Shape.root]
    dsimp only [Function.comp_def] at bound
    omega
  · intro shape member;simp at member
  · intro head tail headIH tailIH shape member
    rcases List.mem_cons.mp member with same | later
    · subst shape;exact headIH
    · exact tailIH shape later

/-- Every present root of a finite reciprocal Forest yields an exact, distinct
original-metadata postorder Plan within the interpreter's unchanged source
counter budget. In particular no externally supplied Plan is needed. -/
theorem plan (original : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (forest : Forest (source_normal_projection original location protections).topology)
    (children : GeneralBorrowGraph.ChildNodes original) (root : UniIndex) (node : TreeNode)
    (present : original.nodes.get root = some node) :
    ∃ final count, GeneralBorrowGcDfsPlan.Plan original #[(root,0)] [] final count ∧ count ≤ original.nodes.size*2+1 := by
  let weights := GeneralBorrowWildcardForestWeights.of_forest original location protections forest
  let shape := unroll original original.nodes.size root
  have enough := GeneralBorrowWildcardForestWeights.bounded original location protections forest root
  have valid := unroll_valid original weights children original.nodes.size root node present enough
  have distinct := (order_properties original location protections forest shape valid).2
  have lengthBound := order_bounded original weights shape valid
  have rootEq : shape.root = root := unroll_root original original.nodes.size root
  rw [rootEq] at lengthBound
  change shape.order.length ≤ (GeneralBorrowWildcardForestWeights.of_forest original location protections forest).weight root at lengthBound
  refine ⟨shape.order.reverse,2*shape.order.length-1,?_,by omega⟩
  have actual := GeneralBorrowGcDfsShape.plan original shape valid distinct
  simpa only [rootEq] using actual

/-- The REAL source child-GC traversal completes on every present component of
an arbitrary finite reciprocal Forest. Canonical topology data constructs both
the schedule and its counter budget; no supplied Plan/success premise remains.
Final reciprocal topology and whole-root-list GC are separate obligations. -/
theorem children_complete_staged (original : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (forest : Forest (source_normal_projection original location protections).topology)
    (children : GeneralBorrowGraph.ChildNodes original) (root : UniIndex) (node : TreeNode)
    (present : original.nodes.get root = some node) (live : Array BorTag) :
    ∃ after final, source_gc_children original root live = ⟨after,.ok ()⟩ ∧
      GeneralBorrowGcDfsStage.Stage original final after ∧
      GeneralBorrowGcStrictChildren.Ranked (fun index => forest.rank index.toNat) after ∧
      after.nodes.size = original.nodes.size := by
  obtain ⟨final,count,schedule,budget⟩ := plan original location protections forest children root node present
  let rank := fun index : UniIndex => forest.rank index.toNat
  have ranked : GeneralBorrowGcStrictChildren.Ranked rank original := by
    intro index current lookup child member
    obtain ⟨valid,shapeEq⟩ := source_node original location protections index current lookup
    have childMember : child.toNat ∈ (source_normal_projection original location protections).topology.nodes[index.toNat].children := by
      rw [shapeEq]
      exact List.mem_map.mpr ⟨child,member,rfl⟩
    obtain ⟨childValid,edge⟩ := forest.childParent index.toNat valid child.toNat childMember
    exact (forest.parents child.toNat childValid index.toNat edge).2
  have stage : GeneralBorrowGcDfsStage.Stage original [] original :=
    ⟨by intro index outside;rfl,by intro index member;simp at member⟩
  obtain ⟨after,actual,finalStage,finalRank,capacity⟩ := GeneralBorrowGcDfsPlan.execute rank original original root live
    schedule original 0 stage ranked (by simpa using budget)
  refine ⟨after,final,?_,finalStage,finalRank,capacity⟩
  rw [GeneralBorrowGcWalker.children_equation,actual]

/-- Outcome-only interface to the staged completion result. -/
theorem children_complete (original : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (forest : Forest (source_normal_projection original location protections).topology)
    (children : GeneralBorrowGraph.ChildNodes original) (root : UniIndex) (node : TreeNode)
    (present : original.nodes.get root = some node) (live : Array BorTag) :
    ∃ after, source_gc_children original root live = ⟨after,.ok ()⟩ ∧
      after.nodes.size = original.nodes.size := by
  obtain ⟨after,_,actual,_,_,capacity⟩ := children_complete_staged original location protections forest children root node present live
  exact ⟨after,actual,capacity⟩

end
end DuplicatePrefix.GeneralBorrowGcDfsFormation
