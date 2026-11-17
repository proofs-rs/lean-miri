import duplicate_prefix.GeneralBorrowGcDfsPlan

namespace DuplicatePrefix.GeneralBorrowGcDfsShape
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowGcDfsPlan
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Pure finite source topology, in the original child-array order. -/
inductive Shape where
  | node (index : UniIndex) (children : List Shape)

def Shape.root : Shape → UniIndex | .node index _ => index

def Shape.order : Shape → List UniIndex
  | .node index children => children.flatMap Shape.order ++ [index]

def Shape.Valid (original : BorrowTree) : Shape → Prop
  | .node index children => ∃ node, original.nodes.get index = some node ∧
      children.map Shape.root = node.children.toList ∧ ∀ child ∈ children, child.Valid original

private def Disjoint (left right : List UniIndex) : Prop := ∀ index ∈ left, index ∉ right

private def TreeExec (original : BorrowTree) (shape : Shape) : Prop :=
  shape.Valid original → shape.order.Nodup → ∀ (stack : Array (UniIndex × Nat)) (processed final : List UniIndex) (rest : Nat),
    Disjoint shape.order processed →
    Plan original stack (shape.order.reverse ++ processed) final rest →
    Plan original (stack.push (shape.root,0)) processed final (2*shape.order.length-1+rest)

private def ChildrenExec (original : BorrowTree) (children : List Shape) : Prop :=
  (∀ child ∈ children, child.Valid original) → (children.flatMap Shape.order).Nodup →
  ∀ (index : UniIndex) (node : TreeNode) (stack : Array (UniIndex × Nat)) (cursor : Nat)
    (processed final : List UniIndex) (rest : Nat), original.nodes.get index = some node →
    cursor ≤ node.children.size → children.map Shape.root = node.children.toList.drop cursor →
    index ∉ processed → index ∉ children.flatMap Shape.order →
    Disjoint (children.flatMap Shape.order) processed →
    Plan original (stack.push (index,node.children.size)) ((children.flatMap Shape.order).reverse ++ processed) final rest →
    Plan original (stack.push (index,cursor)) processed final (2*(children.flatMap Shape.order).length+rest)

private theorem exec (original : BorrowTree) (shape : Shape) : TreeExec original shape := by
  apply Shape.rec (motive_1 := TreeExec original) (motive_2 := ChildrenExec original)
  · intro index children childrenIH valid distinct stack processed final rest disjoint continuation
    simp only [Shape.Valid] at valid
    simp only [Shape.order] at distinct disjoint continuation
    obtain ⟨node,present,childrenEq,childValid⟩ := valid
    have parts := List.nodup_append.mp distinct
    have parentNotChildren : index ∉ children.flatMap Shape.order := by
      intro inside
      exact parts.2.2 index inside index (by simp) rfl
    have parentNotProcessed : index ∉ processed := by
      exact fun inside => disjoint index (by simp) inside
    have childDisjoint : Disjoint (children.flatMap Shape.order) processed := by
      intro query member inside
      exact disjoint query (List.mem_append_left _ member) inside
    have finish : Plan original (stack.push (index,node.children.size))
        ((children.flatMap Shape.order).reverse ++ processed) final (rest+1) := by
      apply Plan.up stack index node.children.size node _ final rest present
      · intro member
        rcases List.mem_append.mp member with child | old
        · exact parentNotChildren (List.mem_reverse.mp child)
        · exact parentNotProcessed old
      · omega
      · intro child member
        have childRoot : child ∈ children.map Shape.root := by rw [childrenEq];exact member
        obtain ⟨childShape,inChildren,same⟩ := List.mem_map.mp childRoot
        have rootMember : childShape.root ∈ childShape.order := by cases childShape;simp [Shape.root,Shape.order]
        apply List.mem_append_left
        exact List.mem_reverse.mpr (List.mem_flatMap.mpr ⟨childShape,inChildren,by simpa only [same] using rootMember⟩)
      · simpa only [Shape.order,List.reverse_append,List.reverse_singleton,List.singleton_append,List.cons_append,List.nil_append] using continuation
    have result := childrenIH childValid parts.1 index node stack 0 processed final (rest+1) present
      (Nat.zero_le _) (by simpa using childrenEq) parentNotProcessed parentNotChildren childDisjoint finish
    change Plan original (stack.push (index,0)) processed final _
    have arithmetic : 2*(Shape.order (.node index children)).length-1+rest = 2*(children.flatMap Shape.order).length+(rest+1) := by
      simp only [Shape.order,List.length_append,List.length_singleton];omega
    rw [arithmetic]
    exact result
  · intro valid distinct index node stack cursor processed final rest present cursorBound childrenEq parentOutside childrenOutside disjoint continuation
    have cursorEq : cursor = node.children.size := by
      have lengths := congrArg List.length childrenEq
      simp only [List.map_nil,List.length_nil,List.length_drop,Array.length_toList] at lengths
      omega
    subst cursor
    simpa only [List.flatMap_nil,List.length_nil,Nat.mul_zero,Nat.zero_add,List.reverse_nil,List.nil_append] using continuation
  · intro head tail headIH tailIH valid distinct index node stack cursor processed final rest present cursorBound childrenEq parentOutside childrenOutside disjoint continuation
    have orders : (head :: tail).flatMap Shape.order = head.order ++ tail.flatMap Shape.order := rfl
    rw [orders] at distinct disjoint childrenOutside continuation ⊢
    have parts := List.nodup_append.mp distinct
    have nonempty : 0 < head.order.length := by cases head;simp [Shape.order]
    have cursorInside : cursor < node.children.size := by
      have lengths := congrArg List.length childrenEq
      simp only [List.map_cons,List.length_cons,List.length_map,List.length_drop,Array.length_toList] at lengths
      omega
    have childAt : node.children[cursor] = head.root := by
      have first := congrArg (fun rows : List UniIndex => rows.head?) childrenEq
      simpa only [List.map_cons,List.head?_cons,List.head?_drop,Array.getElem?_toList,Array.getElem?_eq_getElem cursorInside,Option.some.injEq] using first.symm
    have tailEq : tail.map Shape.root = node.children.toList.drop (cursor+1) := by
      have after := congrArg List.tail childrenEq
      simpa only [List.map_cons,List.tail_cons,List.tail_drop] using after
    have headDisjoint : Disjoint head.order processed := by
      intro query member inside;exact disjoint query (List.mem_append_left _ member) inside
    have tailDisjoint : Disjoint (tail.flatMap Shape.order) (head.order.reverse ++ processed) := by
      intro query member inside
      rcases List.mem_append.mp inside with earlier | old
      · exact parts.2.2 query (List.mem_reverse.mp earlier) query member rfl
      · exact disjoint query (List.mem_append_right _ member) old
    have parentAfter : index ∉ head.order.reverse ++ processed := by
      intro member
      rcases List.mem_append.mp member with earlier | old
      · exact childrenOutside (List.mem_append_left _ (List.mem_reverse.mp earlier))
      · exact parentOutside old
    have tailContinuation : Plan original (stack.push (index,node.children.size))
        ((tail.flatMap Shape.order).reverse ++ (head.order.reverse ++ processed)) final rest := by
      simpa only [List.reverse_append,List.append_assoc] using continuation
    have tailResult := tailIH (by intro child member;exact valid child (List.mem_cons_of_mem _ member)) parts.2.1
      index node stack (cursor+1) (head.order.reverse ++ processed) final rest present (by omega) tailEq parentAfter
      (by intro member;exact childrenOutside (List.mem_append_right _ member)) tailDisjoint tailContinuation
    have headResult := headIH (valid head (by simp)) parts.1 (stack.push (index,cursor+1)) processed final
      (2*(tail.flatMap Shape.order).length+rest) headDisjoint tailResult
    have down := Plan.down stack index cursor node processed final
      (2*head.order.length-1+(2*(tail.flatMap Shape.order).length+rest)) present parentOutside cursorInside
      (by simpa only [childAt] using headResult)
    have arithmetic : 2*(head.order ++ tail.flatMap Shape.order).length+rest =
        (2*head.order.length-1+(2*(tail.flatMap Shape.order).length+rest))+1 := by
      simp only [List.length_append];omega
    rw [arithmetic]
    exact down

/-- An exact source-order finite topology with no repeated nodes forms the real
DFS cursor Plan. This theorem constructs Plan, rather than assuming loop success. -/
theorem plan (original : BorrowTree) (shape : Shape) (valid : shape.Valid original) (distinct : shape.order.Nodup) :
    Plan original #[(shape.root,0)] [] shape.order.reverse (2*shape.order.length-1) := by
  have result := exec original shape valid distinct #[] [] shape.order.reverse 0 (by simp [Disjoint])
    (by simpa using Plan.done (original := original) shape.order.reverse)
  simpa using result

end DuplicatePrefix.GeneralBorrowGcDfsShape
