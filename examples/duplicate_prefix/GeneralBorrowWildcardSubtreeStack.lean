import duplicate_prefix.GeneralBorrowWildcardSubtreeData

namespace DuplicatePrefix.GeneralBorrowWildcardSubtreeStack
open Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

abbrev Task := UniIndex × Bool

def cost (weight : UniIndex → Nat) (task : Task) : Nat := if task.2 then 1 else 2*weight task.1

def potential (weight : UniIndex → Nat) (stack : Array Task) : Nat :=
  (stack.toList.map (cost weight)).sum

def Earlier (weight : UniIndex → Nat) (left right : Task) : Prop := left.2 = true → weight right.1 < weight left.1

def Ranked (weight : UniIndex → Nat) (stack : Array Task) : Prop := stack.toList.Pairwise (Earlier weight)

def expanded (baseStack : Array Task) (index : UniIndex) (children : Array UniIndex) : Array Task :=
  baseStack.push (index,true) ++ children.map (fun child => (child,false))

theorem potential_push (weight : UniIndex → Nat) (baseStack : Array Task) (task : Task) :
    potential weight (baseStack.push task) = potential weight baseStack + cost weight task := by
  simp [potential,Array.toList_push,List.map_append,List.sum_append]

theorem ranked_push (weight : UniIndex → Nat) (baseStack : Array Task) (task : Task) :
    Ranked weight (baseStack.push task) ↔ Ranked weight baseStack ∧ ∀ earlier ∈ baseStack.toList, Earlier weight earlier task := by
  simp [Ranked,Array.toList_push,List.pairwise_append]

/-- The actual dependent source child-push loop appends precisely one pending
previsit task per child, in the source order. -/
theorem children_loop (children : Array UniIndex) (stack : Array Task) :
    (forIn' children stack (fun child _ current => (pure (.yield (current.push (child,false))) : Id (ForInStep (Array Task))))) =
      stack ++ children.map (fun child => (child,false)) := by
  rw [Array.forIn'_pure_yield_eq_foldl]
  change children.attach.foldl (fun current child => current.push (child.val,false)) stack = _
  rw [Array.foldl_push_eq_append rfl]
  exact congrArg (fun rows => stack ++ rows) (Array.attach_map_val children (fun child => (child,false)))

private theorem double_sum (children : List UniIndex) (weight : UniIndex → Nat) :
    (children.map (fun child => 2*weight child)).sum = 2*(children.map weight).sum := by
  induction children with
  | nil => rfl
  | cons child rest ih => simp only [List.map_cons,List.sum_cons,ih];omega

theorem expanded_potential (weight : UniIndex → Nat) (baseStack : Array Task) (index : UniIndex) (children : Array UniIndex) :
    potential weight (expanded baseStack index children) = potential weight baseStack + 1 + 2*(children.toList.map weight).sum := by
  simp only [expanded,potential,Array.toList_append,Array.toList_push,Array.toList_map,List.map_append,List.map_map,List.sum_append]
  simp only [Function.comp_def,cost,Bool.false_eq_true,ite_false,ite_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
  rw [double_sum]

theorem expanded_ranked (weight : UniIndex → Nat) (baseStack : Array Task) (index : UniIndex) (children : Array UniIndex)
    (ranked : Ranked weight (baseStack.push (index,false)))
    (below : ∀ child ∈ children.toList, weight child < weight index) :
    Ranked weight (expanded baseStack index children) := by
  obtain ⟨baseStackRanked,earlier⟩ := (ranked_push weight baseStack (index,false)).mp ranked
  have parentRanked : Ranked weight (baseStack.push (index,true)) :=
    (ranked_push weight baseStack (index,true)).mpr ⟨baseStackRanked,earlier⟩
  unfold Ranked expanded
  rw [Array.toList_append]
  apply List.pairwise_append.mpr
  refine ⟨parentRanked,?_,?_⟩
  · rw [Array.toList_map]
    apply List.pairwise_map.mpr
    apply List.pairwise_of_forall
    intro left right
    simp [Earlier]
  · intro previous member later inChildren
    rw [Array.toList_map] at inChildren
    obtain ⟨child,childMember,same⟩ := List.mem_map.mp inChildren
    subst later
    rw [Array.toList_push,List.mem_append,List.mem_singleton] at member
    rcases member with previousMember | parent
    · intro held
      exact Nat.lt_trans (below child childMember) (earlier previous previousMember held)
    · subst previous
      intro _
      exact below child childMember

end DuplicatePrefix.GeneralBorrowWildcardSubtreeStack
