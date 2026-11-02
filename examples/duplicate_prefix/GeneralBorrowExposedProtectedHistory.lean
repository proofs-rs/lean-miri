import duplicate_prefix.GeneralBorrowProtectedMutableHistory
import duplicate_prefix.GeneralBorrowExposedPartitionState

namespace DuplicatePrefix.GeneralBorrowExposedProtectedHistory
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowPartitionState
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Actual root exposure may be mixed with every prior protected and
unprotected history action. No cache-coherence assertion is included. -/
inductive Action (bytes : UInt64) where
  | ordinary (request : GeneralBorrowProtectedMutableHistory.Action bytes)
  | exposeRoot

def Action.tags {bytes : UInt64} : Action bytes → List BorTag
  | .ordinary request => request.tags
  | .exposeRoot => []

def nextTree (tree : BorrowTree) (global : GlobalState) (parentTag : BorTag) (capacity : UInt64) : Action capacity → BorrowTree
  | .ordinary request => GeneralBorrowProtectedMutableHistory.nextTree tree global parentTag capacity request
  | .exposeRoot => (tree.exposeTag {} parentTag).tree

/-- Root exposure retains the actual global state; ordinary actions thread
their genuine registration/endCall transitions. -/
def nextGlobal (global : GlobalState) {capacity : UInt64} : Action capacity → GlobalState
  | .ordinary request => GeneralBorrowProtectedMutableHistory.nextGlobal global request
  | .exposeRoot => global

def Completed (tree : BorrowTree) (global : GlobalState) (parentTag : BorTag) (capacity : UInt64) : Action capacity → Prop
  | .ordinary request => GeneralBorrowProtectedMutableHistory.Completed tree global parentTag capacity request
  | .exposeRoot => (tree.exposeTag {} parentTag).outcome = .ok ()

/-- Root exposure and all earlier actions preserve the recurring State and
actual empty protector table; cache values remain unrestricted. -/
theorem advance (tree : BorrowTree) (global : GlobalState) (empty : global.protectedTags = {})
    (root : UniIndex) (capacity : UInt64) (parentTag : BorTag)
    (s : State tree root capacity) (tagged : s.node.tag = parentTag) (action : Action capacity)
    (fresh : ∀ tag ∈ action.tags, GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (room : tree.nodes.size+action.tags.length+4 ≤ 4294967295) :
    Completed tree global parentTag capacity action ∧
    (nextGlobal global action).protectedTags = {} ∧
    Nonempty {post : State (nextTree tree global parentTag capacity action) root capacity // post.node.tag = parentTag} ∧
    (nextTree tree global parentTag capacity action).nodes.size ≤ tree.nodes.size+action.tags.length ∧
    (∀ tag, tag ∉ action.tags → GeneralBorrowTagMap.Fresh tree.tagMapping tag →
      GeneralBorrowTagMap.Fresh (nextTree tree global parentTag capacity action).tagMapping tag) := by
  cases action with
  | ordinary request =>
    have facts := GeneralBorrowProtectedMutableHistory.advance tree global empty root capacity parentTag s tagged request fresh room
    exact facts
  | exposeRoot =>
    have facts := GeneralBorrowExposedPartitionState.expose_root tree root capacity s
    rw [tagged] at facts
    refine ⟨facts.1,empty,facts.2.1,?_,?_⟩
    · simpa only [nextTree,Action.tags,List.length_nil,Nat.add_zero] using (Nat.le_of_eq facts.2.2.1)
    · intro later unused initial
      change GeneralBorrowTagMap.Fresh (tree.exposeTag {} parentTag).tree.tagMapping later
      rw [facts.2.2.2]
      exact initial

def execute (tree : BorrowTree) (global : GlobalState) (parentTag : BorTag) (capacity : UInt64) : List (Action capacity) → BorrowTree × GlobalState
  | [] => (tree,global)
  | action :: rest => execute (nextTree tree global parentTag capacity action) (nextGlobal global action) parentTag capacity rest

def AllCompleted (tree : BorrowTree) (global : GlobalState) (parentTag : BorTag) (capacity : UInt64) : List (Action capacity) → Prop
  | [] => True
  | action :: rest => Completed tree global parentTag capacity action ∧
      AllCompleted (nextTree tree global parentTag capacity action) (nextGlobal global action) parentTag capacity rest

/-- Any finite mixture of real root exposures, closed protected mutable
lifetimes, accesses, constructors and collections preserves full root State.
Initial freshness and storage bounds suffice, without cache coherence or
intermediate operation-success premises. -/
theorem run (tree : BorrowTree) (global : GlobalState) (empty : global.protectedTags = {})
    (root : UniIndex) (capacity : UInt64) (parentTag : BorTag)
    (s : State tree root capacity) (tagged : s.node.tag = parentTag) (actions : List (Action capacity))
    (unique : (actions.flatMap Action.tags).Nodup)
    (fresh : ∀ tag ∈ actions.flatMap Action.tags, GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (room : tree.nodes.size+(actions.flatMap Action.tags).length+4 ≤ 4294967295) :
    AllCompleted tree global parentTag capacity actions ∧
    (execute tree global parentTag capacity actions).2.protectedTags = {} ∧
    Nonempty {post : State (execute tree global parentTag capacity actions).1 root capacity // post.node.tag = parentTag} ∧
    (execute tree global parentTag capacity actions).1.nodes.size ≤ tree.nodes.size+(actions.flatMap Action.tags).length ∧
    (∀ tag, tag ∉ actions.flatMap Action.tags → GeneralBorrowTagMap.Fresh tree.tagMapping tag →
      GeneralBorrowTagMap.Fresh (execute tree global parentTag capacity actions).1.tagMapping tag) := by
  induction actions generalizing tree global with
  | nil => exact ⟨True.intro,empty,⟨⟨s,tagged⟩⟩,Nat.le_refl _,fun _ _ initial => initial⟩
  | cons action rest ih =>
    have tags : ((action :: rest).flatMap Action.tags) = action.tags ++ rest.flatMap Action.tags := rfl
    rw [tags] at unique fresh room ⊢
    have separate := List.nodup_append.mp unique
    have first := advance tree global empty root capacity parentTag s tagged action
      (fun tag member => fresh tag (List.mem_append_left _ member)) (by rw [List.length_append] at room;omega)
    obtain ⟨⟨post,postTag⟩⟩ := first.2.2.1
    have nextFresh : ∀ tag ∈ rest.flatMap Action.tags,
        GeneralBorrowTagMap.Fresh (nextTree tree global parentTag capacity action).tagMapping tag := by
      intro tag member
      apply first.2.2.2.2 tag
      · intro earlier;exact separate.2.2 tag earlier tag member rfl
      · exact fresh tag (List.mem_append_right _ member)
    have nextRoom : (nextTree tree global parentTag capacity action).nodes.size+(rest.flatMap Action.tags).length+4 ≤ 4294967295 := by
      have bound := first.2.2.2.1
      rw [List.length_append] at room
      omega
    have tail := ih _ _ first.2.1 post postTag separate.2.1 nextFresh nextRoom
    refine ⟨⟨first.1,tail.1⟩,tail.2.1,tail.2.2.1,?_,?_⟩
    · have before := first.2.2.2.1
      have after := tail.2.2.2.1
      simp only [execute,List.length_append]
      change (execute (nextTree tree global parentTag capacity action) (nextGlobal global action) parentTag capacity rest).1.nodes.size ≤ _
      omega
    · intro tag unused initial
      have absent : tag ∉ action.tags ∧ tag ∉ rest.flatMap Action.tags := by
        simpa only [List.mem_append,not_or] using unused
      exact tail.2.2.2.2 tag absent.2 (first.2.2.2.2 tag absent.1 initial)

end DuplicatePrefix.GeneralBorrowExposedProtectedHistory
