import duplicate_prefix.GeneralBorrowProtectedMutableHistoryStage
import duplicate_prefix.GeneralBorrowPartitionGcHistory

namespace DuplicatePrefix.GeneralBorrowProtectedMutableHistory
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowPartitionState
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Closed strong-protector lifetimes may be mixed with every existing root
access, shared/default/zero constructor, activation and collection action. -/
inductive Action (bytes : UInt64) where
  | ordinary (request : GeneralBorrowPartitionGcHistory.Action bytes)
  | lifetime (tag : BorTag) (offset len : UInt64) (nonzero : len ≠ 0)
      (bounds : offset.toNat+len.toNat ≤ bytes.toNat) (allocation : AllocId)

def Action.tags {bytes : UInt64} : Action bytes → List BorTag
  | .ordinary request => request.tags
  | .lifetime tag .. => [tag]

def nextTree (tree : BorrowTree) (global : GlobalState) (parentTag : BorTag) (capacity : UInt64) : Action capacity → BorrowTree
  | .ordinary request => GeneralBorrowPartitionGcHistory.next tree parentTag capacity request
  | .lifetime tag offset len _ _ allocation =>
      (GeneralBorrowProtectedMutableLifecycle.released tree parentTag tag offset len global allocation).tree

/-- The source global state is actually threaded through registrations and
matching endCall operations, rather than reset to an abstract empty map. -/
def nextGlobal (global : GlobalState) {capacity : UInt64} : Action capacity → GlobalState
  | .ordinary _ => global
  | .lifetime tag _ _ _ _ allocation =>
      (GeneralBorrowProtectedMutableRelease.registration global allocation tag).1.endCall
        (GeneralBorrowProtectedMutableRelease.registration global allocation tag).2

def Completed (tree : BorrowTree) (global : GlobalState) (parentTag : BorTag) (capacity : UInt64) : Action capacity → Prop
  | .ordinary request => GeneralBorrowPartitionGcHistory.Completed tree parentTag capacity request
  | .lifetime tag offset len _ _ allocation =>
      (GeneralBorrowProtectedMutableStage.read tree parentTag tag offset len global allocation).status = .Completed ∧
      (GeneralBorrowProtectedMutableStage.child tree parentTag tag offset len global allocation).outcome = .ok () ∧
      (GeneralBorrowProtectedMutableLifecycle.write tree parentTag tag offset len global allocation).status = .Completed ∧
      (GeneralBorrowProtectedMutableLifecycle.released tree parentTag tag offset len global allocation).status = .Released

/-- A complete real protected lifetime restores the recurring invariant and
empty actual global protector table before the following operation. -/
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
    have facts := GeneralBorrowPartitionGcHistory.advance tree root capacity parentTag s tagged request fresh room
    exact ⟨facts.1,empty,facts.2.1,facts.2.2.1,facts.2.2.2⟩
  | lifetime tag offset len nonzero bounds allocation =>
    have headroom : tree.nodes.size+5 ≤ 4294967295 := by simpa [Action.tags,Nat.add_assoc] using room
    have facts := GeneralBorrowProtectedMutableHistoryStage.borrow tree root capacity s offset len nonzero bounds tag
      (fresh tag (by simp [Action.tags])) headroom global empty allocation
    rw [tagged] at facts
    obtain ⟨readDone,reserveDone,writeDone,releaseDone,endDone,post,growth,future⟩ := facts
    refine ⟨⟨readDone,reserveDone,writeDone,releaseDone⟩,endDone,post,?_,?_⟩
    · simpa only [nextTree,Action.tags,List.length_singleton] using growth
    · intro later unused initial
      exact future later (by intro same;apply unused;simp [Action.tags,same]) initial

def execute (tree : BorrowTree) (global : GlobalState) (parentTag : BorTag) (capacity : UInt64) : List (Action capacity) → BorrowTree × GlobalState
  | [] => (tree,global)
  | action :: rest => execute (nextTree tree global parentTag capacity action) (nextGlobal global action) parentTag capacity rest

def AllCompleted (tree : BorrowTree) (global : GlobalState) (parentTag : BorTag) (capacity : UInt64) : List (Action capacity) → Prop
  | [] => True
  | action :: rest => Completed tree global parentTag capacity action ∧
      AllCompleted (nextTree tree global parentTag capacity action) (nextGlobal global action) parentTag capacity rest

/-- Arbitrary finite partial-range closed protected mutable lifetimes,
interleaved with all prior history actions, execute successfully from root State.
Inputs contain only ranges, fresh distinct tags, numeric headroom and initially
empty global protector resources; no intermediate operation success is assumed. -/
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

end DuplicatePrefix.GeneralBorrowProtectedMutableHistory
