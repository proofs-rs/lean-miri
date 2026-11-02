import duplicate_prefix.GeneralBorrowZeroSharedStage
import duplicate_prefix.GeneralBorrowZeroDefaultStage
import duplicate_prefix.GeneralBorrowDefaultActivatedStage
import duplicate_prefix.GeneralBorrowPartitionSharedStage
import duplicate_prefix.GeneralBorrowPartitionDefaultStage
import duplicate_prefix.GeneralBorrowPartitionGc
import duplicate_prefix.GeneralBorrowPartitionHistory

namespace DuplicatePrefix.GeneralBorrowPartitionGcHistory
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowPartitionState
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Actual in-bounds accesses, shared/default stages and full collection. -/
inductive Action (bytes : UInt64) where
  | access (request : GeneralBorrowPartitionHistory.Action bytes)
  | shared (tag : BorTag) (offset len : UInt64) (nonzero : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ bytes.toNat)
  | reserved (tag : BorTag) (offset len : UInt64) (nonzero : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ bytes.toNat)
  | sharedZero (tag : BorTag) (offset : UInt64) (bounds : offset.toNat ≤ bytes.toNat)
  | reservedZero (tag : BorTag) (offset : UInt64) (bounds : offset.toNat ≤ bytes.toNat)
  | activate (tag : BorTag) (offset len : UInt64) (nonzero : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ bytes.toNat)
  | collect (extraLive : Array BorTag)

def Action.tags {bytes : UInt64} : Action bytes → List BorTag
  | .shared tag .. => [tag]
  | .reserved tag .. => [tag]
  | .sharedZero tag .. => [tag]
  | .reservedZero tag .. => [tag]
  | .activate tag .. => [tag]
  | _ => []

def next (tree : BorrowTree) (parentTag : BorTag) (capacity : UInt64) : Action capacity → BorrowTree
  | .access request => (GeneralBorrowPartitionState.operation tree parentTag request.offset request.len request.kind).tree
  | .shared tag offset len _ _ => (GeneralBorrowPartitionSharedStage.operation tree parentTag tag offset len).tree
  | .reserved tag offset len _ _ => (GeneralBorrowPartitionDefaultStage.operation tree parentTag tag offset len).tree
  | .sharedZero tag offset _ => (GeneralBorrowZeroSharedStage.operation tree parentTag tag offset).tree
  | .reservedZero tag offset _ => (GeneralBorrowZeroDefaultStage.operation tree parentTag tag offset).tree
  | .activate tag offset len _ _ => (GeneralBorrowDefaultActivatedStage.operation tree parentTag tag offset len).tree
  | .collect live => (GeneralBorrowPartitionGc.operation tree parentTag live).tree

def Completed (tree : BorrowTree) (parentTag : BorTag) (capacity : UInt64) : Action capacity → Prop
  | .access request => (GeneralBorrowPartitionState.operation tree parentTag request.offset request.len request.kind).status = .Completed
  | .shared tag offset len _ _ =>
      (GeneralBorrowPartitionState.operation tree parentTag offset len .Read).status = .Completed ∧
      (GeneralBorrowPartitionSharedStage.operation tree parentTag tag offset len).outcome = .ok ()
  | .reserved tag offset len _ _ =>
      (GeneralBorrowPartitionState.operation tree parentTag offset len .Read).status = .Completed ∧
      (GeneralBorrowPartitionDefaultStage.operation tree parentTag tag offset len).outcome = .ok ()
  | .sharedZero tag offset _ =>
      (GeneralBorrowPartitionState.operation tree parentTag offset 0 .Read).status = .Completed ∧
      (GeneralBorrowZeroSharedStage.operation tree parentTag tag offset).outcome = .ok ()
  | .reservedZero tag offset _ =>
      (GeneralBorrowPartitionState.operation tree parentTag offset 0 .Read).status = .Completed ∧
      (GeneralBorrowZeroDefaultStage.operation tree parentTag tag offset).outcome = .ok ()
  | .activate tag offset len _ _ =>
      (GeneralBorrowPartitionState.operation tree parentTag offset len .Read).status = .Completed ∧
      (GeneralBorrowPartitionDefaultStage.operation tree parentTag tag offset len).outcome = .ok () ∧
      (GeneralBorrowDefaultActivatedStage.operation tree parentTag tag offset len).status = .Completed
  | .collect live => (GeneralBorrowPartitionGc.operation tree parentTag live).outcome = .ok ()

/-- One actual operation re-establishes the recurring state. Only initial tag
freshness and numeric storage headroom are supplied; completion is derived. -/
theorem advance (tree : BorrowTree) (root : UniIndex) (capacity : UInt64) (parentTag : BorTag)
    (s : State tree root capacity) (tagged : s.node.tag = parentTag) (action : Action capacity)
    (fresh : ∀ tag ∈ action.tags, GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (room : tree.nodes.size+action.tags.length+4 ≤ 4294967295) :
    Completed tree parentTag capacity action ∧
    Nonempty {post : State (next tree parentTag capacity action) root capacity // post.node.tag = parentTag} ∧
    (next tree parentTag capacity action).nodes.size ≤ tree.nodes.size+action.tags.length ∧
    (∀ tag, tag ∉ action.tags → GeneralBorrowTagMap.Fresh tree.tagMapping tag →
      GeneralBorrowTagMap.Fresh (next tree parentTag capacity action).tagMapping tag) := by
  cases action with
  | access request =>
    have facts := GeneralBorrowPartitionState.access tree root capacity s request.offset request.len request.kind request.bounds
    rw [tagged] at facts
    refine ⟨facts.1,facts.2.1,?_,?_⟩
    · simpa only [next,Action.tags,List.length_nil,Nat.add_zero] using (Nat.le_of_eq facts.2.2.1)
    · intro tag unused initial
      change GeneralBorrowTagMap.Fresh (GeneralBorrowPartitionState.operation tree parentTag request.offset request.len request.kind).tree.tagMapping tag
      rw [facts.2.2.2];exact initial
  | shared tag offset len nonzero bounds =>
    have headroom : tree.nodes.size+5 ≤ 4294967295 := by simpa [Action.tags,Nat.add_assoc] using room
    have facts := GeneralBorrowPartitionSharedStage.borrow tree root capacity s offset len nonzero bounds tag (fresh tag (by simp [Action.tags])) headroom
    rw [tagged] at facts
    refine ⟨⟨facts.1,facts.2.1⟩,facts.2.2.1,?_,?_⟩
    · simpa only [next,Action.tags,List.length_singleton] using facts.2.2.2.1
    · intro future unused initial
      exact facts.2.2.2.2 future (by intro same;apply unused;simpa [Action.tags,same]) initial
  | reserved tag offset len nonzero bounds =>
    have headroom : tree.nodes.size+5 ≤ 4294967295 := by simpa [Action.tags,Nat.add_assoc] using room
    have facts := GeneralBorrowPartitionDefaultStage.borrow tree root capacity s offset len nonzero bounds tag (fresh tag (by simp [Action.tags])) headroom
    rw [tagged] at facts
    refine ⟨⟨facts.1,facts.2.1⟩,facts.2.2.1,?_,?_⟩
    · simpa only [next,Action.tags,List.length_singleton] using facts.2.2.2.1
    · intro future unused initial
      exact facts.2.2.2.2 future (by intro same;apply unused;simpa [Action.tags,same]) initial
  | sharedZero tag offset bounds =>
    have headroom : tree.nodes.size+5 ≤ 4294967295 := by simpa [Action.tags,Nat.add_assoc] using room
    have facts := GeneralBorrowZeroSharedStage.borrow tree root capacity s tag (fresh tag (by simp [Action.tags])) headroom offset bounds
    rw [tagged] at facts
    refine ⟨⟨facts.1,facts.2.1⟩,facts.2.2.1,?_,?_⟩
    · simpa only [next,Action.tags,List.length_singleton] using facts.2.2.2.1
    · intro future unused initial
      exact facts.2.2.2.2 future (by intro same;apply unused;simp [Action.tags,same]) initial
  | reservedZero tag offset bounds =>
    have headroom : tree.nodes.size+5 ≤ 4294967295 := by simpa [Action.tags,Nat.add_assoc] using room
    have facts := GeneralBorrowZeroDefaultStage.borrow tree root capacity s tag (fresh tag (by simp [Action.tags])) headroom offset bounds
    rw [tagged] at facts
    refine ⟨⟨facts.1,facts.2.1⟩,facts.2.2.1,?_,?_⟩
    · simpa only [next,Action.tags,List.length_singleton] using facts.2.2.2.1
    · intro future unused initial
      exact facts.2.2.2.2 future (by intro same;apply unused;simp [Action.tags,same]) initial
  | activate tag offset len nonzero bounds =>
    have headroom : tree.nodes.size+5 ≤ 4294967295 := by simpa [Action.tags,Nat.add_assoc] using room
    have facts := GeneralBorrowDefaultActivatedStage.borrow tree root capacity s offset len nonzero bounds tag (fresh tag (by simp [Action.tags])) headroom
    rw [tagged] at facts
    refine ⟨⟨facts.1,facts.2.1,facts.2.2.1⟩,facts.2.2.2.1,?_,?_⟩
    · simpa only [next,Action.tags,List.length_singleton] using facts.2.2.2.2.1
    · intro future unused initial
      exact facts.2.2.2.2.2 future (by intro same;apply unused;simp [Action.tags,same]) initial
  | collect live =>
    have facts := GeneralBorrowPartitionGc.collect tree root capacity s live
    rw [tagged] at facts
    refine ⟨facts.1,facts.2.1,?_,?_⟩
    · simpa only [next,Action.tags,List.length_nil,Nat.add_zero] using (Nat.le_of_eq facts.2.2.1)
    · intro tag unused initial;exact facts.2.2.2 tag initial

def execute (tree : BorrowTree) (parentTag : BorTag) (capacity : UInt64) : List (Action capacity) → BorrowTree
  | [] => tree
  | action :: rest => execute (next tree parentTag capacity action) parentTag capacity rest

def AllCompleted (tree : BorrowTree) (parentTag : BorTag) (capacity : UInt64) : List (Action capacity) → Prop
  | [] => True
  | action :: rest => Completed tree parentTag capacity action ∧
      AllCompleted (next tree parentTag capacity action) parentTag capacity rest

/-- Arbitrarily many real partial-range Reads/Writes, shared/default stages, child Write activation, zero constructors and GCs
may be interleaved. Distinct initially fresh tags and conservative UInt32 storage
headroom suffice; no intermediate state or operation-success premise is supplied. -/
theorem run (tree : BorrowTree) (root : UniIndex) (capacity : UInt64) (parentTag : BorTag)
    (s : State tree root capacity) (tagged : s.node.tag = parentTag) (actions : List (Action capacity))
    (unique : (actions.flatMap Action.tags).Nodup)
    (fresh : ∀ tag ∈ actions.flatMap Action.tags, GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (room : tree.nodes.size+(actions.flatMap Action.tags).length+4 ≤ 4294967295) :
    AllCompleted tree parentTag capacity actions ∧
    Nonempty {post : State (execute tree parentTag capacity actions) root capacity // post.node.tag = parentTag} ∧
    (execute tree parentTag capacity actions).nodes.size ≤ tree.nodes.size+(actions.flatMap Action.tags).length ∧
    (∀ tag, tag ∉ actions.flatMap Action.tags → GeneralBorrowTagMap.Fresh tree.tagMapping tag →
      GeneralBorrowTagMap.Fresh (execute tree parentTag capacity actions).tagMapping tag) := by
  induction actions generalizing tree with
  | nil => exact ⟨True.intro,⟨⟨s,tagged⟩⟩,Nat.le_refl _,fun _ _ initial => initial⟩
  | cons action rest ih =>
    have tags : ((action :: rest).flatMap Action.tags) = action.tags ++ rest.flatMap Action.tags := rfl
    rw [tags] at unique fresh room ⊢
    have separate := List.nodup_append.mp unique
    have first := advance tree root capacity parentTag s tagged action
      (fun tag member => fresh tag (List.mem_append_left _ member)) (by rw [List.length_append] at room;omega)
    obtain ⟨⟨post,postTag⟩⟩ := first.2.1
    have nextFresh : ∀ tag ∈ rest.flatMap Action.tags,
        GeneralBorrowTagMap.Fresh (next tree parentTag capacity action).tagMapping tag := by
      intro tag member
      apply first.2.2.2 tag
      · intro earlier;exact separate.2.2 tag earlier tag member rfl
      · exact fresh tag (List.mem_append_right _ member)
    have nextRoom : (next tree parentTag capacity action).nodes.size+(rest.flatMap Action.tags).length+4 ≤ 4294967295 := by
      have bound := first.2.2.1
      rw [List.length_append] at room
      omega
    have tail := ih _ post postTag separate.2.1 nextFresh nextRoom
    refine ⟨⟨first.1,tail.1⟩,tail.2.1,?_,?_⟩
    · have before := first.2.2.1
      have after := tail.2.2.1
      simp only [execute,List.length_append]
      change (execute (next tree parentTag capacity action) parentTag capacity rest).nodes.size ≤ _
      omega
    · intro tag unused initial
      have absent : tag ∉ action.tags ∧ tag ∉ rest.flatMap Action.tags := by
        simpa only [List.mem_append,not_or] using unused
      exact tail.2.2.2 tag absent.2 (first.2.2.2 tag absent.1 initial)

end DuplicatePrefix.GeneralBorrowPartitionGcHistory
