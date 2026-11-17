import duplicate_prefix.GeneralBorrowReusableHistory

namespace DuplicatePrefix.GeneralBorrowReusableGeneration
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowReusableStar DuplicatePrefix.GeneralBorrowReusableHistory
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Construct the recurring invariant from the real allocation constructor. The
second tag is merely a distinct resource for the later invocation. -/
def seed (capacity : UInt64) (nonzero : capacity ≠ 0) (rootTag tag : BorTag)
    (different : rootTag ≠ tag) :
    State (BorrowTree.new rootTag (Size.ofBytes capacity)) GeneralBorrowFullSharedSeed.root capacity :=
  of_generated (GeneralBorrowFullSharedSeed.input capacity nonzero rootTag tag different)
    GeneralBorrowFullSharedSeed.location (GeneralBorrowFullSharedSeed.state capacity nonzero rootTag tag different)
    (GeneralBorrowGeneratedStarShape.seed_star capacity nonzero rootTag tag different)
    (GeneralBorrowGcAllocator.initial rootTag (Size.ofBytes capacity))
    (by change 1+4 ≤ 4294967295;omega)

theorem seed_fresh (capacity : UInt64) (nonzero : capacity ≠ 0) (rootTag tag : BorTag)
    (different : rootTag ≠ tag) :
    GeneralBorrowTagMap.Fresh (BorrowTree.new rootTag (Size.ofBytes capacity)).tagMapping tag := by
  change GeneralBorrowTagMap.Fresh (GeneralBorrowFullSharedSeed.tree capacity nonzero rootTag).tagMapping tag
  rw [GeneralBorrowFullSharedSeed.tree_eq]
  intro row member
  have same := Array.mem_singleton.mp member
  subst row
  exact different

set_option autoImplicit false in
/-- All borrow-state facts and completed history are outputs. The physical
caller is supplied later and must use this actual final tree. -/
structure Generated (capacity : UInt64) (rootTag tag : BorTag) (actions : List Action)
    (reserve : Fin 5 → BorTag) where
  state : State (execute (BorrowTree.new rootTag (Size.ofBytes capacity)) rootTag capacity actions)
    GeneralBorrowFullSharedSeed.root capacity
  completed : AllCompleted (BorrowTree.new rootTag (Size.ofBytes capacity)) rootTag capacity actions
  tagged : state.node.tag = rootTag
  fresh : GeneralBorrowTagMap.Fresh (execute (BorrowTree.new rootTag (Size.ofBytes capacity)) rootTag capacity actions).tagMapping tag
  reserved : ∀ i, GeneralBorrowTagMap.Fresh (execute (BorrowTree.new rootTag (Size.ofBytes capacity)) rootTag capacity actions).tagMapping (reserve i)

/-- Actual allocation and an arbitrary finite mix of full-slice root Reads,
shared append/reuse and full GC establish call-entry resources. Only the tag
supply and conservative storage budget are external; no intermediate graph,
permission, allocator invariant, successful operation or final Data is assumed. -/
noncomputable def generate (capacity : UInt64) (nonzero : capacity ≠ 0) (rootTag tag : BorTag)
    (different : rootTag ≠ tag) (actions : List Action)
    (unique : (actions.flatMap Action.tags).Nodup)
    (rootUnused : rootTag ∉ actions.flatMap Action.tags)
    (tagUnused : tag ∉ actions.flatMap Action.tags)
    (reserve : Fin 5 → BorTag)
    (reserved : ∀ i, reserve i ∉ rootTag :: actions.flatMap Action.tags)
    (room : 1+(actions.flatMap Action.tags).length+4 ≤ 4294967295) :
    Generated capacity rootTag tag actions reserve := by
  let initial := seed capacity nonzero rootTag tag different
  have initialTag : initial.node.tag = rootTag := rfl
  have fresh : ∀ nextTag ∈ actions.flatMap Action.tags,
      GeneralBorrowTagMap.Fresh (BorrowTree.new rootTag (Size.ofBytes capacity)).tagMapping nextTag := by
    intro nextTag member
    exact seed_fresh capacity nonzero rootTag nextTag (fun same => rootUnused (same ▸ member))
  have budget : (BorrowTree.new rootTag (Size.ofBytes capacity)).nodes.size+
      (actions.flatMap Action.tags).length+4 ≤ 4294967295 := by
    change (GeneralBorrowFullSharedSeed.tree capacity nonzero rootTag).nodes.size+_+4 ≤ _
    rw [GeneralBorrowFullSharedSeed.tree_eq]
    exact room
  have history := run _ GeneralBorrowFullSharedSeed.root capacity rootTag initial initialTag actions unique fresh budget
  let post := Classical.choice history.2.1
  exact ⟨post.val,history.1,post.property,
    history.2.2.2 tag tagUnused (seed_fresh capacity nonzero rootTag tag different),
    fun i => history.2.2.2 (reserve i) (fun member => reserved i (List.mem_cons_of_mem _ member))
      (seed_fresh capacity nonzero rootTag (reserve i) (fun same => reserved i (by simp [same])))⟩

end DuplicatePrefix.GeneralBorrowReusableGeneration
