import duplicate_prefix.GeneralBorrowTagMap
namespace DuplicatePrefix.GeneralBorrowFreshReuseMap
open Miri.Memory Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 300000

/-- No active key currently designates the reusable slot. Being present in the
free stack alone does not imply this invariant in the executable semantics. -/
def Inactive (mapping : UniKeyMap BorTag) (index : UniIndex) : Prop :=
  ∀ entry ∈ mapping.mapping, entry.2 ≠ index

set_option autoImplicit false in
/-- Explicit metadata required for consuming one free index. Node vacancy,
absence of stale child references and per-location cleanup are independent
caller obligations; this record does not silently assert them. -/
structure Available (mapping : UniKeyMap BorTag) (index : UniIndex) : Prop where
  back : mapping.deassigned.back? = some index
  inactive : Inactive mapping index

/-- The real reusable-index insertion succeeds, pops exactly the free-stack
entry and preserves every old key lookup. The new active slot designates only
the fresh tag; no map-length/node-length alignment or u32 conversion is needed. -/
theorem insert_reuse (mapping : UniKeyMap BorTag) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh mapping tag) (index : UniIndex) (available : Available mapping index) :
    let next : UniKeyMap BorTag := ⟨mapping.mapping.push (tag,index),mapping.deassigned.pop⟩
    mapping.insert tag = .Inserted next index ∧ next.get tag = some index ∧
      (∀ query, tag ≠ query → next.get query = mapping.get query) ∧
      (∀ entry ∈ next.mapping, entry.2 = index → entry.1 = tag) ∧
      next.mapping.size = mapping.mapping.size+1 ∧ next.deassigned = mapping.deassigned.pop := by
  dsimp only
  refine ⟨GeneralBorrowTagMap.insert_free mapping tag fresh index available.back,
    GeneralBorrowTagMap.pushed_get_new mapping tag fresh index _,?_,?_,by simp,rfl⟩
  · intro query different
    exact GeneralBorrowTagMap.pushed_get_old mapping tag query different index _
  · intro entry member same
    rcases Array.mem_push.mp member with old | new
    · exact False.elim (available.inactive entry old same)
    · cases new
      rfl
end DuplicatePrefix.GeneralBorrowFreshReuseMap
#print axioms DuplicatePrefix.GeneralBorrowFreshReuseMap.insert_reuse
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshReuseMap." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved reusable tag metadata dependency {dependency}"
