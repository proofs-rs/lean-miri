import duplicate_prefix.GeneralBorrowSharedGeneratorSeed
import duplicate_prefix.GeneralBorrowSharedGeneratorReadyRepeat
namespace DuplicatePrefix.GeneralBorrowAllocatedSharedHistory
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshMetadataChildShared DuplicatePrefix.GeneralBorrowSharedGeneratorStep
open DuplicatePrefix.GeneralBorrowSharedGeneratorReadyRepeat
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- Form the initial state from actual allocation creation, then derive every
Read/shared append and the final Ready family. No graph, permission, ownership,
cache, vacant Clean, intermediate Input/state or operation success is an input.
The concrete tag supply and UInt32 allocator headroom are explicit resources.
This is a Lean borrow-protocol history, not yet whole invocation safety. -/
theorem generate (rootTag childTag : BorTag) (different : rootTag ≠ childTag)
    (tags : List BorTag) (unique : tags.Nodup) (rootUnused : rootTag ∉ tags)
    (childUnused : childTag ∉ tags) (room : 1+tags.length ≤ 4294967295) :
    let seed := GeneralBorrowSharedGeneratorSeed.input rootTag childTag different
    ∃ final finalLocation keys, GeneralBorrowSharedGeneratorRepeat.Run seed tags final ∧
      State final finalLocation ∧ finalLocation.exposedCache = {} ∧
      ReadyKeys final finalLocation keys ∧ (keys.map Prod.snd).Nodup ∧ keys.length = tags.length := by
  let seed := GeneralBorrowSharedGeneratorSeed.input rootTag childTag different
  have fresh : ∀ tag ∈ tags, GeneralBorrowTagMap.Fresh seed.tree.tagMapping tag := by
    intro tag member row present
    change row ∈ (GeneralBorrowSharedGeneratorSeed.tree rootTag).tagMapping.mapping at present
    rw [GeneralBorrowSharedGeneratorSeed.tree_eq] at present
    have same := Array.mem_singleton.mp present
    subst row
    intro equal
    have sameTag : rootTag = tag := equal
    exact rootUnused (sameTag.symm ▸ member)
  have capacity : seed.tree.tagMapping.mapping.size+tags.length ≤ 4294967295 := by
    change (GeneralBorrowSharedGeneratorSeed.tree rootTag).tagMapping.mapping.size+tags.length ≤ 4294967295
    rw [GeneralBorrowSharedGeneratorSeed.tree_eq]
    exact room
  obtain ⟨final,finalLocation,keys,history,good,cache,ready,distinct,length⟩ :=
    iterate tags seed GeneralBorrowSharedGeneratorSeed.location
      (GeneralBorrowSharedGeneratorSeed.state rootTag childTag different) []
      (by simp [ReadyKeys]) (by simp) fresh unique childUnused capacity
  exact ⟨final,finalLocation,keys,history,good,cache.trans GeneralBorrowSharedGeneratorSeed.cache_empty,
    ready,distinct,by simpa only [List.length_nil,Nat.zero_add] using length⟩
end DuplicatePrefix.GeneralBorrowAllocatedSharedHistory
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowAllocatedSharedHistory.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved allocated shared history dependency {dependency}"
