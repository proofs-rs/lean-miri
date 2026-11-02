import duplicate_prefix.GeneralBorrowSharedGeneratorReadyRepeat
import duplicate_prefix.GeneralBorrowBoundedExposure
namespace DuplicatePrefix.GeneralBorrowBoundedGeneratedExposure
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshMetadataChildShared DuplicatePrefix.GeneralBorrowSharedGeneratorStep
open DuplicatePrefix.GeneralBorrowExposeReadFold DuplicatePrefix.GeneralBorrowExposureHistoryBounds
open DuplicatePrefix.GeneralBorrowBoundedExposure
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- Protocol accounting: initial cache witness allowance, two real borrow
operations per generated child (Read, append), one real exposure per child,
and one reserved virtual-root classification charge. Not MIR instruction count. -/
def historyLength (initialBudget generated : Nat) : Nat :=
  initialBudget + 2*generated + generated + 1

/-- Construct real shared siblings, recover their Ready requests internally,
then expose them using the actual source fold. Every exposure prefix completes
and has Lean/Rust-compatible cache arithmetic under historyLength<65536.
Initial single-root State/cache data, fresh tags and allocator capacity remain
explicit; arbitrary valid Rust histories and whole invocation safety are NOT
claimed. No generated nodes, requests, poststates or completion premises enter. -/
theorem generate_expose (tags : List BorTag) (input : Input) (location : LocationTree)
    (good : State input location)
    (fresh : ∀ tag ∈ tags, GeneralBorrowTagMap.Fresh input.tree.tagMapping tag)
    (distinct : tags.Nodup) (current : input.newTag ∉ tags)
    (room : input.tree.tagMapping.mapping.size+tags.length ≤ 4294967295)
    (protections : ProtectedTags) (budget : Nat) (bounded : Within location.exposedCache budget)
    (short : historyLength budget tags.length < 65536) :
    ∃ final finalLocation requests,
      GeneralBorrowSharedGeneratorRepeat.Run input tags final ∧ State final finalLocation ∧
      finalLocation.exposedCache = location.exposedCache ∧ requests.length = tags.length ∧
      (run protections requests final.tree).outcome = .ok () ∧
      ∀ before remaining, requests = before ++ remaining →
        (run protections before final.tree).outcome = .ok () ∧
        ∃ exposedLocation, (run protections before final.tree).tree.locations =
          DuplicatePrefix.RangeMapNonempty.homogeneous 1 exposedLocation ∧
          Within exposedLocation.exposedCache (budget+before.length) ∧ Compatible exposedLocation.exposedCache := by
  obtain ⟨final,finalLocation,keys,history,finalGood,cache,readyKeys,uniqueKeys,lengthKeys⟩ :=
    GeneralBorrowSharedGeneratorReadyRepeat.iterate tags input location good [] (by simp [GeneralBorrowSharedGeneratorReadyRepeat.ReadyKeys])
      (by simp) fresh distinct current room
  obtain ⟨requests,leaves,ready⟩ :=
    GeneralBorrowSharedGeneratorReadyRepeat.requests_exist final finalLocation keys readyKeys
  have length : requests.length = tags.length := by
    have same : requests.length = keys.length := by simpa only [List.length_map] using congrArg List.length leaves
    simpa only [List.length_nil,Nat.zero_add] using same.trans lengthKeys
  have requestUnique : (requests.map Request.leaf).Nodup := by rw [leaves];exact uniqueKeys
  have finalBound : Within finalLocation.exposedCache budget := by rw [cache];exact bounded
  have shortExposures : budget+requests.length+1 < 65536 := by
    rw [length]
    unfold historyLength at short
    omega
  have complete := run_safe_arithmetic requests final.tree finalLocation 1 final.parent final.parentNode protections budget
    finalGood.locations ready requestUnique finalBound shortExposures
  have prefixes := all_prefixes requests final.tree finalLocation 1 final.parent final.parentNode protections budget
    finalGood.locations ready requestUnique finalBound shortExposures
  exact ⟨final,finalLocation,requests,history,finalGood,cache,length,complete.1,prefixes⟩

/-- Empty initial caches need no caller-supplied numeric budget. The generated
requests and every operation completion remain conclusions of generate_expose. -/
theorem generate_expose_empty (tags : List BorTag) (input : Input) (location : LocationTree)
    (good : State input location)
    (fresh : ∀ tag ∈ tags, GeneralBorrowTagMap.Fresh input.tree.tagMapping tag)
    (distinct : tags.Nodup) (current : input.newTag ∉ tags)
    (room : input.tree.tagMapping.mapping.size+tags.length ≤ 4294967295)
    (protections : ProtectedTags) (empty : location.exposedCache = {})
    (short : historyLength 0 tags.length < 65536) :
    ∃ final finalLocation requests,
      GeneralBorrowSharedGeneratorRepeat.Run input tags final ∧ State final finalLocation ∧
      finalLocation.exposedCache = location.exposedCache ∧ requests.length = tags.length ∧
      (run protections requests final.tree).outcome = .ok () ∧
      ∀ before remaining, requests = before ++ remaining →
        (run protections before final.tree).outcome = .ok () ∧
        ∃ exposedLocation, (run protections before final.tree).tree.locations =
          DuplicatePrefix.RangeMapNonempty.homogeneous 1 exposedLocation ∧
          Within exposedLocation.exposedCache before.length ∧ Compatible exposedLocation.exposedCache := by
  have bounded : Within location.exposedCache 0 := by rw [empty];exact empty_within
  simpa only [Nat.zero_add] using generate_expose tags input location good fresh distinct current room protections 0 bounded short
end DuplicatePrefix.GeneralBorrowBoundedGeneratedExposure
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowBoundedGeneratedExposure.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved bounded generated exposure dependency {dependency}"
