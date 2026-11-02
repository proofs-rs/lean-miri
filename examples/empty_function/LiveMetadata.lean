import empty_function.RawResources
namespace EmptyFunction.LiveMetadata
open Miri Miri.Memory Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Liveness excludes the dead-metadata branch using the actual registry
query order. No numeric resource bound is involved. -/
theorem not_dead {K : Type} (memory : MemoryState Provenance BorrowTree K) (id : AllocId)
    (live : memory.isAllocLive id = true) (info : AllocationInfo)
    (metadata : memory.getAllocInfo id = .ok info) : info.kind ≠ .dead := by
  unfold MemoryState.getAllocInfo at metadata
  cases located : memory.live.find? (fun row => row.1 == id) with
  | some row =>
    simp only [located,pure,Except.pure] at metadata
    cases metadata
    simp
  | none =>
    simp only [located] at metadata
    by_cases function : memory.hasFunctionPointer id = true
    · simp only [function,↓reduceIte,pure,Except.pure] at metadata
      cases metadata
      simp
    · simp only [function] at metadata
      by_cases va : memory.hasVaListId id = true
      · unfold MemoryState.hasVaListId at va
        simp only [va,↓reduceIte,pure,Except.pure] at metadata
        cases metadata
        simp
      · have noVa : memory.hasVaListId id = false := Bool.eq_false_iff.mpr va
        unfold MemoryState.hasVaListId at va
        simp only [va,Bool.false_eq_true,↓reduceIte] at metadata
        cases descriptor : memory.findGlobal? id with
        | none =>
          have noLive : memory.live.any (fun row => row.1 == id) = false :=
            Array.any_eq_false'.mpr (Array.find?_eq_none.mp located)
          have noExtra : memory.hasExtraFunctionId id = false := by
            apply Bool.eq_false_iff.mpr
            intro extra
            apply function
            unfold MemoryState.hasFunctionPointer
            unfold MemoryState.hasExtraFunctionId at extra
            simp only [extra,Bool.true_or]
          have noGlobal : memory.hasGlobalId id = false := by
            unfold MemoryState.hasGlobalId
            unfold MemoryState.findGlobal? at descriptor
            exact KeyedArray.contains_false_of_find_none _ _ descriptor
          change (memory.live.any (fun row => row.1 == id) || memory.hasExtraFunctionId id || memory.hasVaListId id ||
            memory.hasGlobalId id) = true at live
          rw [noLive,noExtra,noVa,noGlobal] at live
          cases live
        | some global =>
          simp only [descriptor] at metadata
          cases kind : global.kind <;> simp only [kind,pure,Except.pure] at metadata <;> cases metadata <;> simp
end EmptyFunction.LiveMetadata
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.LiveMetadata.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved live metadata axiom {dependency} in {name}"
