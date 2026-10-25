import Lean
import Miri.Concurrency.WeakMemory

open Miri.Concurrency
open Lean Elab Tactic

private def findUniqueSelectorName (suffix : String) : TacticM Name := do
  let env ← getEnv
  let candidates := env.constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith suffix then some name else none
  match candidates with
  | [name] => pure name
  | _ => throwError m!"expected one private selector `{suffix}`, found {candidates.length}"

-- The exact source-shaped buffer requested for this regression: the initial
-- value is 0, then one SeqCst store writes 1.
private def oneSeqCstStore (storeIndex : VectorIdx) (storeClock syncClock : VClock) :
    StoreBuffer Nat :=
  (StoreBuffer.new (some 0)).storeImpl 1 storeIndex storeClock true syncClock

elab "simp_sc_selector" : tactic => do
  let helpers ← [
    ".StoreBuffer.indexedEntries",
    ".StoreBuffer.reverseIndexed",
    ".StoreBuffer.candidatePrefix",
    ".StoreBuffer.filterSeqCst",
    ".StoreBuffer.markBeforeSeqCstStore"
  ].mapM findUniqueSelectorName
  let helperIds := helpers.toArray.map mkIdent
  let generated ← `(tactic| simp [StoreBuffer.fetchChoices, StoreBuffer.storeImpl,
    oneSeqCstStore, StoreBuffer.entries,
    StoreBuffer.new, StoreBuffer.blocksEarlier, VClock.index, VTimestamp.ZERO,
    VTimestamp.time, STORE_BUFFER_LIMIT,
    $[$helperIds:ident],*])
  evalTactic generated

/-- Every SeqCst load after the initial value and one SeqCst store chooses
exactly the newly written value, independent of thread indices and clocks. -/
theorem initial_sc_store_load_selects_newest
    (storeIndex : VectorIdx) (storeClock : VClock) (syncClock : VClock)
    (loadClocks : ThreadClockSet) :
    (StoreBuffer.fetchChoices (oneSeqCstStore storeIndex storeClock syncClock)
      true loadClocks).map (fun choice => (choice.position, choice.element.val)) =
      [(1, some 1)] := by
  simp_sc_selector <;> split <;> simp_sc_selector

#print axioms initial_sc_store_load_selects_newest
