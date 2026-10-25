import Lean
import Miri.Concurrency.WeakMemory

open Miri.Concurrency
open Lean Elab Tactic

private def findUniqueJoinReadName (suffix : String) : TacticM Name := do
  let env ← getEnv
  let candidates := env.constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith suffix then some name else none
  match candidates with
  | [name] => pure name
  | _ => throwError m!"expected one private selector `{suffix}`, found {candidates.length}"

private def oneRelaxedStore (storeIndex : VectorIdx) (storeClock syncClock : VClock)
    (value : Nat) : StoreBuffer Nat :=
  (StoreBuffer.new (some 9)).storeImpl value storeIndex storeClock false syncClock

elab "simp_join_read" : tactic => do
  let helpers ← [
    ".StoreBuffer.indexedEntries",
    ".StoreBuffer.reverseIndexed",
    ".StoreBuffer.candidatePrefix",
    ".StoreBuffer.filterSeqCst"
  ].mapM findUniqueJoinReadName
  let helperIds := helpers.toArray.map mkIdent
  let generated ← `(tactic| simp_all [StoreBuffer.fetchChoices, StoreBuffer.storeImpl,
    oneRelaxedStore, StoreBuffer.entries, StoreBuffer.new, StoreBuffer.blocksEarlier,
    VClock.index, VTimestamp.ZERO, VTimestamp.time, STORE_BUFFER_LIMIT,
    $[$helperIds:ident],*])
  evalTactic generated

/-- After the reader clock has advanced through the sole Relaxed store, the
actual store-buffer fetch filter can return only that newly stored value. -/
theorem joined_reader_selects_single_relaxed_store
    (storeIndex : VectorIdx) (writerClock syncClock : VClock)
    (readerClocks : ThreadClockSet) (value : Nat) (loadIsSeqCst : Bool)
    (happensBefore : (writerClock.index storeIndex).time ≤
      (readerClocks.clock.index storeIndex).time) :
    (StoreBuffer.fetchChoices
      (oneRelaxedStore storeIndex writerClock syncClock value)
      loadIsSeqCst readerClocks).map
      (fun choice => (choice.position, choice.element.val)) =
      [(1, some value)] := by
  simp_join_read

#print axioms joined_reader_selects_single_relaxed_store
