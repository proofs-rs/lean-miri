import duplicate_prefix.GlobalAddressPhysicalRowHistory
namespace DuplicatePrefix.AddressReuseClockFormation
open Miri Miri.Concurrency Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

open Lean Elab in
elab "clock_source " suffix:str : term => do
  let names:=(←getEnv).constants.toList.filterMap fun (name,_)=>
    if name.toString.endsWith suffix.getString then some name else none
  let [name]:=names | throwError "expected unique clock source helper"
  Lean.Meta.mkConstWithFreshMVarLevels name

theorem getAt {A} (entries : List A) (index : Nat) :
    (clock_source ".GlobalState.getAt?") entries index=entries[index]? := by
  induction entries generalizing index with
  | nil=>rfl
  | cons head tail ih=>cases index with
    | zero=>rfl
    | succ index=>exact ih index

theorem setAt {A} (entries : List A) (index : Nat) (value : A) (bounded : index<entries.length) :
    (clock_source ".GlobalState.setAt?") entries index value=some (entries.set index value) := by
  induction entries generalizing index with
  | nil=>simp only [List.length_nil] at bounded;omega
  | cons head tail ih=>
    cases index with
    | zero=>rfl
    | succ index=>
      have next : index<tail.length:=by simpa using bounded
      unfold_internal ".GlobalState.setAt?"
      rw [ih index next]
      rfl

/-- Actual reuse-clock acquisition is total when the active thread's raw
metadata and clock slot exist. It joins the donor snapshot into that real
slot, with no acquire-success or post-global premise. -/
theorem acquire (global : Miri.Concurrency.GlobalState) (threads : ThreadManager)
    (index : VectorIdx) (extra : ThreadExtraState) (clocks : ThreadClockSet) (donor : VClock)
    (threadPresent : global.threadInfo[threads.activeThread.toNat]?=some extra)
    (threadIndex : extra.vectorIndex=some index)
    (clockPresent : global.vectorClocks[index.toNat]?=some clocks) :
    global.acquireClock threads donor=.ok {global with vectorClocks:=global.vectorClocks.set index.toNat {clocks with clock:=clocks.clock.join donor}} := by
  have bounded : index.toNat<global.vectorClocks.length := by
    by_cases valid : index.toNat<global.vectorClocks.length
    · exact valid
    · rw [List.getElem?_eq_none (by omega)] at clockPresent
      cases clockPresent
  unfold Miri.Concurrency.GlobalState.acquireClock Miri.Concurrency.GlobalState.activeThreadState
    Miri.Concurrency.GlobalState.activeThreadIndex
  unfold_internal ".GlobalState.threadIndex"
  unfold_internal ".GlobalState.threadExtra?"
  unfold_internal ".GlobalState.clocksAt"
  simp only [getAt,threadPresent,threadIndex,clockPresent,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]
  rw [setAt global.vectorClocks index.toNat _ bounded]
end DuplicatePrefix.AddressReuseClockFormation
