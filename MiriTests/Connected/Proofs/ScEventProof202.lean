import Miri.Concurrency.WeakMemory
import MiriTests.Connected.Proofs.SelectorProof195

/-! # Six-event SC support quotient

This checks the per-location finite support of the actual Lean
`StoreBuffer.fetchChoices` for the six two-thread event orders. For a load
before its opposite store it uses the sole-initial-value buffer; after that
store it uses the real SC `storeImpl` buffer and the public all-clock selector
lemma. The event order is supplied to this quotient: this does not prove that
the connected MIR scheduler realizes exactly these orders or that runtime
steps erase to this projection.
-/

open Miri.Concurrency

private def oneSc (idx : VectorIdx) (writer sync : VClock) : StoreBuffer Nat :=
  (StoreBuffer.new (some 0)).storeImpl 1 idx writer true sync

private def choicesToValues (choices : List (StoreBuffer.LoadChoice Nat)) :
    List (Option Nat) :=
  choices.map (fun choice => choice.element.val)

private def initialSupport (reader : ThreadClockSet) : List (Option Nat) :=
  choicesToValues (StoreBuffer.fetchChoices (StoreBuffer.new (some 0)) true reader)

private def storedSupport (idx : VectorIdx) (writer sync : VClock)
    (reader : ThreadClockSet) : List (Option Nat) :=
  choicesToValues (StoreBuffer.fetchChoices (oneSc idx writer sync) true reader)

theorem initial_support_is_zero (reader : ThreadClockSet) :
    initialSupport reader = [some 0] := by
  conv => lhs; cbv

theorem stored_support_is_one (idx : VectorIdx) (writer sync : VClock)
    (reader : ThreadClockSet) : storedSupport idx writer sync reader = [some 1] := by
  have h := initial_sc_store_load_selects_newest idx writer sync reader
  change (StoreBuffer.fetchChoices (oneSc idx writer sync) true reader).map
      (fun choice => (choice.position, choice.element.val)) = [(1, some 1)] at h
  have hv := congrArg (List.map Prod.snd) h
  simp only [List.map_map, Function.comp_def] at hv
  simp [storedSupport, choicesToValues, hv]

inductive Event where
  | aStore | aLoad | bStore | bLoad
  deriving DecidableEq, BEq, Repr

private def sixOrders : List (List Event) := [
  [.aStore, .aLoad, .bStore, .bLoad],
  [.aStore, .bStore, .aLoad, .bLoad],
  [.aStore, .bStore, .bLoad, .aLoad],
  [.bStore, .aStore, .aLoad, .bLoad],
  [.bStore, .aStore, .bLoad, .aLoad],
  [.bStore, .bLoad, .aStore, .aLoad]
]

private def precedes (events : List Event) (first second : Event) : Bool :=
  events.idxOf first < events.idxOf second

private def supportIf (storeBeforeLoad : Bool) (idx : VectorIdx)
    (writer sync : VClock) (reader : ThreadClockSet) : List (Option Nat) :=
  if storeBeforeLoad then storedSupport idx writer sync reader else initialSupport reader

private def pairSupport (events : List Event)
    (xIndex yIndex : VectorIdx)
    (writerX syncX : VClock) (readerB : ThreadClockSet)
    (writerY syncY : VClock) (readerA : ThreadClockSet) :
    List (Option Nat × Option Nat) :=
  (supportIf (precedes events .bStore .aLoad) yIndex writerY syncY readerA).flatMap
    (fun a => (supportIf (precedes events .aStore .bLoad) xIndex writerX syncX readerB).map
      (fun b => (a, b)))

theorem actual_sc_selector_six_event_support
    (xIndex yIndex : VectorIdx)
    (writerX syncX : VClock) (readerB : ThreadClockSet)
    (writerY syncY : VClock) (readerA : ThreadClockSet) :
    sixOrders.map (fun events => pairSupport events xIndex yIndex
      writerX syncX readerB writerY syncY readerA) =
      [[(some 0, some 1)], [(some 1, some 1)], [(some 1, some 1)],
       [(some 1, some 1)], [(some 1, some 1)], [(some 1, some 0)]] := by
  simp [sixOrders, pairSupport, supportIf, precedes, initial_support_is_zero,
    stored_support_is_one] <;> decide

#print axioms initial_support_is_zero
#print axioms stored_support_is_one
#print axioms actual_sc_selector_six_event_support
