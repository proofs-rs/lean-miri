import duplicate_prefix.GeneralBorrowGcFrameProvenanceCollection
import Miri.Interpreter.MachineGCRoots

namespace DuplicatePrefix.GeneralBorrowGcFrameProvenanceMonotone
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows ProvenanceGC
open GeneralBorrowGcFrameProvenanceScalar
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

def Result (before : Roots) (outcome : Except StepError Roots) : Prop :=
  ∀ after, outcome = .ok after → Extends before after

theorem pure_result (roots : Roots) : Result roots (.ok roots) := by
  intro after equal
  cases equal
  exact extends_refl roots

theorem chain (roots : Roots) (first : Except StepError Roots)
    (next : Roots → Except StepError Roots) (one : Result roots first)
    (two : ∀ middle, Result middle (next middle)) : Result roots (first >>= next) := by
  intro after success
  cases actual : first with
  | error error => simp only [actual,bind,Except.bind] at success; cases success
  | ok middle =>
    simp only [actual,bind,Except.bind] at success
    exact extends_trans (one middle actual) (two middle after success)

theorem guard (roots : Roots) (first : Except StepError α)
    (next : α → Except StepError Roots) (good : ∀ value, Result roots (next value)) :
    Result roots (first >>= next) := by
  intro after success
  cases actual : first with
  | error error => simp only [actual,bind,Except.bind] at success; cases success
  | ok value => exact good value after (by simpa only [actual,bind,Except.bind] using success)

theorem loop (items : List α) (visit : α → Roots → Except StepError (ForInStep Roots))
    (step : ∀ item ∈ items, ∀ before out, visit item before = .ok out → Extends before out.value)
    (roots : Roots) : Result roots (forIn (m := Except StepError) items roots visit) := by
  induction items generalizing roots with
  | nil => simpa only [List.forIn_nil,pure,Except.pure] using pure_result roots
  | cons item rest ih =>
    intro after success
    rw [List.forIn_cons] at success
    cases actual : visit item roots with
    | error error => simp only [actual,bind,Except.bind] at success; cases success
    | ok out =>
      have one := step item (by simp) roots out actual
      cases out with
      | done final =>
        simp only [actual,bind,Except.bind,pure,Except.pure] at success
        cases success
        exact one
      | yield middle =>
        simp only [actual,bind,Except.bind] at success
        exact extends_trans one (ih (fun other member => step other (by simp [member])) middle after success)

theorem fold (items : List α) (visit : Roots → α → Roots)
    (step : ∀ roots item, Extends roots (visit roots item)) (roots : Roots) :
    Extends roots (items.foldl visit roots) := by
  induction items generalizing roots with
  | nil => exact extends_refl roots
  | cons item rest ih => exact extends_trans (step roots item) (ih (visit roots item))

theorem scalar (roots : Roots) (value : Scalar Provenance) : Result roots (roots.scalar value) := by
  intro after success
  unfold Roots.scalar at success
  cases actual : value.toBitsOrPtrInternal (Miri.Memory.Scalar.size value) with
  | error error => simp only [actual,Except.mapError,bind,Except.bind] at success; cases success
  | ok value =>
    cases value with
    | bits value =>
      simp only [actual,Except.mapError,bind,Except.bind,pure,Except.pure] at success
      cases success
      exact extends_refl roots
    | pointer pointer =>
      simp only [actual,Except.mapError,bind,Except.bind,pure,Except.pure] at success
      cases success
      exact provenance_extends roots pointer.provenance

theorem immediate (roots : Roots) (value : Immediate Provenance) : Result roots (roots.immediate value) := by
  cases value with
  | uninit => exact pure_result roots
  | scalar value => exact scalar roots value
  | scalarPair first second =>
    exact chain roots (roots.scalar first) (fun middle => middle.scalar second) (scalar roots first) (fun middle => scalar middle second)

theorem metadata (roots : Roots) (value : MemPlaceMeta Provenance) : Result roots (roots.metadata value) := by
  cases value with
  | none => exact pure_result roots
  | metadata value => exact scalar roots value

theorem memPlace (roots : Roots) (place : MemPlace Provenance) : Result roots (roots.memPlace place) := by
  intro after success
  exact extends_trans (pointer_extends roots place.ptr) (metadata (roots.pointer place.ptr) place.metadata after success)

theorem operand (roots : Roots) (value : Operand Provenance) : Result roots (roots.operand value) := by
  cases value with
  | immediate value => exact immediate roots value
  | indirect place => exact memPlace roots place

theorem runtimePlace (roots : Roots) (place : RuntimeStackPlace Provenance) : Result roots (roots.runtimePlace place) := by
  cases place with
  | memory place => exact memPlace roots place.mplace
  | frameLocal => exact pure_result roots


theorem yielding (roots : Roots) (action : Except StepError Roots) (good : Result roots action)
    (out : ForInStep Roots) (success : (do return ForInStep.yield (←action)) = .ok out) :
    Extends roots out.value := by
  cases actual : action with
  | error error => simp only [actual,bind,Except.bind] at success; cases success
  | ok after =>
    simp only [actual,bind,Except.bind,pure,Except.pure] at success
    cases success
    exact good after actual


theorem of_extension (before middle : Roots) (action : Except StepError Roots)
    (extension : Extends before middle) (good : Result middle action) : Result before action := by
  intro after success
  exact extends_trans extension (good after success)

theorem frame (roots : Roots) (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) :
    Result roots (roots.frame frame) := by
  unfold Roots.frame
  apply chain roots _ _ (runtimePlace roots frame.returnPlace)
  intro initial
  apply chain initial _ _
  · rw [←Array.forIn_toList]
    apply loop
    intro entry member before out success
    cases stored : entry.value with
    | dead =>
      simp only [stored,pure,Except.pure] at success
      cases success
      exact extends_refl before
    | live value =>
      simp only [stored] at success
      exact yielding before (before.operand value) (operand before value) out success
  · intro afterLocals
    let finish (start : Roots) : Except StepError Roots := do
      let mut current := start
      if let some borrow := frame.extra.borrowTracker then
        for (id,tag) in borrow.protectedTags do current := current.add (some id) (some tag)
      return current
    have finalStep : ∀ start, Result start (finish start) := by
      intro start
      dsimp only [finish]
      cases stored : frame.extra.borrowTracker with
      | none => exact pure_result start
      | some borrow =>
        apply chain start _ _
        · rw [←Array.forIn_toList]
          apply loop
          intro pair member before out success
          cases pair with
          | mk id tag =>
            simp only [pure,Except.pure] at success
            cases success
            exact add_extends before (some id) (some tag)
        · intro after
          exact pure_result after
    cases frame.extra.catchUnwind with
    | none => exact finalStep afterLocals
    | some caught =>
      intro after success
      apply extends_trans (pointer_extends afterLocals caught.catchFn)
      exact chain (afterLocals.pointer caught.catchFn) _ _
        (immediate (afterLocals.pointer caught.catchFn) caught.data.imm)
        (fun middle => chain middle _ _ (memPlace middle caught.dest.mplace) finalStep) after success

theorem stack (roots : Roots) (stack : ThreadStacks.ActualStack) : Result roots (roots.stack stack) := by
  unfold Roots.stack
  apply chain roots _ _
  · rw [←Array.forIn_toList]
    apply loop
    intro item member before out success
    exact yielding before (before.frame item) (frame before item) out success
  · intro after
    exact pure_result after

end DuplicatePrefix.GeneralBorrowGcFrameProvenanceMonotone
