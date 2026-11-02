import duplicate_prefix.GeneralBorrowCanonicalParentLoopCausalFrame
import duplicate_prefix.GeneralBorrowCanonicalReborrowSource
namespace DuplicatePrefix.GeneralBorrowCanonicalSegmentSourceFrame
open Miri Miri.Memory Miri.ABI Miri.MIR Miri.Interpreter Miri.DataStructures Miri.TreeBorrows
open TypedRetagEntry GeneralBorrowCanonicalParentLoopCausalFrame
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 400000
private theorem bind_if {E S A B : Type} (condition : Prop) [Decidable condition]
    (yes no : EStateM E S A) (next : A → EStateM E S B) :
    (if condition then yes else no) >>= next =
      if condition then yes >>= next else no >>= next := by
  split <;> rfl
private theorem bind_option {E S A B C : Type} (value : Option C)
    (none : EStateM E S A) (some : C → EStateM E S A) (next : A → EStateM E S B) :
    (match value with | .none => none | .some x => some x) >>= next =
      match value with | .none => none >>= next | .some x => some x >>= next := by
  cases value <;> rfl
private theorem throw_bind {E S A B : Type} (error : E) (next : A → EStateM E S B) :
    (throw error : EStateM E S A) >>= next = throw error := by rfl

theorem segment_equation {K U : Type} [DecidableEq K]
    (location : RetagPipeline.ResolvedLocation) (segment : RangeMapSegment Tree.LocationState) :
    (GeneralBorrowCanonicalReborrowSource.sourceSegment location segment : MachineHooks.M K U (ForInStep PUnit)) =
      (do parentSegment location segment; pure (.yield ())) := by
  unfold GeneralBorrowCanonicalReborrowSource.sourceSegment parentSegment mutabilityGuard parentCore
  cases associated : segment.data.permission.associatedAccess with
  | none => rfl
  | some access =>
    cases access <;>
      simp only [associated,reduceCtorEq,Bool.false_eq_true,↓reduceIte,bind_assoc,pure_bind,bind_pure,
        bind_if,bind_option,throw_bind,
        show (AccessKind.Read == AccessKind.Write) = false from rfl,
        show (AccessKind.Write == AccessKind.Write) = true from rfl]
    all_goals
      funext state
      simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure]
      cases found : state.machine.memory.live.find? (fun row => row.1 == location.allocId) with
      | none => rfl
      | some row =>
        cases mutable : (row.2.allocation.mutability == .Not) <;>
          simp only [mutable,Bool.false_eq_true,↓reduceIte] <;> rfl
/-- The actual canonical ForIn body preserves every node/tag-map-stable
all-live tree invariant, including error states. No access success is assumed. -/
theorem source_loop_preserves {K U : Type} [DecidableEq K]
    (P : AllocId → BorrowTree → Prop) (stable : FrameStable P)
    (location : RetagPipeline.ResolvedLocation) (inside : DedupRangeMap Tree.LocationState) :
    Preserves P (forIn inside.iterAll () (fun segment _ =>
      GeneralBorrowCanonicalReborrowSource.sourceSegment location segment) : MachineHooks.M K U PUnit) := by
  simp only [← Array.forIn_toList]
  apply list_preserves
  intro segment member initial
  rw [segment_equation]
  apply bind_preserves P _ _ (segment_preserves P stable location segment)
  intro _
  exact readonly_preserves P _ (GeneralBorrowCanonicalRetagQueryFrame.pure_readonly _)

end DuplicatePrefix.GeneralBorrowCanonicalSegmentSourceFrame
