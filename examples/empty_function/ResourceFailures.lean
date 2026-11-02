import empty_function.TagReserve
import Miri.Interpreter.TypedRetag
import Miri.Interpreter.RunLoop
import Miri.Interpreter.ValidityVisitor
import Miri.Interpreter.DynamicLayout
import Lean

namespace EmptyFunction.ResourceFailures
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
set_option maxHeartbeats 800000

 theorem invalidProgram_nonUB (reason : String) :
    RunLoop.reportsUB (.invalidProgram reason) = false := rfl

 theorem resourceExhaustion_nonUB (reason : String) :
    RunLoop.reportsUB (.resourceExhaustion reason) = false := rfl

/-- Failure at the source's checked tag increment is a runner invariant error,
not an aliasing violation. No memory callback is executed after that failure. -/
 theorem retag_tag_failure {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K U) (budget : Nat) (place : MPlaceTy Provenance)
    (policy : RetagPolicy.NewPermission) (state : MachineHooks.State K U)
    (tracker : MachineHooks.BorrowState) (measured : Option (Size × Align))
    (sizeQuery : h.sizeAndAlign place = pure measured)
    (enabled : state.machine.borrowTracker = some tracker)
    (failure : tracker.global.newPointerTag = .error (.pointerTagOverflow tracker.global.nextPointerTag)) :
    ∃ reason, TypedRetag.retagPlace h budget place policy state =
      .error (.invalidProgram reason) state := by
  exact TypedRetag.retagPlace_tag_failure h budget place policy state tracker measured sizeQuery enabled failure

 theorem max_tag_fails (global : GlobalState)
    (maximum : global.nextPointerTag.value = 18446744073709551615) :
    global.newPointerTag = .error (.pointerTagOverflow global.nextPointerTag) := by
  simp [GlobalState.newPointerTag,BorTag.succ,maximum]

 theorem protect_maximum_failure {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K U) (budget : Nat) (place : MPlaceTy Provenance)
    (state : MachineHooks.State K U) (tracker : MachineHooks.BorrowState)
    (measured : Option (Size × Align))
    (sizeQuery : h.sizeAndAlign place = pure measured)
    (enabled : state.machine.borrowTracker = some tracker)
    (maximum : tracker.global.nextPointerTag.value = 18446744073709551615) :
    ∃ reason, TypedRetag.protectInPlaceFunctionArgument h budget place state =
      .error (.invalidProgram reason) state := by
  obtain ⟨reason,failed⟩ := retag_tag_failure h budget place MachineHooks.protectionPolicy
    state tracker measured sizeQuery enabled (max_tag_fails tracker.global maximum)
  refine ⟨reason,?_⟩
  unfold TypedRetag.protectInPlaceFunctionArgument TypedRetag.protectPlace
  simp [enabled,failed,bind,Bind.bind,EStateM.bind,get,getThe,MonadStateOf.get,EStateM.get,
    pure,Pure.pure,EStateM.pure]

/-- The finite u64 tag supply either advances once, or stops with its exact
checked-overflow error. No numeric room is an input assumption. -/
 theorem tag_total (global : GlobalState) :
    (global.nextPointerTag.value = 18446744073709551615 ∧
      global.newPointerTag = .error (.pointerTagOverflow global.nextPointerTag)) ∨
    (∃ after, global.newPointerTag = .ok (after,global.nextPointerTag) ∧
      global.nextPointerTag.value.toNat + 1 < 2^64 ∧
      after.nextPointerTag.value.toNat = global.nextPointerTag.value.toNat + 1 ∧
      after.rootPointerTags = global.rootPointerTags ∧
      after.protectedTags = global.protectedTags ∧
      after.trackedPointerTags = global.trackedPointerTags) := by
  by_cases maximum : global.nextPointerTag.value = 18446744073709551615
  · exact Or.inl ⟨maximum,max_tag_fails global maximum⟩
  · have room : global.nextPointerTag.value.toNat + 1 < 2^64 := by
      have bound := UInt64.toNat_lt global.nextPointerTag.value
      have different : global.nextPointerTag.value.toNat ≠ 18446744073709551615 := by
        intro equal
        exact maximum (UInt64.toNat_inj.mp equal)
      omega
    obtain ⟨after,actual,count,cache,protectors,tracked⟩ := TagReserve.child global [] (by simpa using room)
    exact Or.inr ⟨after,actual,room,by simpa using count,cache,protectors,tracked⟩

/-- Successful execution supplies its own room and unchanged root cache; a
whole-domain theorem may split on the actual result rather than assume room. -/
 theorem tag_success (global after : GlobalState) (tag : BorTag)
    (actual : global.newPointerTag = .ok (after,tag)) :
    global.nextPointerTag.value.toNat + 1 < 2^64 ∧ tag = global.nextPointerTag ∧
      after.nextPointerTag.value.toNat = global.nextPointerTag.value.toNat + 1 ∧
      after.rootPointerTags = global.rootPointerTags ∧
      after.protectedTags = global.protectedTags ∧
      after.trackedPointerTags = global.trackedPointerTags := by
  rcases tag_total global with ⟨_,failure⟩ | ⟨next,success,room,counter,cache,protectors,tracked⟩
  · rw [failure] at actual
    cases actual
  · rw [success] at actual
    cases actual
    exact ⟨room,rfl,counter,cache,protectors,tracked⟩

 theorem root_total (global : GlobalState) (id : AllocId) :
    (∃ after tag, global.rootPointerTag id = .ok (after,tag)) ∨
    (global.rootTag? id = none ∧ global.nextPointerTag.value = 18446744073709551615 ∧
      global.rootPointerTag id = .error (.pointerTagOverflow global.nextPointerTag)) := by
  cases cached : global.rootTag? id with
  | some tag => exact Or.inl ⟨global,tag,GlobalState.rootPointerTag_existing global id tag cached⟩
  | none =>
    rcases tag_total global with ⟨maximum,failed⟩ | ⟨next,created,_⟩
    · apply Or.inr
      refine ⟨rfl,maximum,?_⟩
      simp [GlobalState.rootPointerTag,cached,failed,bind,Except.bind]
    · apply Or.inl
      refine ⟨{next with rootPointerTags := next.rootPointerTags.push (id,global.nextPointerTag)},
        global.nextPointerTag,?_⟩
      simp [GlobalState.rootPointerTag,cached,created,bind,Except.bind,pure,Except.pure]

/-- Canonical retag error decoration does not turn exhaustion into UB. -/
 theorem retag_classification_resource (path : ValidationPath)
    (kind : SafePointerKind) (reason : String) :
    RunLoop.reportsUB (ValidityVisitor.classifyRetagError path kind
      (.resourceExhaustion reason)) = false := rfl

 theorem retag_classification_invariant (path : ValidationPath)
    (kind : SafePointerKind) (reason : String) :
    RunLoop.reportsUB (ValidityVisitor.classifyRetagError path kind
      (.invalidProgram reason)) = false := rfl

 theorem validity_zero {P S C E F A Pad : Type} [PointerProvenance P] [DecidableEq P]
    (h : ValidityVisitor.Hooks P S C E F A Pad) (choice : C)
    (session : ValidityVisitor.Session P) (place : RuntimePlace P) (state : S) :
    ValidityVisitor.visit h choice 0 session place state =
      .error (.resourceExhaustion "validity traversal fuel") state := rfl

 theorem dynamic_zero {P S C : Type} [PointerProvenance P]
    (h : DynamicLayoutHooks P S C) (choice : C) (metadataValue : MemPlaceMeta P)
    (layout : TyAndLayout MIR.TyId) (unsized : layout.layout.isSized = false) (state : S) :
    DynamicLayout.sizeAndAlignFromMeta h choice 0 metadataValue layout state =
      .error (.resourceExhaustion "dynamic layout recursion fuel") state := by
  simp [DynamicLayout.sizeAndAlignFromMeta,unsized,throw,throwThe,MonadExceptOf.throw,EStateM.throw]

open Lean Elab Command in
run_cmd do
  let mut total : Nat := 0
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.startsWith "EmptyFunction.ResourceFailures." then
      total := total+1
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved resource failure axiom {dependency} in {name}"
  logInfo m!"Audited {total} resource failure declarations"

end EmptyFunction.ResourceFailures
