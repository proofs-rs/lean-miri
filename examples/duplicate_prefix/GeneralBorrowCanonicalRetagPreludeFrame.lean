import duplicate_prefix.GeneralBorrowCanonicalChildCausalFrame
import duplicate_prefix.GeneralBorrowCanonicalRaceCausalFrame
namespace DuplicatePrefix.GeneralBorrowCanonicalRetagPreludeFrame
open Miri Miri.Memory Miri.ABI Miri.MIR Miri.Interpreter Miri.DataStructures Miri.TreeBorrows
open TypedRetagEntry GeneralBorrowCanonicalRetagQueryFrame GeneralBorrowEffectfulTreeUpdateFrame GeneralBorrowTypedTreeUpdateCausalFrame
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- Source protector registration and allocation-kind lookup. No hooks are
supplied; only actual tracker/stack state may change, including before errors. -/
def prelude {K User : Type} (location : RetagPipeline.ResolvedLocation)
    (policy : RetagPolicy.NewPermission) (tag : BorTag) : MachineHooks.M K User AllocationInfo := do
  if let some protection := policy.protector then
    let frame ← MachineHooks.currentFrame
    let some borrowFrame := frame.extra.borrowTracker
      | throw (.invalidProgram "borrow frame missing")
    let old ← (typed_tracker (K:=K) (User:=User))
    let (global, borrowFrame) := old.global.addProtector borrowFrame location.allocId tag protection
    modify fun state => { state with machine := { state.machine with
      borrowTracker := some { old with global } } }
    MachineHooks.setCurrentFrame { frame with extra := { frame.extra with borrowTracker := some borrowFrame } }
  typed_checked "allocation kind" ((← get).machine.memory.getAllocInfo location.allocId)

theorem memory {K U : Type} (state : MachineHooks.State K U)
    (location : RetagPipeline.ResolvedLocation) (policy : RetagPolicy.NewPermission) (tag : BorTag) :
    (retained (prelude location policy tag state)).machine.memory = state.machine.memory := by
  unfold prelude
  unfold_typed ".TypedRetag.tracker"
  unfold_typed ".TypedRetag.checked"
  unfold MachineHooks.currentFrame MachineHooks.setCurrentFrame
  cases protectionEq : policy.protector with
  | none =>
    simp only [protectionEq,get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind]
    all_goals cases info : state.machine.memory.getAllocInfo location.allocId <;> rfl
  | some protection =>
    simp only [protectionEq,get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure]
    cases frameEq : state.stack.currentFrame? with
    | none => simp only [frameEq];rfl
    | some frame =>
      simp only [frameEq,get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure]
      cases borrowed : frame.extra.borrowTracker with
      | none => simp only [borrowed,get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure];rfl
      | some borrowFrame =>
        simp only [borrowed,get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure]
        cases enabled : state.machine.borrowTracker with
        | none => simp only [enabled,get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure];rfl
        | some tracker =>
          simp only [enabled,pure,EStateM.pure,modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,
            get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,set,EStateM.set]
          cases empty : state.stack.frames.isEmpty <;>
            simp only [empty,Bool.false_eq_true,↓reduceIte,pure,EStateM.pure,set,EStateM.set,bind,EStateM.bind]
          all_goals cases info : state.machine.memory.getAllocInfo location.allocId <;> rfl

theorem preserves {K U : Type} (P : AllocId → BorrowTree → Prop)
    (state : MachineHooks.State K U) (location : RetagPipeline.ResolvedLocation)
    (policy : RetagPolicy.NewPermission) (tag : BorTag) (before : AllTrees P state.machine.memory) :
    Holds P (prelude location policy tag state) := by
  have after : AllTrees P (retained (prelude location policy tag state)).machine.memory := by
    rw [memory];exact before
  cases actual : prelude location policy tag state <;> simpa only [actual,retained,Holds] using after

def withPrelude {K User A : Type} (location : RetagPipeline.ResolvedLocation)
    (policy : RetagPolicy.NewPermission) (tag : BorTag) (next : AllocationInfo → MachineHooks.M K User A) : MachineHooks.M K User A := do
  if let some protection := policy.protector then
    let frame ← MachineHooks.currentFrame
    let some borrowFrame := frame.extra.borrowTracker
      | throw (.invalidProgram "borrow frame missing")
    let old ← (typed_tracker (K:=K) (User:=User))
    let (global, borrowFrame) := old.global.addProtector borrowFrame location.allocId tag protection
    modify fun state => { state with machine := { state.machine with
      borrowTracker := some { old with global } } }
    MachineHooks.setCurrentFrame { frame with extra := { frame.extra with borrowTracker := some borrowFrame } }
  let info ← typed_checked "allocation kind" ((← get).machine.memory.getAllocInfo location.allocId)
  next info

theorem with_equation {K U A : Type} (state : MachineHooks.State K U)
    (location : RetagPipeline.ResolvedLocation) (policy : RetagPolicy.NewPermission) (tag : BorTag)
    (next : AllocationInfo → MachineHooks.M K U A) :
    withPrelude location policy tag next state = (prelude location policy tag >>= next) state := by
  unfold prelude withPrelude
  unfold_typed ".TypedRetag.tracker"
  unfold_typed ".TypedRetag.checked"
  unfold MachineHooks.currentFrame MachineHooks.setCurrentFrame
  cases protectionEq : policy.protector with
  | none =>
    simp only [protectionEq,get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind]
    all_goals cases info : state.machine.memory.getAllocInfo location.allocId <;> rfl
  | some protection =>
    simp only [protectionEq,get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure]
    cases frameEq : state.stack.currentFrame? with
    | none => simp only [frameEq];rfl
    | some frame =>
      simp only [frameEq,get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure]
      cases borrowed : frame.extra.borrowTracker with
      | none => simp only [borrowed,get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure];rfl
      | some borrowFrame =>
        simp only [borrowed,get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure]
        cases enabled : state.machine.borrowTracker with
        | none => simp only [enabled,get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure];rfl
        | some tracker =>
          simp only [enabled,pure,EStateM.pure,modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,
            get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,set,EStateM.set]
          cases empty : state.stack.frames.isEmpty <;>
            simp only [empty,Bool.false_eq_true,↓reduceIte,pure,EStateM.pure,set,EStateM.set,bind,EStateM.bind]
          all_goals cases info : state.machine.memory.getAllocInfo location.allocId <;> rfl


theorem with_preserves {K U A : Type} (P : AllocId → BorrowTree → Prop)
    (state : MachineHooks.State K U) (location : RetagPipeline.ResolvedLocation)
    (policy : RetagPolicy.NewPermission) (tag : BorTag) (next : AllocationInfo → MachineHooks.M K U A)
    (before : AllTrees P state.machine.memory)
    (continuation : ∀ info after, AllTrees P after.machine.memory → Holds P (next info after)) :
    Holds P (withPrelude location policy tag next state) := by
  rw [with_equation]
  have stageInvariant := preserves P state location policy tag before
  cases actual : prelude location policy tag state with
  | error error changed => simpa only [bind,EStateM.bind,actual,Holds] using stageInvariant
  | ok info changed =>
    simp only [bind,EStateM.bind,actual]
    exact continuation info changed (by simpa only [actual,Holds] using stageInvariant)

def preludeReborrow {K User : Type} [DecidableEq K] (h : TypedRetag.Hooks K User) (budget : Nat)
    (place : MPlaceTy Provenance) (size : Size) (policy : RetagPolicy.NewPermission) (tag : BorTag) :
    MachineHooks.M K User (Option Provenance) := do
  h.checkPtrAccess place.mplace.ptr size
  let location ← h.resolveAllocation place.mplace.ptr
  match location with
  | none =>
    if size.bytes != 0 then throw (.invalidProgram "nonzero reborrow without allocation")
    h.logCreation place size policy tag none
    return place.mplace.ptr.provenance
  | some location =>
    h.logCreation place size policy tag (some location)
    withPrelude location policy tag (fun info => do
      let provenance := some (Provenance.concrete location.allocId tag)
      if info.kind != .liveData then
        if size.bytes != 0 then throw (.invalidProgram "nonlive allocation with nonzero reborrow")
        return provenance
      let inside ← typed_inside h budget place size policy
      h.ensureTreeExtra location.allocId
      let _ ← forIn inside.iterAll () (fun segment _ => GeneralBorrowCanonicalReborrowSource.sourceSegment location segment)
      GeneralBorrowCanonicalChildCausalFrame.childSuffix location inside policy tag)

/-- The continuation-inside adapter is exactly the actual canonical source.
No successful query, retag, access or child is assumed. -/
theorem source_equation {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K U) (budget : Nat) (place : MPlaceTy Provenance)
    (size : Size) (policy : RetagPolicy.NewPermission) (tag : BorTag) :
    TypedRetag.reborrow h budget place size policy tag =
      preludeReborrow h budget place size policy tag := by rfl
end DuplicatePrefix.GeneralBorrowCanonicalRetagPreludeFrame
