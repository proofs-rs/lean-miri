import Miri.Verification.RvalueWP
import Miri.Verification.TreeBorrowsWP
import Miri.Interpreter.TypedMachineBindings

/-! The release access runs while the protector is still in force. Each
homogeneous segment threads the updated location map to the next segment. -/
namespace Miri.Verification.ProtectorReleaseWP

open Miri.ABI Miri.DataStructures Miri.Interpreter Miri.Memory Miri.TreeBorrows Std.WP

/-- A successful segment continues on its updated tree. Skipped segments
keep the tree, while failed mutations preserve the committed prefix. -/
def segmentPre (source : UniIndex) (tags : ProtectedTags) (position : Nat)
    (next : BorrowTree → Prop) (failure : BorrowTree.ProtectorReleaseStatus → BorrowTree → Prop)
    (tree : BorrowTree) : Prop :=
  match tree.locations.index position with
  | .error error => failure (.RangeMapFailure error) tree
  | .ok segment =>
    match segment.data.perms.get source with
    | none => next tree
    | some state =>
      match state.permission.associatedAccess with
      | none => next tree
      | some kind =>
        if state.accessed then
          BorrowTree.RangeVerification.locationContract tree segment.data (some source) kind
            tags .SkipChildrenOfAccessed segment.range fun visit =>
              let mutation := tree.locations.setAtPos position visit.location
              let updated := { tree with locations := mutation.state }
              match mutation.outcome with
              | .error error => failure (.LocationMapFailure error) updated
              | .ok () =>
                match visit.status with
                | some status => failure (.AccessFailure segment.range status) updated
                | none => next updated
        else next tree

def segmentsPre (tag : BorTag) (tags : ProtectedTags) (source : UniIndex)
    (post : BorrowTree → Prop) (failure : BorrowTree.ProtectorReleaseStatus → BorrowTree → Prop) :
    List Nat → BorrowTree → Prop
  | [], tree =>
    BorrowTree.MutationVerification.releaseExposurePre tree tag post
      (fun error => failure (.ExposureUpdateFailure error))
  | position :: rest, tree =>
    segmentPre source tags position (segmentsPre tag tags source post failure rest) failure tree

/-- Discharge the exact success or failed-release condition for this tag. -/
def releasePre (tag : BorTag) (tags : ProtectedTags) (post : BorrowTree → Prop)
    (failure : BorrowTree.ProtectorReleaseStatus → BorrowTree → Prop) (tree : BorrowTree) : Prop :=
  match tree.indexOfTag tag with
  | none => failure (.MissingTag tag) tree
  | some source => segmentsPre tag tags source post failure
      (List.range' 0 tree.locations.entries.size) tree

private def resultPre (post : BorrowTree → Prop)
    (failure : BorrowTree.ProtectorReleaseStatus → BorrowTree → Prop)
    (result : BorrowTree.ProtectorReleaseResult) : Prop :=
  match result.status with
  | .Released => post result.tree
  | error => failure error result.tree

set_option maxHeartbeats 2000000 in
theorem releasePre_iff (tag : BorTag) (tags : ProtectedTags) (post : BorrowTree → Prop)
    (failure : BorrowTree.ProtectorReleaseStatus → BorrowTree → Prop) (tree : BorrowTree) :
    releasePre tag tags post failure tree ↔ resultPre post failure (tree.releaseProtector tag tags) := by
  simp only [releasePre, BorrowTree.releaseProtector, Id.run]
  cases sourceState : tree.indexOfTag tag with
  | none => simp [resultPre, pure, Pure.pure]
  | some source =>
    simp only [Std.Legacy.Range.forIn_eq_forIn_range']
    have sizeEq : ([:tree.locations.entries.size] : Std.Legacy.Range).size =
        tree.locations.entries.size := by simp [Std.Legacy.Range.size]
    simp only [sizeEq]
    clear sourceState sizeEq
    induction List.range' 0 tree.locations.entries.size generalizing tree with
    | nil =>
      simp only [segmentsPre, List.forIn_nil, bind, Bind.bind, pure, Pure.pure]
      rw [BorrowTree.MutationVerification.releaseExposurePre_iff]
      cases exposure : (tree.updateExposureForProtectorRelease tag).outcome <;>
        simp [exposure, resultPre]
    | cons position rest ih =>
      simp only [segmentsPre, segmentPre, List.forIn_cons, bind, Bind.bind, pure, Pure.pure]
      cases indexed : tree.locations.index position with
      | error => simp [resultPre]
      | ok segment =>
        cases found : segment.data.perms.get source with
        | none =>
          simp only [found]
          exact ih tree
        | some state =>
          cases association : state.permission.associatedAccess with
          | none =>
            simp only [found, association]
            exact ih tree
          | some kind =>
            cases accessed : state.accessed with
            | false =>
              simp only [found, association, accessed, Bool.false_eq_true, ↓reduceIte]
              exact ih tree
            | true =>
              simp only [found, association, accessed, ↓reduceIte]
              rw [← BorrowTree.RangeVerification.locationContract_iff]
              let visit := tree.performTreeAccessAt segment.data (some source) kind
                tags .SkipChildrenOfAccessed segment.range
              let mutation := tree.locations.setAtPos position visit.location
              cases updated : mutation.outcome with
              | error => simp [resultPre]
              | ok success =>
                cases success
                simp only
                cases failed : visit.status with
                | some error => simp [resultPre]
                | none =>
                  simp only
                  exact ih { tree with locations := mutation.state }

@[spec high] theorem spec_release (tag : BorTag) (tags : ProtectedTags)
    (post : Unit → BorrowTree → Prop) (failure : BorrowTree.ProtectorReleaseStatus → BorrowTree → Prop) :
    Triple (TreeBorrowsWP.release tag tags) (releasePre tag tags (post ()) failure) post failure := by
  apply Triple.iff.mpr
  intro tree safe
  have checked := (releasePre_iff tag tags (post ()) failure tree).mp safe
  simp only [wp, WP.wpTrans, TreeBorrowsWP.release, TreeBorrowsWP.mutation]
  cases result : (tree.releaseProtector tag tags).status <;> simpa [resultPre, result] using checked

section StackPop

variable {K User : Type} [DecidableEq K]
local notation "State" => MachineHooks.State K User
local notation "ErrorPost" => StepError → State → Prop

private def accessError (status : BorrowTree.BorrowTreeAccessStatus) : StepError :=
  match status with
  | .AccessFailure _ (.TransitionError ..)
  | .WildcardFailure _ (.TransitionError ..)
  | .WildcardFailure _ (.NoValidExposedReferences ..) =>
    .undefinedBehavior s!"Tree Borrows: {reprStr status}"
  | _ => .invalidProgram s!"Tree Borrows invariant: {reprStr status}"

/-- One stack protector entry commits its tree update before classifying its
release status. Dead entries advance directly. -/
def stackEntryPre (ensureTreeExtra : AllocId → MachineHooks.M K User Unit)
    (allocId : AllocId) (tag : BorTag) (next : State → Prop)
    (failure : ErrorPost) (state : State) : Prop :=
  match state.machine.memory.getAllocInfo allocId with
  | .error error => failure (.callback s!"protector allocation info: {reprStr error}") state
  | .ok info =>
    if info.kind == .liveData then
      RvalueWP.actionPre (ensureTreeExtra allocId) (fun _ ready =>
        let machine := ready.machine
        match machine.memory.live.find? (fun entry => entry.1 == allocId) with
        | none => failure (.invalidProgram "live protected allocation missing Tree Borrows extra") ready
        | some entry =>
          match machine.borrowTracker with
          | none => failure (.invalidProgram "borrow tracker removed during protector release") ready
          | some tracker =>
            let install (tree : BorrowTree) (finish : State → Prop) :=
              match machine.memory.setLiveAllocation allocId (entry.2.allocation.setExtra tree) with
              | .error error => failure (.callback s!"protector tree update: {reprStr error}") ready
              | .ok memory => finish { ready with machine := { machine with memory } }
            releasePre tag tracker.global.protectedTags (fun tree => install tree next)
              (fun status tree => install tree (failure (match status with
                | .AccessFailure _ status => accessError status
                | other => .invalidProgram s!"protector release invariant: {reprStr other}")))
              entry.2.allocation.extra)
        failure state
    else next state

def stackEntriesPre (ensureTreeExtra : AllocId → MachineHooks.M K User Unit)
    (next : State → Prop) (failure : ErrorPost) : List (AllocId × BorTag) → State → Prop
  | [], state => next state
  | (allocId, tag) :: rest, state =>
    stackEntryPre ensureTreeExtra allocId tag (stackEntriesPre ensureTreeExtra next failure rest) failure state

/-- The global protector map changes only after every entry has released.
Missing frame state and tracker removal use the actual retained state. -/
def beforeStackPopPre (ensureTreeExtra : AllocId → MachineHooks.M K User Unit)
    (post : State → Prop) (failure : ErrorPost) (state : State) : Prop :=
  if state.machine.borrowTracker.isSome then
    match state.stack.currentFrame? with
    | none => failure (.stack .emptyStack) state
    | some frame =>
      match frame.extra.borrowTracker with
      | none => failure (.invalidProgram "enabled borrow tracker missing frame state") state
      | some borrowFrame =>
        stackEntriesPre ensureTreeExtra (fun after =>
          match after.machine.borrowTracker with
          | none => failure (.invalidProgram "borrow tracker removed during stack pop") after
          | some tracker =>
            let tracker := { tracker with global := tracker.global.endCall borrowFrame }
            post { after with machine := { after.machine with borrowTracker := some tracker } })
          failure borrowFrame.protectedTags.toList state
  else post state

set_option maxHeartbeats 2000000 in
theorem beforeStackPopPre_iff (ensureTreeExtra : AllocId → MachineHooks.M K User Unit)
    (post : State → Prop) (failure : ErrorPost) (state : State) :
    beforeStackPopPre ensureTreeExtra post failure state ↔
      RvalueWP.actionPre (MachineHooks.beforeStackPopWithEnsure ensureTreeExtra)
        (fun _ => post) failure state := by
  simp only [beforeStackPopPre, MachineHooks.beforeStackPopWithEnsure, RvalueWP.actionPre,
    bind, Bind.bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get]
  split
  · rename_i enabled
    cases current : state.stack.currentFrame? with
    | none => simp [MachineHooks.currentFrame, current, bind, Bind.bind, EStateM.bind,
        get, getThe, MonadStateOf.get, EStateM.get]; rfl
    | some frame =>
      simp only [MachineHooks.currentFrame, current, bind, Bind.bind, EStateM.bind,
        get, getThe, MonadStateOf.get, EStateM.get, pure, Pure.pure, EStateM.pure]
      cases frameState : frame.extra.borrowTracker with
      | none => simp only; rfl
      | some borrowFrame =>
        simp only [← Array.forIn_toList, EStateM.pure, EStateM.bind, EStateM.get]
        clear enabled current frameState
        induction borrowFrame.protectedTags.toList generalizing state with
        | nil =>
          simp only [stackEntriesPre, List.forIn_nil, pure, Pure.pure, EStateM.pure]
          cases state.machine.borrowTracker <;> rfl
        | cons pair rest ih =>
          obtain ⟨allocId, tag⟩ := pair
          simp only [stackEntriesPre, stackEntryPre, List.forIn_cons, bind, Bind.bind, EStateM.bind, EStateM.get]
          cases info : state.machine.memory.getAllocInfo allocId with
          | error => simp only; rfl
          | ok infoValue =>
            simp only [pure, Pure.pure, EStateM.pure, EStateM.bind]
            by_cases live : (infoValue.kind == .liveData) = true
            · simp only [live, ite_true, RvalueWP.actionPre, EStateM.bind]
              cases ensured : ensureTreeExtra allocId state with
              | error => simp only
              | ok success ready =>
                cases success
                simp only [EStateM.get]
                cases entry : ready.machine.memory.live.find? (fun entry => entry.1 == allocId) with
                | none => simp only; rfl
                | some found =>
                  simp only [EStateM.bind, EStateM.pure]
                  cases tracker : ready.machine.borrowTracker with
                  | none => simp only; rfl
                  | some held =>
                    simp only [EStateM.bind, EStateM.pure]
                    rw [releasePre_iff]
                    let released := found.2.allocation.extra.releaseProtector tag held.global.protectedTags
                    cases installed : ready.machine.memory.setLiveAllocation allocId
                        (found.2.allocation.setExtra released.tree) with
                    | error =>
                      simp only [released] at installed
                      cases done : released.status <;> simp only [released] at done <;>
                        simp only [resultPre, done, installed, EStateM.bind] <;> rfl
                    | ok memory =>
                      simp only [released] at installed
                      cases done : released.status with
                      | Released =>
                        simp only [released] at done
                        simp only [resultPre, done, installed, EStateM.bind, EStateM.pure]
                        simp only [← tracker]
                        exact ih { ready with machine := { ready.machine with memory } }
                      | AccessFailure range status =>
                        simp only [released] at done
                        simp only [resultPre, done, installed, EStateM.bind, EStateM.pure]
                        simp only [← tracker]
                        cases status <;> rfl
                      | _ =>
                        simp only [released] at done
                        simp only [resultPre, done, installed, EStateM.bind, EStateM.pure]
                        simp only [← tracker]
                        rfl
            · simp only [live]
              exact ih state
  · rename_i disabled
    simp [pure, Pure.pure, EStateM.pure]

@[spec high] theorem spec_beforeStackPopWithEnsure (ensureTreeExtra : AllocId → MachineHooks.M K User Unit)
    (post : Unit → State → Prop) (onError : ErrorPost) :
    Triple (MachineHooks.beforeStackPopWithEnsure ensureTreeExtra)
      (beforeStackPopPre ensureTreeExtra (post ()) onError) post onError := by
  apply Triple.iff.mpr
  intro state checked
  have h := (beforeStackPopPre_iff ensureTreeExtra (post ()) onError state).mp checked
  simp only [wp, WP.wpTrans, RvalueWP.actionPre] at h ⊢
  cases executed : MachineHooks.beforeStackPopWithEnsure ensureTreeExtra state with
  | error => simpa only [executed] using h
  | ok value => cases value; simpa only [executed] using h

/-- Release all owned protectors before the frame-relevance cleanup and
the actual pop. Propagate the first error with its resulting state. -/
def popRawPre (retag : TypedRetag.Hooks K User)
    (post : Frame Provenance LocalLayout MachineHooks.FrameExtra → State → Prop)
    (onError : ErrorPost) (state : State) : Prop :=
  beforeStackPopPre retag.ensureTreeExtra
    (RvalueWP.actionPre FrameRelevance.beforeStackPop (fun _ after =>
      match after.stack.popFrame with
      | .error error => onError (.stack error) after
      | .ok (stack, frame) => post frame { after with stack }) onError)
    onError state

theorem popRawPre_iff (retag : TypedRetag.Hooks K User)
    (post : Frame Provenance LocalLayout MachineHooks.FrameExtra → State → Prop)
    (onError : ErrorPost) (state : State) :
    popRawPre retag post onError state ↔
      RvalueWP.actionPre (TypedMachineBindings.popRaw retag) post onError state := by
  unfold popRawPre TypedMachineBindings.popRaw
  rw [beforeStackPopPre_iff, RvalueWP.actionPre_bind]
  unfold RvalueWP.actionPre
  cases ran : MachineHooks.beforeStackPopWithEnsure retag.ensureTreeExtra state with
  | error => rfl
  | ok value ready =>
    cases value
    simp only
    cases relevance : FrameRelevance.beforeStackPop ready with
    | error => simp [relevance, bind, Bind.bind, EStateM.bind]
    | ok value after =>
      cases value
      cases popped : after.stack.popFrame <;>
        simp [relevance, popped, bind, Bind.bind, EStateM.bind, get,
          getThe, MonadStateOf.get, EStateM.get, pure, Pure.pure, EStateM.pure]
      all_goals rfl

@[spec high] theorem spec_popRaw (retag : TypedRetag.Hooks K User)
    (post : Frame Provenance LocalLayout MachineHooks.FrameExtra → State → Prop)
    (onError : ErrorPost) :
    Triple (TypedMachineBindings.popRaw retag) (popRawPre retag post onError) post onError := by
  apply Triple.iff.mpr
  intro state checked
  have h := (popRawPre_iff retag post onError state).mp checked
  simp only [wp, WP.wpTrans, RvalueWP.actionPre] at h ⊢
  cases executed : TypedMachineBindings.popRaw retag state <;> simpa only [executed] using h

end StackPop
end Miri.Verification.ProtectorReleaseWP
