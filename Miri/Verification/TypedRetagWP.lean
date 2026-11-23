import Miri.Verification.TreeMutationWP

/-! Retagging reads and commits the allocation-local Tree Borrows state before
running the race detector, then installs the new child. -/
namespace Miri.Verification.TypedRetagWP

open Miri.ABI Miri.DataStructures Miri.Interpreter Miri.Memory
open Miri.TreeBorrows Miri.TreeBorrows.RetagPolicy Std.WP
open TypedRetag

variable {K U : Type}
local notation "State" => MachineHooks.State K U
local notation "Action" => MachineHooks.M K U
local notation "Failure" => StepError → State → Prop

/-- Pull success and failure predicates back through a single machine effect. -/
def effectPre {A : Type} (effect : Action A) (post : A → State → Prop)
    (failure : Failure) (before : State) : Prop :=
  match effect before with
  | .ok value after => post value after
  | .error error after => failure error after

private theorem bindPre {A B : Type} (action : Action A) (next : A → Action B)
    (post : B → State → Prop) (failure : Failure) (before : State) :
    effectPre (action >>= next) post failure before ↔
      effectPre action (fun value => effectPre (next value) post failure) failure before := by
  unfold effectPre
  simp only [bind, Bind.bind, EStateM.bind]
  cases action before <;> rfl

private theorem actionPostCongr {A : Type} (action : Action A)
    {post post' : A → State → Prop} (failure : Failure) (before : State)
    (same : ∀ value after, post value after ↔ post' value after) :
    effectPre action post failure before ↔ effectPre action post' failure before := by
  unfold effectPre
  cases action before with
  | error => rfl
  | ok value after => exact same value after

/-- The associated access is checked on the parent's tree. Even an access
error writes back the tree before returning, and a write-back failure takes
precedence over the access error. -/
def parentAccessPre [DecidableEq K] (location : RetagPipeline.ResolvedLocation)
    (offset length : Size) (access : AccessKind) (next : State → Prop)
    (failure : Failure) (before : State) : Prop :=
  effectPre (getTree location.allocId) (fun tree =>
    effectPre tracker (fun tracker state =>
      TreeBorrowsWP.accessPre tree location.parentProvenance offset length access
        tracker.global.protectedTags .VisitChildrenOfAccessed
        (fun after _ => effectPre (updateTree location.allocId after) (fun _ => next) failure state)
        (fun status after _ => effectPre (updateTree location.allocId after)
          (fun _ => failure (reborrowAccessError status)) failure state)) failure) failure before

private def parentAccess [DecidableEq K] (location : RetagPipeline.ResolvedLocation)
    (offset length : Size) (access : AccessKind) : Action Unit := do
  let tree ← getTree location.allocId
  let result := tree.performBorrowAccessRange location.parentProvenance offset length access
    (← tracker).global.protectedTags .VisitChildrenOfAccessed
  updateTree location.allocId result.tree
  if result.status != .Completed then throw (reborrowAccessError result.status)

theorem parentAccessPre_iff [DecidableEq K] (location : RetagPipeline.ResolvedLocation)
    (offset length : Size) (access : AccessKind) (next : State → Prop)
    (failure : Failure) (before : State) :
    parentAccessPre location offset length access next failure before ↔
      effectPre (parentAccess location offset length access) (fun _ => next) failure before := by
  unfold parentAccessPre parentAccess
  rw [bindPre]
  apply actionPostCongr
  intro tree state
  rw [bindPre]
  apply actionPostCongr
  intro borrow state
  rw [TreeBorrowsWP.accessPre_iff, bindPre]
  let result := tree.performBorrowAccessRange location.parentProvenance offset length access
    borrow.global.protectedTags .VisitChildrenOfAccessed
  change (match result.status with
    | .Completed => effectPre (updateTree location.allocId result.tree) (fun _ => next) failure state
    | status => effectPre (updateTree location.allocId result.tree)
        (fun _ => failure (reborrowAccessError status)) failure state) ↔ _
  cases status : result.status <;>
    apply actionPostCongr <;> intro _ after <;>
    simp [effectPre, status, pure, Pure.pure, EStateM.pure, throw, throwThe,
      MonadExceptOf.throw, EStateM.throw]

/-- The new tree is installed before checking the retag result. In
particular, a failed insertion can retain a replaced tag mapping. -/
def insertChildPre [DecidableEq K] (location : RetagPipeline.ResolvedLocation)
    (policy : NewPermission) (tag : BorTag) (inside : DedupRangeMap Tree.LocationState)
    (next : State → Prop) (failure : Failure) (before : State) : Prop :=
  effectPre (getTree location.allocId) (fun tree state =>
    BorrowTree.MutationVerification.insertChildPre tree location.baseOffset
      location.parentProvenance tag inside policy.outsidePermission policy.protector.isSome
      (fun after => effectPre (updateTree location.allocId after) (fun _ => next) failure state)
      (fun error after => effectPre (updateTree location.allocId after)
        (fun _ => failure (.invalidProgram s!"{"reborrow child insertion"}: {reprStr error}")) failure state))
      failure before

private def insertChild [DecidableEq K] (location : RetagPipeline.ResolvedLocation)
    (policy : NewPermission) (tag : BorTag)
    (inside : DedupRangeMap Tree.LocationState) : Action Unit := do
  let tree ← getTree location.allocId
  let child := tree.newChild location.baseOffset location.parentProvenance tag inside
    policy.outsidePermission policy.protector.isSome
  updateTree location.allocId child.tree
  checked "reborrow child insertion" child.outcome

theorem insertChildPre_iff [DecidableEq K] (location : RetagPipeline.ResolvedLocation)
    (policy : NewPermission) (tag : BorTag) (inside : DedupRangeMap Tree.LocationState)
    (next : State → Prop) (failure : Failure) (before : State) :
    insertChildPre location policy tag inside next failure before ↔
      effectPre (insertChild location policy tag inside) (fun _ => next) failure before := by
  unfold insertChildPre insertChild
  rw [bindPre]
  apply actionPostCongr
  intro tree state
  rw [BorrowTree.MutationVerification.insertChildPre_iff, bindPre]
  let result := tree.newChild location.baseOffset location.parentProvenance tag inside
    policy.outsidePermission policy.protector.isSome
  change BorrowTree.MutationVerification.childResultPre _ _ result ↔ _
  unfold BorrowTree.MutationVerification.childResultPre
  cases err : result.outcome <;>
    apply actionPostCongr <;> intro _ after <;>
    simp [effectPre, checked, pure, Pure.pure, EStateM.pure,
      throw, throwThe, MonadExceptOf.throw, EStateM.throw]

private def writableForReborrow (allocId : AllocId) (access : AccessKind) : Action Unit := do
  if access == .Write then
    let some entry := (← get).machine.memory.live.find? (fun entry => entry.1 == allocId)
      | throw (.invalidProgram "missing live allocation mutability")
    if entry.2.allocation.mutability == .Not then throw .retagWriteToReadOnly

private def raceAfterAccess (allocId : AllocId) (access : AccessKind)
    (offset length : Size) : Action Unit := do
  if length.bytes != 0 then
    match access with
    | .Read => MachineHooks.memoryRaceRead allocId (allocRange offset length) .Retag
    | .Write => MachineHooks.memoryRaceWrite allocId (allocRange offset length) .Retag

/-- Pull the continuation back across one freeze-permission segment. Accesses
are committed before the race detector runs, and each subsequent segment
observes the updated tree and machine. -/
def segmentPre [DecidableEq K] (location : RetagPipeline.ResolvedLocation)
    (segment : RangeMapSegment Tree.LocationState) (next : State → Prop)
    (failure : Failure) (before : State) : Prop :=
  match segment.data.permission.associatedAccess with
  | none => next before
  | some access =>
    effectPre (writableForReborrow location.allocId access) (fun _ =>
      effectPre (checked "reborrow offset" (Size.add location.baseOffset (Size.ofBytes segment.range.start)))
        (fun offset =>
          let length := Size.ofBytes (segment.range.stop - segment.range.start)
          parentAccessPre location offset length access
            (effectPre (raceAfterAccess location.allocId access offset length) (fun _ => next) failure)
            failure) failure) failure before

private def accessSegment [DecidableEq K] (location : RetagPipeline.ResolvedLocation)
    (segment : RangeMapSegment Tree.LocationState) : Action Unit := do
  if let some access := segment.data.permission.associatedAccess then
    writableForReborrow location.allocId access
    let offset ← checked "reborrow offset"
      (Size.add location.baseOffset (Size.ofBytes segment.range.start))
    let length := Size.ofBytes (segment.range.stop - segment.range.start)
    parentAccess location offset length access
    raceAfterAccess location.allocId access offset length

private theorem segmentPre_iff [DecidableEq K] (location : RetagPipeline.ResolvedLocation)
    (segment : RangeMapSegment Tree.LocationState) (next : State → Prop)
    (failure : Failure) (before : State) :
    segmentPre location segment next failure before ↔
      effectPre (accessSegment location segment) (fun _ => next) failure before := by
  unfold segmentPre accessSegment
  cases kind : segment.data.permission.associatedAccess with
  | none => rfl
  | some access =>
    rw [bindPre]
    apply actionPostCongr
    intro _ state
    rw [bindPre]
    apply actionPostCongr
    intro offset state
    rw [bindPre]
    exact parentAccessPre_iff _ _ _ _ _ _ _

/-- Visit permission segments in their source order and insert the child
only after every required parent access and race check succeeds. -/
def segmentsPre [DecidableEq K] (location : RetagPipeline.ResolvedLocation)
    (policy : NewPermission) (tag : BorTag) (inside : DedupRangeMap Tree.LocationState)
    (next : State → Prop) (failure : Failure) :
    List (RangeMapSegment Tree.LocationState) → State → Prop
  | [], state => insertChildPre location policy tag inside next failure state
  | segment :: rest, state =>
    segmentPre location segment (segmentsPre location policy tag inside next failure rest) failure state

private theorem segmentsPre_iff [DecidableEq K] (location : RetagPipeline.ResolvedLocation)
    (policy : NewPermission) (tag : BorTag) (inside : DedupRangeMap Tree.LocationState)
    (next : State → Prop) (failure : Failure)
    (segments : List (RangeMapSegment Tree.LocationState)) (before : State) :
    segmentsPre location policy tag inside next failure segments before ↔
      effectPre ((do
        for segment in segments do accessSegment location segment
        insertChild location policy tag inside) : Action Unit) (fun _ => next) failure before := by
  induction segments generalizing before with
  | nil =>
    simpa only [segmentsPre, List.forIn_nil, pure_bind] using
      insertChildPre_iff location policy tag inside next failure before
  | cons segment rest ih =>
    simp only [segmentsPre, List.forIn_cons, bind_assoc]
    rw [segmentPre_iff, bindPre]
    apply actionPostCongr
    intro _ state
    simpa only [pure_bind] using ih state

/-- Publish the protector before consulting the allocation kind or permissions. -/
def registerProtector (location : RetagPipeline.ResolvedLocation)
    (policy : NewPermission) (tag : BorTag) : Action Unit := do
  if let some protection := policy.protector then
    let frame ← MachineHooks.currentFrame
    let some borrowFrame := frame.extra.borrowTracker
      | throw (.invalidProgram "borrow frame missing")
    let old ← tracker
    let (global, borrowFrame) := old.global.addProtector borrowFrame location.allocId tag protection
    modify fun state => { state with machine := { state.machine with
      borrowTracker := some { old with global } } }
    MachineHooks.setCurrentFrame { frame with extra := { frame.extra with borrowTracker := some borrowFrame } }

private def continuationsAfterResolution [DecidableEq K] (h : Hooks K U) (budget : Nat)
    (place : MPlaceTy Provenance) (size : Size) (policy : NewPermission) (tag : BorTag)
    (location : RetagPipeline.ResolvedLocation) (post : Option Provenance → State → Prop)
    (failure : Failure) (before : State) : Prop :=
  let provenance := some (Provenance.concrete location.allocId tag)
  effectPre (h.logCreation place size policy tag (some location)) (fun _ =>
    effectPre (registerProtector location policy tag) (fun _ state =>
      effectPre (checked "allocation kind" (state.machine.memory.getAllocInfo location.allocId)) (fun info state =>
        if info.kind != .liveData then
          if size.bytes != 0 then failure (.invalidProgram "nonlive allocation with nonzero reborrow") state
          else post provenance state
        else
          effectPre (insidePermissions h budget place size policy) (fun inside =>
            effectPre (h.ensureTreeExtra location.allocId) (fun _ =>
              segmentsPre location policy tag inside (post provenance) failure inside.iterAll.toList)
              failure) failure state) failure state) failure) failure before

/-- Exact source-ordered precondition for a typed reborrow. Compiler and
machine callbacks retain their own success and failure continuations. -/
def reborrowPre [DecidableEq K] (h : Hooks K U) (budget : Nat)
    (place : MPlaceTy Provenance) (size : Size) (policy : NewPermission) (tag : BorTag)
    (post : Option Provenance → State → Prop) (failure : Failure) (before : State) : Prop :=
  effectPre (h.checkPtrAccess place.mplace.ptr size) (fun _ =>
    effectPre (h.resolveAllocation place.mplace.ptr) (fun location state =>
      match location with
      | none =>
        if size.bytes != 0 then failure (.invalidProgram "nonzero reborrow without allocation") state
        else effectPre (h.logCreation place size policy tag none)
          (fun _ => post place.mplace.ptr.provenance) failure state
      | some location => continuationsAfterResolution h budget place size policy tag location post failure state)
      failure) failure before

private def structuredReborrow [DecidableEq K] (h : Hooks K U) (budget : Nat)
    (place : MPlaceTy Provenance) (size : Size) (policy : NewPermission) (tag : BorTag) :
    Action (Option Provenance) := do
  h.checkPtrAccess place.mplace.ptr size
  let location ← h.resolveAllocation place.mplace.ptr
  match location with
  | none =>
    if size.bytes != 0 then throw (.invalidProgram "nonzero reborrow without allocation")
    h.logCreation place size policy tag none
    return place.mplace.ptr.provenance
  | some location =>
    h.logCreation place size policy tag (some location)
    registerProtector location policy tag
    let info ← checked "allocation kind" ((← get).machine.memory.getAllocInfo location.allocId)
    let provenance := some (Provenance.concrete location.allocId tag)
    if info.kind != .liveData then
      if size.bytes != 0 then throw (.invalidProgram "nonlive allocation with nonzero reborrow")
      return provenance
    let inside ← insidePermissions h budget place size policy
    h.ensureTreeExtra location.allocId
    let _ ← (do
      for segment in inside.iterAll.toList do accessSegment location segment
      insertChild location policy tag inside : Action Unit)
    return provenance

private theorem bindIf {A B : Type} (test : Prop) [Decidable test]
    (yes no : Action A) (next : A → Action B) :
    (if test then yes else no) >>= next =
      if test then yes >>= next else no >>= next := by
  by_cases h : test <;> simp [h]

private theorem bindThrow {A B : Type} (error : StepError) (next : A → Action B) :
    ((throw error : Action A) >>= next) = throw error := rfl

private theorem effectPre_eq_wp {A : Type} (action : Action A) (post : A → State → Prop)
    (failure : Failure) :
    effectPre action post failure = wp action post failure := by
  funext before
  simp only [effectPre, wp, WP.wpTrans]
  cases action before <;> rfl

private theorem registerThen {A : Type} (location : RetagPipeline.ResolvedLocation)
    (policy : NewPermission) (tag : BorTag) (next : Action A) :
    (registerProtector location policy tag >>= fun _ => next) = (do
      if let some protection := policy.protector then
        let frame ← MachineHooks.currentFrame
        let some borrowFrame := frame.extra.borrowTracker
          | throw (.invalidProgram "borrow frame missing")
        let old ← tracker
        let (global, borrowFrame) := old.global.addProtector borrowFrame location.allocId tag protection
        modify fun state => { state with machine := { state.machine with
          borrowTracker := some { old with global } } }
        MachineHooks.setCurrentFrame { frame with extra := { frame.extra with borrowTracker := some borrowFrame } }
      next) := by
  unfold registerProtector
  cases policy.protector with
  | none => simp only [pure_bind]
  | some protection =>
    simp only [bind_assoc]
    congr 1
    funext frame
    cases frame.extra.borrowTracker with
    | none => exact bindThrow _ _
    | some borrowFrame =>
      dsimp only
      simp only [bind_assoc]

private theorem segmentThen [DecidableEq K] {A : Type} (location : RetagPipeline.ResolvedLocation)
    (segment : RangeMapSegment Tree.LocationState) (next : Action A) :
    (accessSegment location segment >>= fun _ => next) = (do
      if let some access := segment.data.permission.associatedAccess then
        if access == .Write then
          let some entry := (← get).machine.memory.live.find? (fun entry => entry.1 == location.allocId)
            | throw (.invalidProgram "missing live allocation mutability")
          if entry.2.allocation.mutability == .Not then throw .retagWriteToReadOnly
        let offset ← checked "reborrow offset"
          (Size.add location.baseOffset (Size.ofBytes segment.range.start))
        let length := Size.ofBytes (segment.range.stop - segment.range.start)
        let tree ← getTree location.allocId
        let accessResult := tree.performBorrowAccessRange location.parentProvenance offset length access
          (← tracker).global.protectedTags .VisitChildrenOfAccessed
        updateTree location.allocId accessResult.tree
        if accessResult.status != .Completed then throw (reborrowAccessError accessResult.status)
        if length.bytes != 0 then
          match access with
          | .Read => MachineHooks.memoryRaceRead location.allocId (allocRange offset length) .Retag
          | .Write => MachineHooks.memoryRaceWrite location.allocId (allocRange offset length) .Retag
      next) := by
  unfold accessSegment writableForReborrow parentAccess raceAfterAccess
  cases segment.data.permission.associatedAccess with
  | none => simp only [pure_bind]
  | some access =>
    cases access with
    | Read =>
      simp only [show (AccessKind.Read == .Write) = false from rfl, Bool.false_eq_true,
        ↓reduceIte, bind_assoc, bindIf, bindThrow, pure_bind]
    | Write =>
      simp only [show (AccessKind.Write == .Write) = true from rfl, ↓reduceIte,
        bind_assoc, bindIf, bindThrow, pure_bind]
      congr 1
      funext state
      cases state.machine.memory.live.find? (fun entry => entry.1 == location.allocId) with
      | none => simp only [bindThrow]
      | some entry => simp only [bindIf, bindThrow, pure_bind]

private theorem structuredReborrow_eq [DecidableEq K] (h : Hooks K U) (budget : Nat)
    (place : MPlaceTy Provenance) (size : Size) (policy : NewPermission) (tag : BorTag) :
    structuredReborrow h budget place size policy tag = reborrow h budget place size policy tag := by
  simp only [structuredReborrow, reborrow, insertChild, ← Array.forIn_toList, bind_assoc,
    segmentThen, registerThen, bindThrow]
  with_unfolding_all rfl

private theorem effectPre_get (next : State → State → Prop)
    (failure : Failure) (before : State) :
    effectPre (get : Action State) next failure before ↔ next before before := by
  rfl

theorem reborrowPre_iff [DecidableEq K] (h : Hooks K U) (budget : Nat)
    (place : MPlaceTy Provenance) (size : Size) (policy : NewPermission) (tag : BorTag)
    (post : Option Provenance → State → Prop) (failure : Failure) (before : State) :
    reborrowPre h budget place size policy tag post failure before ↔
      wp (reborrow h budget place size policy tag) post failure before := by
  rw [← effectPre_eq_wp, ← structuredReborrow_eq]
  unfold reborrowPre structuredReborrow
  rw [bindPre]
  apply actionPostCongr
  intro _ state
  rw [bindPre]
  apply actionPostCongr
  intro location state
  cases location with
  | none =>
    dsimp only
    by_cases sizeCheck : (size.bytes != 0) = true
    · simp only [sizeCheck, ↓reduceIte, bindThrow]
      rfl
    · simp only [sizeCheck, Bool.false_eq_true, ↓reduceIte, bindPre]
      rfl
  | some location =>
    dsimp only
    unfold continuationsAfterResolution
    rw [bindPre]
    apply actionPostCongr
    intro _ state
    rw [bindPre]
    apply actionPostCongr
    intro _ state
    rw [bindPre, effectPre_get, bindPre]
    change effectPre (checked "allocation kind" (state.machine.memory.getAllocInfo location.allocId))
      _ failure state ↔ effectPre (checked "allocation kind" (state.machine.memory.getAllocInfo location.allocId))
      _ failure state
    apply actionPostCongr
    intro info state
    by_cases kindCheck : (info.kind != .liveData) = true
    · simp only [kindCheck, ↓reduceIte]
      by_cases sizeCheck : (size.bytes != 0) = true <;>
        simp only [sizeCheck, Bool.false_eq_true, ↓reduceIte, bindThrow] <;> rfl
    · simp only [kindCheck, Bool.false_eq_true, ↓reduceIte]
      rw [bindPre]
      apply actionPostCongr
      intro inside state
      rw [bindPre]
      apply actionPostCongr
      intro _ state
      rw [bindPre]
      exact segmentsPre_iff location policy tag inside _ failure inside.iterAll.toList state

@[spec high] theorem spec_reborrow [DecidableEq K] (h : Hooks K U) (budget : Nat)
    (place : MPlaceTy Provenance) (size : Size) (policy : NewPermission) (tag : BorTag)
    (post : Option Provenance → State → Prop) (failure : Failure) :
    Triple (reborrow h budget place size policy tag)
      (reborrowPre h budget place size policy tag post failure) post failure :=
  Triple.iff.mpr fun before => (reborrowPre_iff h budget place size policy tag post failure before).mp

end Miri.Verification.TypedRetagWP
