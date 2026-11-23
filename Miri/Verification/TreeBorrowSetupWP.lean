import Miri.Interpreter.FunctionPointers
import Miri.Interpreter.PointerSource
import Miri.Interpreter.TypedRetag
import Std.Tactic.Do

/-! Symbolic root-tag setup and permission policy used by the production
allocation and retag paths. Successful or failed allocations retain the
actual tag and bookkeeping changes made before later machine effects. -/
namespace Miri.Verification.TreeBorrowSetupWP

open Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.MIR Std.WP
open Miri.TreeBorrows.RetagPolicy

attribute [spec] PlaceMachine.initializeAllocation
attribute [spec] PlaceMachine.allocateStackRaw PlaceMachine.allocateStack
attribute [spec] GlobalAllocationMachine.initExtra GlobalAllocationMachine.init
attribute [spec] PointerSource.globalRootPointer FunctionPointers.rootPointer

/-- Allocate the current tag and advance the counter, or report an overflow
at the original global state. -/
def newTagPre (state : GlobalState) (post : GlobalState → BorTag → Prop)
    (failure : GlobalStateError → Prop) : Prop :=
  match BorTag.succ state.nextPointerTag with
  | none => failure (.pointerTagOverflow state.nextPointerTag)
  | some next => post { state with nextPointerTag := next } state.nextPointerTag

theorem newTagPre_iff (state : GlobalState) (post : GlobalState → BorTag → Prop)
    (failure : GlobalStateError → Prop) :
    (match state.newPointerTag with
    | .ok (after, tag) => post after tag
    | .error error => failure error) ↔ newTagPre state post failure := by
  unfold GlobalState.newPointerTag newTagPre
  cases BorTag.succ state.nextPointerTag <;> rfl

/-- Repeated root lookups reuse the stored tag, including when the fresh-tag
counter is already exhausted. -/
def rootTagPre (state : GlobalState) (id : AllocId) (post : GlobalState → BorTag → Prop)
    (failure : GlobalStateError → Prop) : Prop :=
  match state.rootTag? id with
  | some tag => post state tag
  | none => newTagPre state
      (fun after tag => post { after with rootPointerTags := after.rootPointerTags.push (id, tag) } tag)
      failure

theorem rootTagPre_iff (state : GlobalState) (id : AllocId)
    (post : GlobalState → BorTag → Prop) (failure : GlobalStateError → Prop) :
    (match state.rootPointerTag id with
    | .ok (after, tag) => post after tag
    | .error error => failure error) ↔ rootTagPre state id post failure := by
  unfold GlobalState.rootPointerTag rootTagPre
  cases state.rootTag? id with
  | some tag => rfl
  | none =>
    dsimp only
    unfold newTagPre GlobalState.newPointerTag
    cases BorTag.succ state.nextPointerTag <;> rfl

/-- Call-owned tags are removed only after the ordered release accesses
succeeded. This recurrence preserves any tags owned by other call frames
that do not occur in the source frame's list. -/
def removeFrameTagsPre (post : ProtectedTags → Prop) :
    List (AllocId × BorTag) → ProtectedTags → Prop
  | [], tags => post tags
  | (_, tag) :: rest, tags => removeFrameTagsPre post rest (tags.remove tag)

private theorem removeFrameTagsPre_iff (post : ProtectedTags → Prop)
    (entries : List (AllocId × BorTag)) (tags : ProtectedTags) :
    post (entries.foldl (fun tags pair => tags.remove pair.2) tags) ↔
      removeFrameTagsPre post entries tags := by
  induction entries generalizing tags with
  | nil => rfl
  | cons pair rest ih =>
    rcases pair with ⟨id, tag⟩
    exact ih (tags.remove tag)

def endCallPre (state : GlobalState) (frame : FrameState) (post : GlobalState → Prop) : Prop :=
  removeFrameTagsPre (fun tags => post { state with protectedTags := tags })
    frame.protectedTags.toList state.protectedTags

theorem endCallPre_iff (state : GlobalState) (frame : FrameState) (post : GlobalState → Prop) :
    post (state.endCall frame) ↔ endCallPre state frame post := by
  unfold GlobalState.endCall endCallPre
  rw [← Array.foldl_toList]
  exact removeFrameTagsPre_iff (fun tags => post { state with protectedTags := tags }) _ _

/-- The retag policy pulls back through mode, pinning, interior mutability,
and implicit writes. Box function arguments get weak protectors. Shared and
mutable reference arguments get strong protectors. -/
def permissionPre (facts : TypeFacts) (kind : ReferenceKind) (mode : RetagMode)
    (config : PolicyConfig) (post : Option NewPermission → Prop) : Prop :=
  if mode == .None then post none
  else if (kind == .Mutable || kind == .Box) && !(facts.isUnpin && facts.isUnsafeUnpin) then
    post none
  else
    let entry := mode == .FnEntry
    let writes := entry && config.implicitWrites && !config.rustcNoWritable
    let permission (outside frozen : Bool) :=
      match kind with
      | .Shared => if frozen then .Frozen else .Cell
      | .Mutable | .Box =>
        if writes && !outside then .Unique
        else if entry || frozen then .ReservedFrz false else .ReservedIM
    let protector := if entry then
      some (if kind == .Box then ProtectorKind.WeakProtector else ProtectorKind.StrongProtector)
      else none
    post (some ⟨permission false true, permission false false, permission true facts.isFreeze,
      protector⟩)

theorem permissionPre_iff (facts : TypeFacts) (kind : ReferenceKind) (mode : RetagMode)
    (config : PolicyConfig) (post : Option NewPermission → Prop) :
    post (create facts kind mode config) ↔ permissionPre facts kind mode config post := by
  rcases facts with ⟨unpin, unsafeUnpin, freeze⟩
  cases unpin <;> cases unsafeUnpin <;> cases kind <;> cases mode <;> rfl

/-- The production order of compiler queries supplying the retag policy.
Each failing query keeps the concrete state returned by that query. -/
def newPermissionPre {K U : Type} (h : TypedRetag.Hooks K U) (pointee : TyId)
    (kind : ReferenceKind) (mode : RetagMode)
    (post : Option NewPermission → MachineHooks.State K U → Prop)
    (failure : StepError → MachineHooks.State K U → Prop) (before : MachineHooks.State K U) : Prop :=
  if mode == .None then post none before
  else
    wp (h.isUnpin pointee) (fun unpin s₁ =>
      wp (if unpin then h.isUnsafeUnpin pointee else pure false) (fun unsafeUnpin s₂ =>
        wp (h.typeIsFreeze pointee) (fun freeze s₃ =>
          let done := fun implicitWrites noWritable state =>
            permissionPre ⟨unpin, unsafeUnpin, freeze⟩ kind mode ⟨implicitWrites, noWritable⟩
              (fun result => post result state)
          if mode == .FnEntry then
            wp h.implicitWrites (fun writes s₄ =>
              wp MachineHooks.currentFrame (fun frame s₅ =>
                wp (h.instanceDefinition frame.functionInstance) (fun id s₆ =>
                  wp (if writes then h.rustcNoWritable id else pure false)
                    (fun noWritable => done writes noWritable) failure s₆) failure s₅) failure s₄)
              failure s₃
          else done false false s₃) failure s₂) failure s₁) failure before

private theorem joinBindBranches {E S A B : Type} (test : Prop) [Decidable test]
    (first second : EStateM E S A) (next : A → EStateM E S B) :
    (if test then EStateM.bind first next else EStateM.bind second next) =
      EStateM.bind (if test then first else second) next := by
  split <;> rfl

theorem newPermissionPre_iff {K U : Type} (h : TypedRetag.Hooks K U) (pointee : TyId)
    (kind : ReferenceKind) (mode : RetagMode)
    (post : Option NewPermission → MachineHooks.State K U → Prop)
    (failure : StepError → MachineHooks.State K U → Prop) (before : MachineHooks.State K U) :
    wp (TypedRetag.newPermission h pointee kind mode) post failure before ↔
      newPermissionPre h pointee kind mode post failure before := by
  unfold TypedRetag.newPermission newPermissionPre
  by_cases noRetag : (mode == .None) = true
  · simp only [noRetag, ↓reduceIte]; rfl
  · simp only [noRetag, Bool.false_eq_true, ↓reduceIte]
    simp only [wp, WP.wpTrans, bind, Bind.bind, EStateM.bind]
    cases unpinResult : h.isUnpin pointee before with
    | error => rfl
    | ok unpin s₁ =>
      dsimp only
      rw [joinBindBranches]
      simp only [EStateM.bind]
      cases unsafeResult : (if unpin then h.isUnsafeUnpin pointee else pure false) s₁ with
      | error => rfl
      | ok unsafeUnpin s₂ =>
        simp only [EStateM.bind]
        cases freezeResult : h.typeIsFreeze pointee s₂ with
        | error => rfl
        | ok freeze s₃ =>
          dsimp only
          by_cases entry : (mode == .FnEntry) = true
          · simp only [entry, ↓reduceIte]
            simp only [EStateM.bind]
            cases writesResult : h.implicitWrites s₃ with
            | error => rfl
            | ok writes s₄ =>
              simp only [EStateM.bind]
              cases frameResult : MachineHooks.currentFrame s₄ with
              | error => rfl
              | ok frame s₅ =>
                simp only [EStateM.bind]
                cases instanceResult : h.instanceDefinition frame.functionInstance s₅ with
                | error => rfl
                | ok id s₆ =>
                  cases writes
                  · simp only [Bool.false_eq_true, ↓reduceIte, pure, Pure.pure, EStateM.pure]
                    exact permissionPre_iff ⟨unpin, unsafeUnpin, freeze⟩ kind mode
                      ⟨false, false⟩ (fun result => post result s₆)
                  · simp only [↓reduceIte, EStateM.bind]
                    cases attributeResult : h.rustcNoWritable id s₆ with
                    | error => rfl
                    | ok noWritable s₇ =>
                      exact permissionPre_iff ⟨unpin, unsafeUnpin, freeze⟩ kind mode
                        ⟨true, noWritable⟩ (fun result => post result s₇)
          · simp only [entry, Bool.false_eq_true, ↓reduceIte]
            exact permissionPre_iff ⟨unpin, unsafeUnpin, freeze⟩ kind mode
              ⟨false, false⟩ (fun result => post result s₃)

@[spec high] theorem spec_newPermission {K U : Type} (h : TypedRetag.Hooks K U) (pointee : TyId)
    (kind : ReferenceKind) (mode : RetagMode)
    (post : Option NewPermission → MachineHooks.State K U → Prop)
    (failure : StepError → MachineHooks.State K U → Prop) :
    Triple (TypedRetag.newPermission h pointee kind mode)
      (newPermissionPre h pointee kind mode post failure) post failure := by
  apply Triple.iff.mpr
  intro before
  exact (newPermissionPre_iff h pointee kind mode post failure before).mpr

private def afterStackTagPre {K U : Type}
    (allocationTail : AllocId → Size → Align → PlaceMachine.MachineM K U Unit)
    (id : AllocId) (size : Size) (align : Align)
    (post : BorrowTree → PlaceMachine.Machine K U → Prop)
    (failure : StepError → PlaceMachine.Machine K U → Prop)
    (state : PlaceMachine.Machine K U) (tag : BorTag) : Prop :=
  let complete := wp (allocationTail id size align) (fun _ => post (BorrowTree.new tag size)) failure
  match state.dataRace with
  | none => complete state
  | some global =>
    match global.activeThreadState state.threads with
    | .error error => failure (.invalidProgram s!"allocation clocks: {repr error}") state
    | .ok (index, clocks) =>
      let length := Miri.Concurrency.ByteSize.ofU64 size.bytes.toNat
        (by have h := UInt64.toNat_lt size.bytes; omega)
      let allocation := Miri.Concurrency.VClockAlloc.newAllocation length (clocks.clock.index index) index
      complete { state with raceAllocations :=
        (state.raceAllocations.filter fun entry => entry.1 != id).push (id, allocation) }

/-- Fresh tree creation uses either the stable root tag or the disabled
tracker's dummy tag, then runs allocation clock and machine-tail effects. -/
def stackExtraPre {K U : Type}
    (allocationTail : AllocId → Size → Align → PlaceMachine.MachineM K U Unit)
    (id : AllocId) (size : Size) (align : Align)
    (post : BorrowTree → PlaceMachine.Machine K U → Prop)
    (failure : StepError → PlaceMachine.Machine K U → Prop) (before : PlaceMachine.Machine K U) : Prop :=
  let complete := afterStackTagPre allocationTail id size align post failure
  match before.borrowTracker with
  | none => complete before BorTag.one
  | some tracker =>
    rootTagPre tracker.global id
      (fun global tag => complete { before with borrowTracker := some { tracker with global } } tag)
      (fun error => failure (.resourceExhaustion s!"allocation root tag: {repr error}") before)

open Lean Elab Tactic Meta in
elab "finish_allocation_tail " tail:ident : tactic =>
  withMainContext do
    let target ← getMainTarget
    let tail ← Term.elabTerm tail none
    let some result := target.find? fun e => e.isApp && e.getAppFn == tail &&
        e.getAppNumArgs == 4 | throwError "allocation-tail result not found"
    let (variables, goal) ← (← getMainGoal).generalize #[{ expr := result }]
    let some generalized := variables[0]? | throwError "allocation-tail result was not generalized"
    let cases ← goal.cases generalized
    replaceMainGoal (cases.toList.map (·.mvarId))
    evalTactic (← `(tactic| all_goals rfl))

theorem stackExtraPre_iff {K U : Type}
    (allocationTail : AllocId → Size → Align → PlaceMachine.MachineM K U Unit)
    (id : AllocId) (size : Size) (align : Align)
    (post : BorrowTree → PlaceMachine.Machine K U → Prop)
    (failure : StepError → PlaceMachine.Machine K U → Prop) (before : PlaceMachine.Machine K U) :
    wp (PlaceMachine.initStackExtra allocationTail id size align) post failure before ↔
      stackExtraPre allocationTail id size align post failure before := by
  unfold PlaceMachine.initStackExtra stackExtraPre
  simp only [wp, WP.wpTrans, get, getThe, MonadStateOf.get, EStateM.get,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, set, MonadStateOf.set]
  cases before.borrowTracker
  case' none => simp only [EStateM.bind, EStateM.set, EStateM.pure]
  case' some tracker =>
    dsimp only
    rw [← rootTagPre_iff]
    cases tracker.global.rootPointerTag id
    case' error => rfl
    case' ok value =>
      rcases value with ⟨global, tag⟩
      simp only [EStateM.bind, EStateM.set, EStateM.pure]
  all_goals
    simp only [afterStackTagPre, wp, WP.wpTrans]
    cases races : before.dataRace with
    | none =>
      simp [EStateM.bind, EStateM.pure]
      finish_allocation_tail allocationTail
    | some global =>
      dsimp only
      cases global.activeThreadState before.threads with
      | error => rfl
      | ok value =>
        rcases value with ⟨index, clocks⟩
        simp [EStateM.bind, EStateM.pure, modify,
          modifyGet, MonadState.modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, races]
        finish_allocation_tail allocationTail

@[spec high] theorem spec_initStackExtra {K U : Type}
    (allocationTail : AllocId → Size → Align → PlaceMachine.MachineM K U Unit)
    (id : AllocId) (size : Size) (align : Align)
    (post : BorrowTree → PlaceMachine.Machine K U → Prop)
    (failure : StepError → PlaceMachine.Machine K U → Prop) :
    Triple (PlaceMachine.initStackExtra allocationTail id size align)
      (stackExtraPre allocationTail id size align post failure) post failure := by
  apply Triple.iff.mpr
  intro before
  exact (stackExtraPre_iff allocationTail id size align post failure before).mpr

end Miri.Verification.TreeBorrowSetupWP
