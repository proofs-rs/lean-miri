import duplicate_prefix.RetagPointerChecks
import duplicate_prefix.ProtectedRelease

/-! Exact source stack-pop protector release, including real live-allocation
ensure, per-row tree commits and deferred global `endCall` bookkeeping. -/
namespace DuplicatePrefix.StackPopRelease
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open Lean Meta Elab
set_option maxHeartbeats 8000000
set_option maxRecDepth 65536

private def helperName (suffix : String) : CoreM Name := do
  let names := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith suffix then some name else none
  match names with
  | [name] => pure name
  | _ => throwError "expected one source helper {suffix}"
elab "pop_fail" : term => do mkConstWithFreshMVarLevels (← helperName ".MachineHooks.fail")
elab "pop_access_error" : term => do return mkConst (← helperName ".MachineHooks.borrowAccessError")

/-- Definitionally the per-protector body of the production hook. It includes
its failure paths and never removes any global protector. -/
private def releaseRow {K U : Type} [DecidableEq K]
    (ensure : AllocId → MachineHooks.M K U Unit) (row : AllocId × BorTag) : MachineHooks.M K U (ForInStep PUnit) := do
  let (allocId, tag) := row
  let machine := (← get).machine
  let info ← match machine.memory.getAllocInfo allocId with
    | .error error => pop_fail "protector allocation info" error
    | .ok info => pure info
  if info.kind == .liveData then
    ensure allocId
    let machine := (← get).machine
    let entry ← match machine.memory.live.find? fun entry => entry.1 == allocId with
      | none => throw (.invalidProgram "live protected allocation missing Tree Borrows extra")
      | some entry => pure entry.2
    let tracker ← match machine.borrowTracker with
      | none => throw (.invalidProgram "borrow tracker removed during protector release")
      | some tracker => pure tracker
    let released := entry.allocation.extra.releaseProtector tag tracker.global.protectedTags
    let memory ← match machine.memory.setLiveAllocation allocId (entry.allocation.setExtra released.tree) with
      | .error error => pop_fail "protector tree update" error
      | .ok memory => pure memory
    modify fun state => {state with machine := {state.machine with memory}}
    match released.status with
    | .Released => pure ()
    | .AccessFailure _ status => throw (pop_access_error status)
    | other => throw (.invalidProgram s!"protector release invariant: {reprStr other}")
  pure (.yield PUnit.unit)

private def releaseRows {K U : Type} [DecidableEq K]
    (ensure : AllocId → MachineHooks.M K U Unit) (rows : List (AllocId × BorTag)) : MachineHooks.M K U PUnit :=
  forIn rows PUnit.unit (fun row _ => releaseRow ensure row)

private def finish {K U : Type} (frame : FrameState) : MachineHooks.M K U Unit := do
  let state ← get
  let tracker ← match state.machine.borrowTracker with
    | none => throw (.invalidProgram "borrow tracker removed during stack pop")
    | some tracker => pure tracker
  set {state with machine := {state.machine with
    borrowTracker := some {tracker with global := tracker.global.endCall frame}}}

private theorem source_factor {K U : Type} [DecidableEq K]
    (ensure : AllocId → MachineHooks.M K U Unit) (state : MachineHooks.State K U)
    (tracker : MachineHooks.BorrowState) (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (borrowFrame : FrameState)
    (enabled : state.machine.borrowTracker = some tracker)
    (current : state.stack.currentFrame? = some frame)
    (framed : frame.extra.borrowTracker = some borrowFrame) :
    MachineHooks.beforeStackPopWithEnsure ensure state =
      (do let _ ← releaseRows ensure borrowFrame.protectedTags.toList; finish borrowFrame) state := by
  have currentStep : MachineHooks.currentFrame state = .ok frame state := by
    unfold MachineHooks.currentFrame
    simp [current, get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure]
  unfold MachineHooks.beforeStackPopWithEnsure
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, enabled,
    Option.isSome_some, Bool.true_eq, ↓reduceIte, currentStep, framed, pure, EStateM.pure]
  simp only [← Array.forIn_toList]
  rfl

private theorem releaseRows_nil {K U : Type} [DecidableEq K]
    (ensure : AllocId → MachineHooks.M K U Unit) : releaseRows ensure [] = pure PUnit.unit := by
  simp [releaseRows]

/-- The exact filter/push performed by `MemoryState.setLiveAllocation`. -/
def commitTree {K : Type} (memory : MemoryState Provenance BorrowTree K) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree K) (tree : BorrowTree) : MemoryState Provenance BorrowTree K :=
  {memory with live := (memory.live.filter fun row => row.1 != id).push (id, {entry with allocation := entry.allocation.setExtra tree})}

def withMemory {K U : Type} (state : MachineHooks.State K U) (memory : MemoryState Provenance BorrowTree K) :
    MachineHooks.State K U := {state with machine := {state.machine with memory}}

@[simp] theorem withMemory_current {K U : Type} (state : MachineHooks.State K U) :
    withMemory state state.machine.memory = state := by
  cases state
  rfl
@[simp] theorem withMemory_twice {K U : Type} (state : MachineHooks.State K U)
    (first second : MemoryState Provenance BorrowTree K) :
    withMemory (withMemory state first) second = withMemory state second := rfl

private theorem row_live {K U : Type} [DecidableEq K]
    (globalKind : K)
    (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K U))
    (sync : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}})
    (state : MachineHooks.State K U) (tracker : MachineHooks.BorrowState)
    (id : AllocId) (tag : BorTag) (entry : LocalAllocation Provenance BorrowTree K) (tree : BorrowTree)
    (enabled : state.machine.borrowTracker = some tracker)
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (released : entry.allocation.extra.releaseProtector tag tracker.global.protectedTags = ⟨tree, .Released⟩) :
    releaseRow (GlobalAllocationMachine.ensure globalKind globals) (id, tag) state =
      .ok (.yield PUnit.unit) (withMemory state (commitTree state.machine.memory id entry tree)) := by
  have info := MemoryCopyBridge.live_alloc_info state.machine.memory id entry present
  have ensured := RetagPointerChecks.ensure_tree_live globalKind globals sync state id entry present
  have stored := MemoryCopyBridge.set_live_exact state.machine.memory id entry (entry.allocation.setExtra tree) present
  unfold releaseRow
  simp [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure,
    info, ensured, present, enabled, released, stored, modify, modifyGet, MonadStateOf.modifyGet,
    EStateM.modifyGet, withMemory, commitTree]

private theorem row_skipped {K U : Type} [DecidableEq K]
    (ensure : AllocId → MachineHooks.M K U Unit) (state : MachineHooks.State K U)
    (id : AllocId) (tag : BorTag) (info : AllocationInfo)
    (lookup : state.machine.memory.getAllocInfo id = .ok info) (notLive : info.kind ≠ .liveData) :
    releaseRow ensure (id, tag) state = .ok (.yield PUnit.unit) state := by
  unfold releaseRow
  simp [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure,
    lookup, beq_iff_eq, notLive]

/-- Structural heap and actual tree-release certificates in frame order.
All releases use the same still-registered global protector table. -/
inductive Plan {K : Type} (protections : ProtectedTags) :
    List (AllocId × BorTag) → MemoryState Provenance BorrowTree K → MemoryState Provenance BorrowTree K → Prop where
  | nil (memory) : Plan protections [] memory memory
  | skip (id tag info rows memory final)
      (lookup : memory.getAllocInfo id = .ok info) (notLive : info.kind ≠ .liveData)
      (tail : Plan protections rows memory final) : Plan protections ((id, tag) :: rows) memory final
  | live (id tag entry tree rows memory final)
      (present : memory.live.find? (fun row => row.1 == id) = some (id, entry))
      (released : entry.allocation.extra.releaseProtector tag protections = ⟨tree, .Released⟩)
      (tail : Plan protections rows (commitTree memory id entry tree) final) :
      Plan protections ((id, tag) :: rows) memory final

theorem plan_single_nonlive {K : Type} (protections : ProtectedTags)
    (memory : MemoryState Provenance BorrowTree K) (id : AllocId) (tag : BorTag) (info : AllocationInfo)
    (lookup : memory.getAllocInfo id = .ok info) (notLive : info.kind ≠ .liveData) :
    Plan protections [(id,tag)] memory memory :=
  .skip id tag info [] memory memory lookup notLive (.nil memory)

theorem plan_all_nonlive {K : Type} (protections : ProtectedTags)
    (memory : MemoryState Provenance BorrowTree K) (rows : List (AllocId × BorTag))
    (metadata : ∀ row ∈ rows, ∃ info, memory.getAllocInfo row.1 = .ok info ∧ info.kind ≠ .liveData) :
    Plan protections rows memory memory := by
  induction rows with
  | nil => exact .nil memory
  | cons row rows ih =>
    obtain ⟨info,lookup,notLive⟩ := metadata row (by simp)
    exact .skip row.1 row.2 info rows memory memory lookup notLive
      (ih (by intro entry member;exact metadata entry (by simp [member])))

private theorem rows_of_plan {K U : Type} [DecidableEq K]
    (globalKind : K)
    (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K U))
    (sync : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}})
    (protections : ProtectedTags) (rows : List (AllocId × BorTag))
    (initial final : MemoryState Provenance BorrowTree K) (plan : Plan protections rows initial final) :
    ∀ (state : MachineHooks.State K U) (tracker : MachineHooks.BorrowState),
      state.machine.memory = initial → state.machine.borrowTracker = some tracker →
      tracker.global.protectedTags = protections →
      releaseRows (GlobalAllocationMachine.ensure globalKind globals) rows state =
        .ok PUnit.unit (withMemory state final) := by
  induction plan with
  | nil memory =>
      intro state tracker memoryEq enabled tableEq
      simpa [releaseRows_nil, pure, EStateM.pure, ← memoryEq]
  | skip id tag info rows memory final lookup notLive tail ih =>
      intro state tracker memoryEq enabled tableEq
      have lookupState : state.machine.memory.getAllocInfo id = .ok info := by simpa [memoryEq] using lookup
      have head := row_skipped (GlobalAllocationMachine.ensure globalKind globals) state id tag info lookupState notLive
      have rest := ih state tracker memoryEq enabled tableEq
      unfold releaseRows at rest ⊢
      rw [List.forIn_cons]
      simpa only [bind, EStateM.bind, head, pure, EStateM.pure] using rest
  | live id tag entry tree rows memory final present released tail ih =>
      intro state tracker memoryEq enabled tableEq
      have presentState : state.machine.memory.live.find? (fun row => row.1 == id) = some (id, entry) := by
        simpa [memoryEq] using present
      have releaseState : entry.allocation.extra.releaseProtector tag tracker.global.protectedTags = ⟨tree, .Released⟩ := by
        simpa [tableEq] using released
      have head := row_live globalKind globals sync state tracker id tag entry tree enabled presentState releaseState
      rw [memoryEq] at head
      let next := withMemory state (commitTree memory id entry tree)
      have nextTracker : next.machine.borrowTracker = some tracker := by simpa [next, withMemory] using enabled
      have rest := ih next tracker rfl nextTracker tableEq
      unfold releaseRows at rest ⊢
      rw [List.forIn_cons]
      simpa only [bind, EStateM.bind, head, pure, EStateM.pure, next, withMemory_twice] using rest

/-- Source stack-pop success with exact heap commits and deferred protector
removal. The frame remains on the stack; raw frame removal is the next step. -/
theorem before_stack_pop_of_plan {K U : Type} [DecidableEq K]
    (globalKind : K)
    (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K U))
    (sync : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}})
    (state : MachineHooks.State K U) (tracker : MachineHooks.BorrowState)
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (enabled : state.machine.borrowTracker = some tracker)
    (current : state.stack.currentFrame? = some frame)
    (framed : frame.extra.borrowTracker = some borrowFrame)
    (final : MemoryState Provenance BorrowTree K)
    (plan : Plan tracker.global.protectedTags borrowFrame.protectedTags.toList state.machine.memory final) :
    MachineHooks.beforeStackPopWithEnsure (GlobalAllocationMachine.ensure globalKind globals) state =
      .ok () {state with machine := {state.machine with memory := final, borrowTracker := some {tracker with global := tracker.global.endCall borrowFrame}}} := by
  rw [source_factor _ state tracker frame borrowFrame enabled current framed]
  have rows := rows_of_plan globalKind globals sync tracker.global.protectedTags borrowFrame.protectedTags.toList
    state.machine.memory final plan state tracker rfl enabled rfl
  simp [bind, EStateM.bind, rows, finish, get, getThe, MonadStateOf.get, EStateM.get,
    pure, EStateM.pure, set, EStateM.set, withMemory, enabled]

theorem lookup_commit_same {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K) (tree : BorrowTree) :
    (commitTree memory id entry tree).live.find? (fun row => row.1 == id) =
      some (id, {entry with allocation := entry.allocation.setExtra tree}) := by
  simpa [commitTree] using MemoryCopyBridge.live_lookup_replaced memory id
    {entry with allocation := entry.allocation.setExtra tree}

theorem lookup_commit_other {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (id other : AllocId) (entry otherEntry : LocalAllocation Provenance BorrowTree K) (tree : BorrowTree)
    (distinct : other ≠ id)
    (present : memory.live.find? (fun row => row.1 == other) = some (other, otherEntry)) :
    (commitTree memory id entry tree).live.find? (fun row => row.1 == other) = some (other, otherEntry) := by
  have filtered : (memory.live.filter (fun row => row.1 != id)).find? (fun row => row.1 == other) =
      memory.live.find? (fun row => row.1 == other) := by
    rw [Array.find?_filter]
    congr 1
    funext row
    by_cases eqOther : (row.1 == other) = true
    · have equality : row.1 = other := beq_iff_eq.mp eqOther
      have neId : row.1 ≠ id := fun h => distinct (equality.symm.trans h)
      have keep : (row.1 != id) = true := by simpa using neId
      simp [eqOther, keep]
    · simp [eqOther]
  simp [commitTree, Array.find?_push, Ne.symm distinct, filtered, present]

theorem metadata_commit_other {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (id other : AllocId) (entry : LocalAllocation Provenance BorrowTree K) (tree : BorrowTree)
    (distinct : other ≠ id) :
    (commitTree memory id entry tree).getAllocInfo other = memory.getAllocInfo other := by
  have filtered : (memory.live.filter (fun row => row.1 != id)).find? (fun row => row.1 == other) =
      memory.live.find? (fun row => row.1 == other) := by
    rw [Array.find?_filter]
    congr 1
    funext row
    by_cases eqOther : (row.1 == other) = true
    · have equality : row.1 = other := beq_iff_eq.mp eqOther
      have neId : row.1 ≠ id := fun h => distinct (equality.symm.trans h)
      have keep : (row.1 != id) = true := by simpa using neId
      simp [eqOther,keep]
    · simp [eqOther]
  have liveEq : (commitTree memory id entry tree).live.find? (fun row => row.1 == other) =
      memory.live.find? (fun row => row.1 == other) := by
    simp [commitTree,Array.find?_push,Ne.symm distinct,filtered]
  unfold MemoryState.getAllocInfo
  rw [liveEq]
  rfl

/-- A nonempty single-protector pop, retaining the real allocation commit. -/
theorem single_live {K U : Type} [DecidableEq K]
    (globalKind : K)
    (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K U))
    (sync : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}})
    (state : MachineHooks.State K U) (tracker : MachineHooks.BorrowState)
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (enabled : state.machine.borrowTracker = some tracker)
    (current : state.stack.currentFrame? = some frame)
    (framed : frame.extra.borrowTracker = some borrowFrame)
    (id : AllocId) (tag : BorTag) (entry : LocalAllocation Provenance BorrowTree K) (tree : BorrowTree)
    (owned : borrowFrame.protectedTags = #[(id, tag)])
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (released : entry.allocation.extra.releaseProtector tag tracker.global.protectedTags = ⟨tree, .Released⟩) :
    MachineHooks.beforeStackPopWithEnsure (GlobalAllocationMachine.ensure globalKind globals) state =
      .ok () {state with machine := {state.machine with memory := commitTree state.machine.memory id entry tree, borrowTracker := some {tracker with global := tracker.global.endCall borrowFrame}}} := by
  apply before_stack_pop_of_plan globalKind globals sync state tracker frame borrowFrame enabled current framed
  rw [owned]
  exact Plan.live id tag entry tree [] state.machine.memory _ present released (Plan.nil _)

/-- Two live protectors, with the second lookup performed after the first
source-ordered tree commit. The global table is unchanged until both finish. -/
theorem two_live {K U : Type} [DecidableEq K]
    (globalKind : K)
    (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K U))
    (sync : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}})
    (state : MachineHooks.State K U) (tracker : MachineHooks.BorrowState)
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (enabled : state.machine.borrowTracker = some tracker)
    (current : state.stack.currentFrame? = some frame)
    (framed : frame.extra.borrowTracker = some borrowFrame)
    (id1 id2 : AllocId) (tag1 tag2 : BorTag)
    (entry1 entry2 : LocalAllocation Provenance BorrowTree K) (tree1 tree2 : BorrowTree)
    (owned : borrowFrame.protectedTags = #[(id1, tag1), (id2, tag2)])
    (present1 : state.machine.memory.live.find? (fun row => row.1 == id1) = some (id1, entry1))
    (released1 : entry1.allocation.extra.releaseProtector tag1 tracker.global.protectedTags = ⟨tree1, .Released⟩)
    (present2 : (commitTree state.machine.memory id1 entry1 tree1).live.find? (fun row => row.1 == id2) = some (id2, entry2))
    (released2 : entry2.allocation.extra.releaseProtector tag2 tracker.global.protectedTags = ⟨tree2, .Released⟩) :
    MachineHooks.beforeStackPopWithEnsure (GlobalAllocationMachine.ensure globalKind globals) state =
      .ok () {state with machine := {state.machine with
        memory := commitTree (commitTree state.machine.memory id1 entry1 tree1) id2 entry2 tree2, borrowTracker := some {tracker with global := tracker.global.endCall borrowFrame}}} := by
  apply before_stack_pop_of_plan globalKind globals sync state tracker frame borrowFrame enabled current framed
  rw [owned]
  exact Plan.live id1 tag1 entry1 tree1 [(id2, tag2)] state.machine.memory _ present1 released1
    (Plan.live id2 tag2 entry2 tree2 [] _ _ present2 released2 (Plan.nil _))

theorem two_live_distinct {K U : Type} [DecidableEq K]
    (globalKind : K)
    (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K U))
    (sync : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}})
    (state : MachineHooks.State K U) (tracker : MachineHooks.BorrowState)
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (enabled : state.machine.borrowTracker = some tracker)
    (current : state.stack.currentFrame? = some frame)
    (framed : frame.extra.borrowTracker = some borrowFrame)
    (id1 id2 : AllocId) (tag1 tag2 : BorTag)
    (entry1 entry2 : LocalAllocation Provenance BorrowTree K) (tree1 tree2 : BorrowTree)
    (owned : borrowFrame.protectedTags = #[(id1, tag1), (id2, tag2)])
    (different : id2 ≠ id1)
    (present1 : state.machine.memory.live.find? (fun row => row.1 == id1) = some (id1, entry1))
    (released1 : entry1.allocation.extra.releaseProtector tag1 tracker.global.protectedTags = ⟨tree1, .Released⟩)
    (present2 : state.machine.memory.live.find? (fun row => row.1 == id2) = some (id2, entry2))
    (released2 : entry2.allocation.extra.releaseProtector tag2 tracker.global.protectedTags = ⟨tree2, .Released⟩) :
    MachineHooks.beforeStackPopWithEnsure (GlobalAllocationMachine.ensure globalKind globals) state =
      .ok () {state with machine := {state.machine with
        memory := commitTree (commitTree state.machine.memory id1 entry1 tree1) id2 entry2 tree2, borrowTracker := some {tracker with global := tracker.global.endCall borrowFrame}}} := by
  exact two_live globalKind globals sync state tracker frame borrowFrame enabled current framed
    id1 id2 tag1 tag2 entry1 entry2 tree1 tree2 owned present1 released1
    (lookup_commit_other state.machine.memory id1 id2 entry1 entry2 tree1 different present2) released2

theorem remove_preserves_other (tags : ProtectedTags) (target removed : BorTag)
    (distinct : target ≠ removed) : (tags.remove removed).get target = tags.get target := by
  have filtered : (tags.entries.filter (fun row => row.1 != removed)).find? (fun row => row.1 == target) =
      tags.entries.find? (fun row => row.1 == target) := by
    rw [Array.find?_filter]
    congr 1
    funext row
    by_cases hit : (row.1 == target) = true
    · have equal : row.1 = target := beq_iff_eq.mp hit
      have different : row.1 ≠ removed := fun h => distinct (equal.symm.trans h)
      have keep : (row.1 != removed) = true := by simpa using different
      simp [hit, keep]
    · simp [hit]
  simp [ProtectedTags.get, ProtectedTags.remove, filtered]

private theorem fold_remove_get (rows : List (AllocId × BorTag)) (tags : ProtectedTags) (target : BorTag) :
    (rows.foldl (fun tags row => tags.remove row.2) tags).get target =
      if target ∈ rows.map Prod.snd then none else tags.get target := by
  induction rows generalizing tags with
  | nil => simp
  | cons row rows ih =>
      rw [List.foldl_cons, ih]
      by_cases hit : target = row.2
      · subst target
        by_cases later : row.2 ∈ rows.map Prod.snd <;> simp [later]
      · have other := remove_preserves_other tags target row.2 hit
        by_cases later : target ∈ rows.map Prod.snd
        · have all : target ∈ (row :: rows).map Prod.snd := List.mem_cons_of_mem _ later
          simp only [if_pos later, if_pos all]
        · have notAll : target ∉ (row :: rows).map Prod.snd := by
            intro member
            rcases List.mem_cons.mp member with equal | member
            · exact hit equal
            · exact later member
          simp only [if_neg later, if_neg notAll, other]

/-- Every frame-owned tag is removed only after the complete source release
loop. Unrelated global entries retain their previous protector kind. -/
theorem end_call_get (global : GlobalState) (frame : FrameState) (target : BorTag) :
    (global.endCall frame).protectedTags.get target =
      if target ∈ frame.protectedTags.toList.map Prod.snd then none else global.protectedTags.get target := by
  unfold GlobalState.endCall
  simp only [← Array.foldl_toList]
  exact fold_remove_get _ _ _

theorem end_call_contains (global : GlobalState) (frame : FrameState) (target : BorTag) :
    (global.endCall frame).protectedTags.contains target =
      if target ∈ frame.protectedTags.toList.map Prod.snd then false else global.protectedTags.contains target := by
  unfold ProtectedTags.contains
  rw [end_call_get]
  by_cases owned : target ∈ frame.protectedTags.toList.map Prod.snd <;> simp [owned]

#print axioms end_call_get
#print axioms end_call_contains
#print axioms single_live
#print axioms two_live
#print axioms two_live_distinct
#print axioms before_stack_pop_of_plan
end DuplicatePrefix.StackPopRelease

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.StackPopRelease.before_stack_pop_of_plan,
      ``DuplicatePrefix.StackPopRelease.single_live, ``DuplicatePrefix.StackPopRelease.two_live,
      ``DuplicatePrefix.StackPopRelease.two_live_distinct, ``DuplicatePrefix.StackPopRelease.end_call_get,
      ``DuplicatePrefix.StackPopRelease.end_call_contains] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"

open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.StackPopRelease.plan_single_nonlive, ``DuplicatePrefix.StackPopRelease.plan_all_nonlive,
      ``DuplicatePrefix.StackPopRelease.metadata_commit_other] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved axiom {dependency}"
