import duplicate_prefix.GeneralBorrowCausalGraphFormation
import duplicate_prefix.GeneralBorrowTypedTreeUpdateCausalFrame
import duplicate_prefix.GeneralBorrowEffectfulRetagCausalOrder
import duplicate_prefix.GeneralBorrowCanonicalRaceCausalFrame
import duplicate_prefix.GeneralBorrowCanonicalReborrowSource
namespace DuplicatePrefix.GeneralBorrowCanonicalParentLoopCausalFrame
open Miri Miri.Memory Miri.ABI Miri.MIR Miri.Interpreter Miri.DataStructures Miri.TreeBorrows
open TypedRetagEntry GeneralBorrowEffectfulTreeUpdateFrame GeneralBorrowTypedTreeUpdateCausalFrame GeneralBorrowCanonicalRetagQueryFrame
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
/-- Exact memory/TB/race suffix of one canonical reborrow segment. -/
def parentCore {K U : Type} [DecidableEq K]
    (location : RetagPipeline.ResolvedLocation) (segment : RangeMapSegment Tree.LocationState)
    (access : AccessKind) : MachineHooks.M K U Unit := do
  let offset ← typed_checked "reborrow offset"
    (Size.add location.baseOffset (Size.ofBytes segment.range.start))
  let length := Size.ofBytes (segment.range.stop - segment.range.start)
  let tree ← typed_get_tree location.allocId
  let accessResult := tree.performBorrowAccessRange location.parentProvenance offset length access
    (← (typed_tracker (K:=K) (User:=U))).global.protectedTags .VisitChildrenOfAccessed
  typed_update_tree location.allocId accessResult.tree
  if accessResult.status != .Completed then throw (typed_access_error accessResult.status)
  if length.bytes != 0 then
    match access with
    | .Read => MachineHooks.memoryRaceRead location.allocId (allocRange offset length) .Retag
    | .Write => MachineHooks.memoryRaceWrite location.allocId (allocRange offset length) .Retag

/-- Canonical segment mutability guard. Connecting the factored segment to
the exact fused TypedRetag ForInStep body is a separate equality theorem. -/
def mutabilityGuard {K U : Type} (location : RetagPipeline.ResolvedLocation)
    (access : AccessKind) : MachineHooks.M K U Unit := do
  if access == .Write then
    let some entry := (← get).machine.memory.live.find? (fun entry => entry.1 == location.allocId)
      | throw (.invalidProgram "missing live allocation mutability")
    if entry.2.allocation.mutability == .Not then throw .retagWriteToReadOnly

def parentSegment {K U : Type} [DecidableEq K]
    (location : RetagPipeline.ResolvedLocation) (segment : RangeMapSegment Tree.LocationState) :
    MachineHooks.M K U Unit := do
  if let some access := segment.data.permission.associatedAccess then
    mutabilityGuard location access
    parentCore location segment access

/-- Node/tag-map-stable data property; a proof invariant, not a valid-input
contract and not target success or safety. -/
def FrameStable (P : AllocId → BorrowTree → Prop) : Prop :=
  ∀ id before after, P id before → after.nodes = before.nodes →
    after.tagMapping = before.tagMapping → P id after

theorem formed_stable : FrameStable (fun _ => GeneralBorrowCausalGraphFormation.Formed) := by
  intro id before after formed nodes mapping
  apply GeneralBorrowCausalGraphFormation.Formed.frame formed
  intro index node present
  exact ⟨node,by simpa only [nodes] using present,rfl,rfl⟩

def Preserves {K U A : Type} (P : AllocId → BorrowTree → Prop)
    (action : MachineHooks.M K U A) : Prop :=
  ∀ state, AllTrees P state.machine.memory → Holds P (action state)

theorem bind_preserves {K U A B : Type} (P : AllocId → BorrowTree → Prop)
    (action : MachineHooks.M K U A) (next : A → MachineHooks.M K U B)
    (first : Preserves P action) (second : ∀ value, Preserves P (next value)) :
    Preserves P (action >>= next) := by
  intro state before
  have maintained := first state before
  cases actual : action state with
  | ok value changed =>
    simp only [bind,EStateM.bind,actual]
    exact second value changed (by simpa only [actual,Holds] using maintained)
  | error error changed =>
    simpa only [bind,EStateM.bind,actual,Holds] using maintained


theorem core_preserves {K U : Type} [DecidableEq K]
    (P : AllocId → BorrowTree → Prop) (stable : FrameStable P)
    (location : RetagPipeline.ResolvedLocation) (segment : RangeMapSegment Tree.LocationState)
    (access : AccessKind) : Preserves P (parentCore location segment access : MachineHooks.M K U Unit) := by
  intro state before
  unfold parentCore
  unfold_typed ".TypedRetag.checked"
  cases added : Size.add location.baseOffset (Size.ofBytes segment.range.start) with
  | error error => simp only [added,bind,EStateM.bind];exact before
  | ok offset =>
    simp only [added,bind,EStateM.bind,pure,EStateM.pure]
    unfold_typed ".TypedRetag.getTree"
    unfold_typed ".TypedRetag.tracker"
    simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure]
    cases found : state.machine.memory.live.find? (fun row => row.1 == location.allocId) with
    | none => simp only [found,bind,EStateM.bind,pure,EStateM.pure];exact before
    | some row =>
      simp only [found,bind,EStateM.bind,pure,EStateM.pure]
      cases enabled : state.machine.borrowTracker with
      | none => simp only [enabled,bind,EStateM.bind,pure,EStateM.pure];exact before
      | some tracker =>
        simp only [enabled,bind,EStateM.bind,pure,EStateM.pure]
        have key : row.1 = location.allocId := by simpa only [beq_iff_eq] using Array.find?_some found
        have original := before row (Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some found))
        rw [key] at original
        have frame := GeneralBorrowEffectfulRetagCausalOrder.access_frame row.2.allocation.extra
          location.parentProvenance offset (Size.ofBytes (segment.range.stop-segment.range.start)) access
          tracker.global.protectedTags .VisitChildrenOfAccessed
        generalize accessed : row.2.allocation.extra.performBorrowAccessRange location.parentProvenance offset
          (Size.ofBytes (segment.range.stop-segment.range.start)) access tracker.global.protectedTags .VisitChildrenOfAccessed = result at frame ⊢
        obtain ⟨nodes,mapping⟩ := frame
        have replacement : P location.allocId result.tree := stable _ _ _ original nodes mapping
        have maintained := update_preserves state P location.allocId result.tree before replacement
        cases updated : typed_update_tree location.allocId result.tree state with
        | error error changed =>
          simpa only [updated,Holds] using maintained
        | ok value changed =>
          have next : AllTrees P changed.machine.memory := by simpa only [updated,Holds] using maintained
          simp only [updated,bind,EStateM.bind,pure,EStateM.pure]
          cases done : (result.status != .Completed) with
          | true => simpa only [done,↓reduceIte,bind,EStateM.bind,pure,EStateM.pure,throw,MonadExceptOf.throw,throwThe,EStateM.throw,Holds] using next
          | false =>
            simp only [done,Bool.false_eq_true,↓reduceIte]
            cases nonzero : ((Size.ofBytes (segment.range.stop-segment.range.start)).bytes != 0) with
            | false => simpa only [nonzero,Bool.false_eq_true,↓reduceIte,bind,EStateM.bind,pure,EStateM.pure,Holds] using next
            | true =>
              simp only [nonzero,↓reduceIte]
              cases access with
              | Read => exact GeneralBorrowCanonicalRaceCausalFrame.read_preserves P changed _ _ _ next
              | Write => exact GeneralBorrowCanonicalRaceCausalFrame.write_preserves P changed _ _ _ next

theorem readonly_preserves {K U A : Type} (P : AllocId → BorrowTree → Prop)
    (action : MachineHooks.M K U A) (readonly : ReadOnly action) : Preserves P action := by
  intro state before
  have after : AllTrees P (retained (action state)).machine.memory := by
    rw [readonly state]
    exact before
  cases actual : action state <;> simpa only [actual,retained,Holds] using after

theorem segment_preserves {K U : Type} [DecidableEq K]
    (P : AllocId → BorrowTree → Prop) (stable : FrameStable P)
    (location : RetagPipeline.ResolvedLocation) (segment : RangeMapSegment Tree.LocationState) :
    Preserves P (parentSegment location segment : MachineHooks.M K U Unit) := by
  unfold parentSegment
  cases associated : segment.data.permission.associatedAccess with
  | none => exact readonly_preserves P _ (pure_readonly _)
  | some access =>
    apply bind_preserves P _ _
    · apply readonly_preserves P _
      intro state
      unfold mutabilityGuard
      cases write : (access == .Write) with
      | false => simp only [write,Bool.false_eq_true,↓reduceIte];rfl
      | true =>
        simp only [write,↓reduceIte,get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind]
        cases found : state.machine.memory.live.find? (fun row => row.1 == location.allocId) with
        | none => simp only [found];rfl
        | some row =>
          simp only [found]
          cases mutable : (row.2.allocation.mutability == .Not) <;>
            simp only [mutable,Bool.false_eq_true,↓reduceIte] <;> rfl
    · intro _
      exact core_preserves P stable location segment access

theorem list_preserves {K U A B : Type} (P : AllocId → BorrowTree → Prop)
    (items : List A) (scan : A → B → MachineHooks.M K U (ForInStep B))
    (step : ∀ item ∈ items, ∀ initial, Preserves P (scan item initial)) (initial : B) :
    Preserves P (forIn items initial scan) := by
  induction items generalizing initial with
  | nil => exact readonly_preserves P _ (pure_readonly _)
  | cons item rest ih =>
    rw [List.forIn_cons]
    apply bind_preserves P _ _ (step item (by simp) initial)
    intro next
    cases next with
    | done result => exact readonly_preserves P _ (pure_readonly _)
    | yield result => exact ih (fun other member state => step other (by simp [member]) state) result

theorem loop_preserves {K U : Type} [DecidableEq K]
    (P : AllocId → BorrowTree → Prop) (stable : FrameStable P)
    (location : RetagPipeline.ResolvedLocation) (inside : DedupRangeMap Tree.LocationState) :
    Preserves P (show MachineHooks.M K U Unit from do
      for segment in inside.iterAll do parentSegment location segment) := by
  simp only [← Array.forIn_toList]
  apply bind_preserves P
  · apply list_preserves
    intro segment member initial
    apply bind_preserves P _ _ (segment_preserves P stable location segment)
    intro _
    exact readonly_preserves P _ (pure_readonly _)
  · intro _
    exact readonly_preserves P _ (pure_readonly _)

end DuplicatePrefix.GeneralBorrowCanonicalParentLoopCausalFrame
