import empty_function.UnitRetagResult
import empty_function.ChildObserved

/-! Error-aware zero-retag continuation from actual construction results.
Only current tree formation is needed; successful allocation derives freshness. -/
namespace EmptyFunction.UnitRetagObserved
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows Miri.TreeBorrows.Tree
open EmptyFunction.UnitRetag EmptyFunction.UnitRetagResult Miri.DataStructures
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem reborrow_zero_live_cases {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K U) (budget : Nat) (place : MPlaceTy Provenance)
    (frames : Array F) (frame : F) (borrowFrame : FrameState)
    (machine : MachineHooks.MachineState K U) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker)
    (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (offset : UInt64) (parent : ProvenanceExtra) (tag : BorTag)
    (check : h.checkPtrAccess place.mplace.ptr Size.ZERO (withCurrent frames frame machine) =
      .ok () (withCurrent frames frame machine))
    (resolve : h.resolveAllocation place.mplace.ptr (withCurrent frames frame machine) =
      .ok (some ⟨id,Size.ofBytes offset,parent⟩) (withCurrent frames frame machine))
    (log : h.logCreation = fun _ _ _ _ _ => pure ())
    (precise : h.preciseInteriorMut = pure false)
    (freeze : h.typeIsFreeze place.layout.ty = pure true)
    (info : AllocationInfo)
    (classified : machine.memory.getAllocInfo id = .ok info)
    (data : info.kind = .liveData)
    (ensuredMachine : MachineHooks.MachineState K U)
    (ensured : h.ensureTreeExtra id
      (withCurrent frames (registeredFrame frame borrowFrame id tag) (registeredMachine machine tracker tag)) =
      .ok () (withCurrent frames (registeredFrame frame borrowFrame id tag) ensuredMachine))
    (live : ensuredMachine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (currentTag : BorTag) (formed : TreeRuntimeInput.TreeFormed entry.allocation.extra currentTag)
    (protections : ProtectedTags) :
    (∃ tree, TypedRetag.reborrow h budget place Size.ZERO MachineHooks.protectionPolicy tag
        (withCurrent frames frame machine) =
        .ok (some (.concrete id tag)) (withCurrent frames (registeredFrame frame borrowFrame id tag)
          {ensuredMachine with memory := replaceTree ensuredMachine.memory id entry tree}) ∧
      tree.releaseProtector tag protections = ⟨tree,.Released⟩ ∧
      Preservation.OldNodeRights entry.allocation.extra tree) ∨
    (∃ reason tree, TypedRetag.reborrow h budget place Size.ZERO MachineHooks.protectionPolicy tag
        (withCurrent frames frame machine) =
        .error (.invalidProgram reason) (withCurrent frames (registeredFrame frame borrowFrame id tag)
          {ensuredMachine with memory := replaceTree ensuredMachine.memory id entry tree})) := by
  have actual := reborrow_zero_live_ensured h budget place frames frame borrowFrame machine tracker
    enabled frameBorrow id entry offset parent tag check resolve log precise freeze info classified data
    ensuredMachine ensured live
  let child := entry.allocation.extra.newChild (Size.ofBytes offset) parent tag
    (DedupRangeMap.new Size.ZERO ⟨.ReservedFrz false,false,.None⟩) (.ReservedFrz false) true
  change TypedRetag.reborrow h budget place Size.ZERO MachineHooks.protectionPolicy tag
      (withCurrent frames frame machine) =
    match child.outcome with
    | .ok () => .ok (some (.concrete id tag)) _
    | .error error => .error (.invalidProgram ("reborrow child insertion" ++ ": " ++ reprStr error)) _ at actual
  cases outcome : child.outcome with
  | error error =>
    apply Or.inr
    exact ⟨_,child.tree,by simpa only [outcome] using actual⟩
  | ok value =>
    cases value
    have created : child = ⟨child.tree,.ok ()⟩ := by
      cases current : child with
      | mk tree result =>
        have success : result = .ok () := by simpa only [current] using outcome
        cases success
        rfl
    have certificate : child.tree.releaseProtector tag protections = ⟨child.tree,.Released⟩ ∧
        Preservation.OldNodeRights entry.allocation.extra child.tree := by
      cases parent with
      | wildcard =>
        exact ChildObserved.wildcard entry.allocation.extra currentTag tag formed
          (Size.ofBytes offset) ⟨.ReservedFrz false,false,.None⟩ child.tree created protections
      | concrete parentTag =>
        exact ChildObserved.concrete entry.allocation.extra currentTag tag parentTag formed
          (Size.ofBytes offset) ⟨.ReservedFrz false,false,.None⟩ child.tree created protections
    exact Or.inl ⟨child.tree,by simpa only [outcome] using actual,certificate⟩

open Lean Elab Command in
run_cmd do
  let mut total : Nat := 0
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.startsWith "EmptyFunction.UnitRetagObserved." ||
        (name.toString.startsWith "_private." && name.toString.contains "UnitRetagObserved") ||
        name.toString.startsWith "EmptyFunction.ChildObserved." then
      total := total+1
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved observed zero-retag axiom {dependency} in {name}"
  logInfo m!"Audited {total} observed zero-retag declarations"
#print axioms reborrow_zero_live_cases
end EmptyFunction.UnitRetagObserved
