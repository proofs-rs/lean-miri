import duplicate_prefix.TypedBorrowSteps
namespace DuplicatePrefix.GeneralBorrowCanonicalReborrowSource
open Miri Miri.Memory Miri.ABI Miri.MIR Miri.Interpreter Miri.DataStructures Miri.TreeBorrows
open TypedRetagEntry
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
/-- The exact ForInStep-producing source body, including the final yield. -/
def sourceSegment {K U : Type} [DecidableEq K]
    (location : RetagPipeline.ResolvedLocation) (segment : RangeMapSegment Tree.LocationState) :
    MachineHooks.M K U (ForInStep PUnit) := do
  if let some access := segment.data.permission.associatedAccess then
    if access == .Write then
      let some entry := (← get).machine.memory.live.find? (fun entry => entry.1 == location.allocId)
        | throw (.invalidProgram "missing live allocation mutability")
      if entry.2.allocation.mutability == .Not then
        throw .retagWriteToReadOnly
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
  pure (.yield ())

def sourceReborrow {K User : Type} [DecidableEq K] (h : TypedRetag.Hooks K User) (budget : Nat)
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
    let provenance := some (Provenance.concrete location.allocId tag)
    if info.kind != .liveData then
      if size.bytes != 0 then throw (.invalidProgram "nonlive allocation with nonzero reborrow")
      return provenance
    let inside ← typed_inside h budget place size policy
    h.ensureTreeExtra location.allocId
    let _ ← forIn inside.iterAll () (fun segment _ => sourceSegment location segment)
    let tree ← typed_get_tree location.allocId
    let child := tree.newChild location.baseOffset location.parentProvenance tag inside
      policy.outsidePermission policy.protector.isSome
    typed_update_tree location.allocId child.tree
    typed_checked "reborrow child insertion" child.outcome
    return provenance

theorem source_equation {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K U) (budget : Nat) (place : MPlaceTy Provenance)
    (size : Size) (policy : RetagPolicy.NewPermission) (tag : BorTag) :
    TypedRetag.reborrow h budget place size policy tag =
      sourceReborrow h budget place size policy tag := by
  rfl
end DuplicatePrefix.GeneralBorrowCanonicalReborrowSource
