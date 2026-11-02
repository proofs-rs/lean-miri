import duplicate_prefix.GeneralBorrowFreshSharedPop
import duplicate_prefix.GeneralBorrowFreshSharedStageAttachAny
namespace DuplicatePrefix.GenericSharedPopPoolData
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralBorrowFreshSharedSequence DuplicatePrefix.GeneralBorrowFreshMixedChild
open DuplicatePrefix.GeneralBorrowFreshReleaseMixed DuplicatePrefix.GeneralBorrowFreshSharedPop
open DuplicatePrefix.GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

private theorem projection_size (tree : BorrowTree) (location : LocationTree) (tags : ProtectedTags) :
    (source_normal_projection tree location tags).topology.nodes.size = tree.nodes.data.size := by
  unfold_general_projection
  unfold_general_topology
  simp only [Array.size_map]

private theorem stage_size_le (tree : BorrowTree) (newTag : BorTag) (parent : UniIndex) (offset len : UInt64)
    (data : Data tree newTag parent offset len) (protections : ProtectedTags) (isProtected : Bool)
    (metadata : GeneralBorrowFreshStageMetadata.Output tree newTag parent offset len data protections isProtected) :
    (child data protections isProtected).tree.nodes.data.size ≤ tree.nodes.data.size+1 := by
  have extension := metadata.extension default default protections
  rcases extension with appended | reused
  · have length := appended.length
    simp only [projection_size] at length
    omega
  · have length := reused.length
    simp only [projection_size] at length
    omega

private theorem finish_second_data {K U : Type} [DecidableEq K]
    (globalKind : K) (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K U))
    (sync : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}})
    (state : MachineHooks.State K U) (tracker : MachineHooks.BorrowState)
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (enabled : state.machine.borrowTracker = some tracker) (current : state.stack.currentFrame? = some frame)
    (framed : frame.extra.borrowTracker = some borrowFrame)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (before middle : BorrowTree) (beforeTags : ProtectedTags) (target expr : UniIndex) (exprTag nextTag : BorTag) (offset len : UInt64)
    (second : Data middle nextTag expr offset len) (roomData : middle.nodes.data.size+1 ≤ 4294967296)
    (owned : OwnedOn (Combined middle beforeTags expr (extend (fun _ => true) expr.toNat)) offset (offset+len) middle.locations)
    (positive : offset.toNat < (offset+len).toNat) (exprUnheld : beforeTags.contains exprTag = false)
    (registeredTags : tracker.global.protectedTags = registered beforeTags nextTag true)
    (different : exprTag ≠ nextTag) (frameOwned : borrowFrame.protectedTags = #[(id,nextTag)])
    (targetMiddle exprMiddle : TreeNode) (targetPresent : middle.nodeAt target = some targetMiddle)
    (exprPresent : middle.nodeAt expr = some exprMiddle) (exprMiddleTag : exprMiddle.tag = exprTag)
    (firstAttach : ∀ location : LocationTree, GeneralBorrowFreshSharedPaths.Attach
      (source_normal_projection before location tracker.global.protectedTags).topology
      (source_normal_projection middle location tracker.global.protectedTags).topology target.toNat expr.toNat) :
    (read second beforeTags true).status = .Completed ∧ (child second beforeTags true).outcome = .ok () ∧
    ∃ released,
      let finalTree := (child second beforeTags true).tree
      let prepared := installed state id entry finalTree
      StackPopRelease.Plan tracker.global.protectedTags [(id,nextTag)] prepared.machine.memory
        (StackPopRelease.commitTree prepared.machine.memory id (withTree entry finalTree) released) ∧
      MachineHooks.beforeStackPopWithEnsure (GlobalAllocationMachine.ensure globalKind globals) prepared =
        .ok () {prepared with machine := {prepared.machine with
          memory := StackPopRelease.commitTree prepared.machine.memory id (withTree entry finalTree) released,
          borrowTracker := some {tracker with global := tracker.global.endCall borrowFrame}}} ∧
      OwnedOn (GeneralBorrowRange.LocationOwned released (tracker.global.endCall borrowFrame).protectedTags target .Write)
        offset (offset+len) released.locations ∧ (tracker.global.endCall borrowFrame).protectedTags.contains nextTag = false := by
  have completed := GeneralBorrowFreshSharedSequence.run middle nextTag expr offset len second beforeTags true
    (extend (fun _ => true) expr.toNat) owned
  have built := GeneralBorrowFreshStageMetadata.build middle nextTag expr offset len second beforeTags true
    (extend (fun _ => true) expr.toNat) owned
  obtain ⟨metadata⟩ : Nonempty (GeneralBorrowFreshStageMetadata.Output middle nextTag expr offset len second beforeTags true) := ⟨built⟩
  have sizeBound := stage_size_le middle nextTag expr offset len second beforeTags true metadata
  have fit : (child second beforeTags true).tree.nodes.data.size ≤ 4294967296 := by omega
  obtain ⟨targetFinal,targetFinalPresent,_,_⟩ := GeneralBorrowFreshSharedStagePaths.old_node middle nextTag expr offset len
    second beforeTags true (extend (fun _ => true) expr.toNat) owned target targetMiddle targetPresent
  obtain ⟨exprFinal,exprFinalPresent,exprFinalTag,_⟩ := GeneralBorrowFreshSharedStagePaths.old_node middle nextTag expr offset len
    second beforeTags true (extend (fun _ => true) expr.toNat) owned expr exprMiddle exprPresent
  obtain ⟨childFinal,childFinalPresent,childFinalTag,childFinalUnexposed⟩ := metadata.node
  have exprFinalUnheld : tracker.global.protectedTags.contains exprFinal.tag = false := by
    rw [exprFinalTag,exprMiddleTag,registeredTags]
    simp only [registered,↓reduceIte]
    rw [ProtectorInsertion.contains_other beforeTags nextTag exprTag .StrongProtector different,exprUnheld]
  have secondAttach := fun location => GeneralBorrowFreshSharedStageAttachAny.attach middle nextTag expr offset len second beforeTags true
    (extend (fun _ => true) expr.toNat) owned location location tracker.global.protectedTags
  have taggedOwned := completed.2.2.1
  rw [←registeredTags] at taggedOwned
  have answer := GeneralBorrowFreshSharedPop.runtime_data globalKind globals sync state tracker frame borrowFrame enabled current framed id nextTag entry
    (child second beforeTags true).tree frameOwned present before middle (index second) target expr second.root offset (offset+len)
    positive fit metadata.certificates.depth metadata.certificates.children childFinal childFinalPresent childFinalUnexposed
    (metadata.roots.trans second.roots) metadata.certificates.covered metadata.lookup metadata.well completed.2.2.2 targetFinal exprFinal
    targetFinalPresent exprFinalPresent childFinalTag exprFinalUnheld firstAttach secondAttach taggedOwned
  exact ⟨completed.1,completed.2.1,answer⟩

/-- Two actual shared stages and real protector release/pop from arbitrary
append/reuse Data. An initial node-capacity bound replaces append-only paths and
allocator assumptions; operation completion and restoration are conclusions. -/
theorem complete_data {K U : Type} [DecidableEq K]
    (globalKind : K) (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K U))
    (sync : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}})
    (state : MachineHooks.State K U) (tracker : MachineHooks.BorrowState)
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (enabled : state.machine.borrowTracker = some tracker) (current : state.stack.currentFrame? = some frame)
    (framed : frame.extra.borrowTracker = some borrowFrame)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (beforeTags : ProtectedTags) (target : UniIndex) (exprTag nextTag : BorTag) (offset len : UInt64)
    (first : Data entry.allocation.extra exprTag target offset len)
    (second : Data (child first beforeTags false).tree nextTag (index first) offset len)
    (secondParent : second.parentTag = exprTag)
    (roomData : entry.allocation.extra.nodes.data.size+1 ≤ 4294967295)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned entry.allocation.extra beforeTags target .Write)
      offset (offset+len) entry.allocation.extra.locations)
    (positive : offset.toNat < (offset+len).toNat)
    (exprUnheld : beforeTags.contains exprTag = false)
    (registeredTags : tracker.global.protectedTags = registered beforeTags nextTag true)
    (different : exprTag ≠ nextTag) (frameOwned : borrowFrame.protectedTags = #[(id,nextTag)]) :
      (read first beforeTags false).status = .Completed ∧ (child first beforeTags false).outcome = .ok () ∧
      (read second beforeTags true).status = .Completed ∧ (child second beforeTags true).outcome = .ok () ∧
      ∃ released,
        let finalTree := (child second beforeTags true).tree
        let prepared := installed state id entry finalTree
        StackPopRelease.Plan tracker.global.protectedTags [(id,nextTag)] prepared.machine.memory
          (StackPopRelease.commitTree prepared.machine.memory id (withTree entry finalTree) released) ∧
        MachineHooks.beforeStackPopWithEnsure (GlobalAllocationMachine.ensure globalKind globals) prepared =
          .ok () {prepared with machine := {prepared.machine with
            memory := StackPopRelease.commitTree prepared.machine.memory id (withTree entry finalTree) released,
            borrowTracker := some {tracker with global := tracker.global.endCall borrowFrame}}} ∧
        OwnedOn (GeneralBorrowRange.LocationOwned released (tracker.global.endCall borrowFrame).protectedTags target .Write)
          offset (offset+len) released.locations ∧
        (tracker.global.endCall borrowFrame).protectedTags.contains nextTag = false := by
  have initial : OwnedOn (Combined entry.allocation.extra beforeTags target (fun _ => true)) offset (offset+len) entry.allocation.extra.locations := by
    intro position valid pos lower upper
    exact write_combined entry.allocation.extra _ beforeTags target (owned position valid pos lower upper)
  have one := GeneralBorrowFreshSharedSequence.run entry.allocation.extra exprTag target offset len first beforeTags false (fun _ => true) initial
  have firstOwned := one.2.2.1
  have regFalse : registered beforeTags exprTag false = beforeTags := by simp only [registered,Bool.false_eq_true,↓reduceIte]
  rw [regFalse] at firstOwned
  have built := GeneralBorrowFreshStageMetadata.build entry.allocation.extra exprTag target offset len first beforeTags false (fun _ => true) initial
  obtain ⟨metadata⟩ : Nonempty (GeneralBorrowFreshStageMetadata.Output entry.allocation.extra exprTag target offset len first beforeTags false) := ⟨built⟩
  have sizeBound := stage_size_le entry.allocation.extra exprTag target offset len first beforeTags false metadata
  have middleRoom : (child first beforeTags false).tree.nodes.data.size+1 ≤ 4294967296 := by omega
  obtain ⟨targetMiddle,targetMiddlePresent,_,_⟩ := GeneralBorrowFreshSharedStagePaths.old_node entry.allocation.extra exprTag target offset len
    first beforeTags false (fun _ => true) initial target first.parentNode first.parentPresent
  obtain ⟨exprMiddle,exprMiddlePresent,exprMiddleTag,_⟩ := metadata.node
  have firstAttach := fun location => GeneralBorrowFreshSharedStageAttachAny.attach entry.allocation.extra exprTag target offset len first beforeTags false
    (fun _ => true) initial location location tracker.global.protectedTags
  have answer := finish_second_data globalKind globals sync state tracker frame borrowFrame enabled current framed id entry present
    entry.allocation.extra (child first beforeTags false).tree beforeTags target (index first) exprTag nextTag offset len second middleRoom
    firstOwned positive exprUnheld registeredTags different frameOwned targetMiddle exprMiddle targetMiddlePresent exprMiddlePresent exprMiddleTag firstAttach
  exact ⟨one.1,one.2.1,answer⟩
end DuplicatePrefix.GenericSharedPopPoolData
