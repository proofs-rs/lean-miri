import duplicate_prefix.GeneralBorrowFreshSharedNext
import duplicate_prefix.GeneralBorrowFreshSharedLifetime
import duplicate_prefix.GeneralBorrowFreshSharedStagePaths
namespace DuplicatePrefix.GeneralBorrowFreshSharedPop
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralBorrowFreshSharedSequence DuplicatePrefix.GeneralBorrowFreshMixedChild
open DuplicatePrefix.GeneralBorrowFreshReleaseMixed
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

def withTree {K : Type} (entry : LocalAllocation Provenance BorrowTree K) (tree : BorrowTree) :=
  {entry with allocation := entry.allocation.setExtra tree}

def installed {K U : Type} (state : MachineHooks.State K U) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree K) (tree : BorrowTree) : MachineHooks.State K U :=
  StackPopRelease.withMemory state (StackPopRelease.commitTree state.machine.memory id entry tree)

private theorem release_complete (result : BorrowTree.ProtectorReleaseResult) (done : result.status = .Released) :
    result = ⟨result.tree,.Released⟩ := by
  cases result with | mk tree status => cases done;rfl

private theorem runtime {K U : Type} [DecidableEq K]
    (globalKind : K)
    (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K U))
    (sync : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}})
    (state : MachineHooks.State K U) (tracker : MachineHooks.BorrowState)
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (enabled : state.machine.borrowTracker = some tracker)
    (current : state.stack.currentFrame? = some frame) (framed : frame.extra.borrowTracker = some borrowFrame)
    (id : AllocId) (tag : BorTag) (entry : LocalAllocation Provenance BorrowTree K) (finalTree : BorrowTree)
    (frameOwned : borrowFrame.protectedTags = #[(id,tag)])
    (_present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (before middle : BorrowTree) (anchor target expr root : UniIndex) (lower upper : UInt64)
    (positive : lower.toNat < upper.toNat) (fits : finalTree.nodes.data.size ≤ 4294967296)
    (depth : GeneralBorrowExposure.ParentDepth finalTree.nodes)
    (children : GeneralBorrowGraph.ChildNodes finalTree)
    (anchorNode : TreeNode) (anchorPresent : finalTree.nodeAt anchor = some anchorNode)
    (notExposed : anchorNode.isExposed = false) (roots : finalTree.roots = #[root])
    (covered : GeneralBorrowGraph.RootsCover finalTree)
    (tagPresent : finalTree.indexOfTag tag = some anchor)
    (well : finalTree.locations.WellFormed)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin finalTree anchor .Read lower upper)
    (targetNode exprNode : TreeNode)
    (targetPresent : finalTree.nodeAt target = some targetNode)
    (exprPresent : finalTree.nodeAt expr = some exprNode)
    (childTag : anchorNode.tag = tag)
    (exprUnheld : tracker.global.protectedTags.contains exprNode.tag = false)
    (first : ∀ location : LocationTree, GeneralBorrowFreshSharedPaths.Attach
      (source_normal_projection before location tracker.global.protectedTags).topology
      (source_normal_projection middle location tracker.global.protectedTags).topology target.toNat expr.toNat)
    (second : ∀ location : LocationTree, GeneralBorrowFreshSharedPaths.Attach
      (source_normal_projection middle location tracker.global.protectedTags).topology
      (source_normal_projection finalTree location tracker.global.protectedTags).topology expr.toNat anchor.toNat)
    (owned : OwnedOn (GeneralBorrowFreshReleaseMixed.Combined finalTree tracker.global.protectedTags anchor (GeneralBorrowFreshSharedPrefix.labels expr anchor))
      lower upper finalTree.locations) :
    ∃ released,
      let prepared := installed state id entry finalTree
      StackPopRelease.Plan tracker.global.protectedTags [(id,tag)] prepared.machine.memory
        (StackPopRelease.commitTree prepared.machine.memory id (withTree entry finalTree) released) ∧
      MachineHooks.beforeStackPopWithEnsure (GlobalAllocationMachine.ensure globalKind globals) prepared =
        .ok () {prepared with machine := {prepared.machine with
          memory := StackPopRelease.commitTree prepared.machine.memory id (withTree entry finalTree) released,
          borrowTracker := some {tracker with global := tracker.global.endCall borrowFrame}}} ∧
      OwnedOn (GeneralBorrowRange.LocationOwned released (tracker.global.endCall borrowFrame).protectedTags target .Write)
        lower upper released.locations ∧ (tracker.global.endCall borrowFrame).protectedTags.contains tag = false := by
  have paths := fun location => GeneralBorrowFreshSharedPaths.two_step _ _ _ target.toNat expr.toNat anchor.toNat
    (first location) (second location)
  have registered : (id,anchorNode.tag) ∈ borrowFrame.protectedTags.toList := by rw [frameOwned,childTag];simp
  have restore := GeneralBorrowFreshSharedPrefix.restore_data finalTree tracker.global borrowFrame
    target expr anchor targetNode exprNode anchorNode targetPresent exprPresent anchorPresent id registered exprUnheld
    (fun location => (paths location).1) (fun location => (paths location).2.1) (fun location => (paths location).2.2)
  let released := finalTree.releaseProtector tag tracker.global.protectedTags
  have ready := GeneralBorrowFreshReleaseMixed.release_shared_mixed finalTree tracker.global.protectedTags tag anchor root
    (GeneralBorrowFreshSharedPrefix.labels expr anchor) lower upper positive fits depth children anchorNode anchorPresent
    notExposed roots covered tagPresent (GeneralBorrowFreshActiveWithin.active_on finalTree anchor .Read lower upper well active) owned
  change released.status = .Released ∧ released.tree = {finalTree with locations := released.tree.locations} ∧
    OwnedOn (Combined released.tree tracker.global.protectedTags anchor (GeneralBorrowFreshSharedPrefix.labels expr anchor))
      lower upper released.tree.locations at ready
  have restoreReleased : GeneralBorrowFreshLifetimeRestore.RestoreTo released.tree tracker.global.protectedTags
      (tracker.global.endCall borrowFrame).protectedTags anchor target (GeneralBorrowFreshSharedPrefix.labels expr anchor) := by
    rw [ready.2.1]
    exact GeneralBorrowFreshLifetimeRestore.restore_map finalTree released.tree.locations _ _ anchor target _ restore
  have restored := GeneralBorrowFreshLifetimeRestore.restore_owned_on released.tree tracker.global.protectedTags
    (tracker.global.endCall borrowFrame).protectedTags (GeneralBorrowRelease.end_call_weakens tracker.global borrowFrame)
    anchor target _ restoreReleased lower upper ready.2.2
  have releaseEq : finalTree.releaseProtector tag tracker.global.protectedTags = ⟨released.tree,.Released⟩ := by
    exact release_complete released ready.1
  let finalEntry := withTree entry finalTree
  let prepared := installed state id entry finalTree
  have found : prepared.machine.memory.live.find? (fun row => row.1 == id) = some (id,finalEntry) :=
    StackPopRelease.lookup_commit_same state.machine.memory id entry finalTree
  have releasedEntry : finalEntry.allocation.extra.releaseProtector tag tracker.global.protectedTags = ⟨released.tree,.Released⟩ := by
    simpa only [finalEntry,withTree,Allocation.setExtra,Allocation.mapExtra] using releaseEq
  have plan := StackPopRelease.Plan.live id tag finalEntry released.tree [] prepared.machine.memory _ found releasedEntry (StackPopRelease.Plan.nil _)
  have popped := StackPopRelease.single_live globalKind globals sync prepared tracker frame borrowFrame enabled current framed
    id tag finalEntry released.tree frameOwned found releasedEntry
  refine ⟨released.tree,plan,popped,restored,?_⟩
  apply GeneralBorrowRelease.end_call_owned_absent tracker.global borrowFrame id tag
  rw [frameOwned]
  simp

/-- Public graph/data-only access to the generic actual stack-pop proof. -/
theorem runtime_data {K U : Type} [DecidableEq K]
    (globalKind : K)
    (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K U))
    (sync : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}})
    (state : MachineHooks.State K U) (tracker : MachineHooks.BorrowState)
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (enabled : state.machine.borrowTracker = some tracker)
    (current : state.stack.currentFrame? = some frame) (framed : frame.extra.borrowTracker = some borrowFrame)
    (id : AllocId) (tag : BorTag) (entry : LocalAllocation Provenance BorrowTree K) (finalTree : BorrowTree)
    (frameOwned : borrowFrame.protectedTags = #[(id,tag)])
    (_present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (before middle : BorrowTree) (anchor target expr root : UniIndex) (lower upper : UInt64)
    (positive : lower.toNat < upper.toNat) (fits : finalTree.nodes.data.size ≤ 4294967296)
    (depth : GeneralBorrowExposure.ParentDepth finalTree.nodes)
    (children : GeneralBorrowGraph.ChildNodes finalTree)
    (anchorNode : TreeNode) (anchorPresent : finalTree.nodeAt anchor = some anchorNode)
    (notExposed : anchorNode.isExposed = false) (roots : finalTree.roots = #[root])
    (covered : GeneralBorrowGraph.RootsCover finalTree)
    (tagPresent : finalTree.indexOfTag tag = some anchor)
    (well : finalTree.locations.WellFormed)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin finalTree anchor .Read lower upper)
    (targetNode exprNode : TreeNode)
    (targetPresent : finalTree.nodeAt target = some targetNode)
    (exprPresent : finalTree.nodeAt expr = some exprNode)
    (childTag : anchorNode.tag = tag)
    (exprUnheld : tracker.global.protectedTags.contains exprNode.tag = false)
    (first : ∀ location : LocationTree, GeneralBorrowFreshSharedPaths.Attach
      (source_normal_projection before location tracker.global.protectedTags).topology
      (source_normal_projection middle location tracker.global.protectedTags).topology target.toNat expr.toNat)
    (second : ∀ location : LocationTree, GeneralBorrowFreshSharedPaths.Attach
      (source_normal_projection middle location tracker.global.protectedTags).topology
      (source_normal_projection finalTree location tracker.global.protectedTags).topology expr.toNat anchor.toNat)
    (owned : OwnedOn (GeneralBorrowFreshReleaseMixed.Combined finalTree tracker.global.protectedTags anchor (GeneralBorrowFreshSharedPrefix.labels expr anchor))
      lower upper finalTree.locations) :
    ∃ released,
      let prepared := installed state id entry finalTree
      StackPopRelease.Plan tracker.global.protectedTags [(id,tag)] prepared.machine.memory
        (StackPopRelease.commitTree prepared.machine.memory id (withTree entry finalTree) released) ∧
      MachineHooks.beforeStackPopWithEnsure (GlobalAllocationMachine.ensure globalKind globals) prepared =
        .ok () {prepared with machine := {prepared.machine with
          memory := StackPopRelease.commitTree prepared.machine.memory id (withTree entry finalTree) released,
          borrowTracker := some {tracker with global := tracker.global.endCall borrowFrame}}} ∧
      OwnedOn (GeneralBorrowRange.LocationOwned released (tracker.global.endCall borrowFrame).protectedTags target .Write)
        lower upper released.locations ∧ (tracker.global.endCall borrowFrame).protectedTags.contains tag = false := by
  exact runtime globalKind globals sync state tracker frame borrowFrame enabled current framed id tag entry finalTree frameOwned _present before middle anchor target expr root lower upper positive fits depth children anchorNode anchorPresent notExposed roots covered tagPresent well active targetNode exprNode targetPresent exprPresent childTag exprUnheld first second owned

private theorem one_fits (old final nodes : Nat) (aligned : final = nodes)
    (push : final = old+1) (fits : old ≤ 4294967295) : nodes ≤ 4294967296 := by omega

private theorem finish_second {K U : Type} [DecidableEq K]
    (globalKind : K) (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K U))
    (sync : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}})
    (state : MachineHooks.State K U) (tracker : MachineHooks.BorrowState)
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (enabled : state.machine.borrowTracker = some tracker) (current : state.stack.currentFrame? = some frame)
    (framed : frame.extra.borrowTracker = some borrowFrame)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (before middle : BorrowTree) (beforeTags : ProtectedTags) (target expr : UniIndex) (exprTag nextTag : BorTag) (offset len : UInt64)
    (second : Data middle nextTag expr offset len) (noFree : middle.tagMapping.deassigned.back? = none)
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
  have fitsBefore : middle.tagMapping.mapping.size ≤ 4294967295 := by
    cases second.slot with
    | append _ _ fits => exact fits
    | reuse candidate available bounded vacant slack => rw [noFree] at available;cases available
  have allocator := metadata.allocator noFree
  have fit := one_fits _ _ _ allocator.2.1 allocator.2.2 fitsBefore
  obtain ⟨targetFinal,targetFinalPresent,_,_⟩ := GeneralBorrowFreshSharedStagePaths.old_node middle nextTag expr offset len
    second beforeTags true (extend (fun _ => true) expr.toNat) owned target targetMiddle targetPresent
  obtain ⟨exprFinal,exprFinalPresent,exprFinalTag,_⟩ := GeneralBorrowFreshSharedStagePaths.old_node middle nextTag expr offset len
    second beforeTags true (extend (fun _ => true) expr.toNat) owned expr exprMiddle exprPresent
  obtain ⟨childFinal,childFinalPresent,childFinalTag,childFinalUnexposed⟩ := metadata.node
  have exprFinalUnheld : tracker.global.protectedTags.contains exprFinal.tag = false := by
    rw [exprFinalTag,exprMiddleTag,registeredTags]
    simp only [registered,↓reduceIte]
    rw [ProtectorInsertion.contains_other beforeTags nextTag exprTag .StrongProtector different,exprUnheld]
  have secondAttach := fun location => GeneralBorrowFreshSharedStagePaths.attach middle nextTag expr offset len second beforeTags true
    (extend (fun _ => true) expr.toNat) owned noFree location location tracker.global.protectedTags
  have taggedOwned := completed.2.2.1
  rw [←registeredTags] at taggedOwned
  have answer := runtime globalKind globals sync state tracker frame borrowFrame enabled current framed id nextTag entry
    (child second beforeTags true).tree frameOwned present before middle (index second) target expr second.root offset (offset+len)
    positive fit metadata.certificates.depth metadata.certificates.children childFinal childFinalPresent childFinalUnexposed
    (metadata.roots.trans second.roots) metadata.certificates.covered metadata.lookup metadata.well completed.2.2.2 targetFinal exprFinal
    targetFinalPresent exprFinalPresent childFinalTag exprFinalUnheld firstAttach secondAttach taggedOwned
  exact ⟨completed.1,completed.2.1,answer⟩

/-- Compose two actual append shared stages with the real helper-frame release.
All tree postconditions, ancestry paths and restoration conditions are derived
from initial mutable ownership and allocator data. Runtime bookkeeping is an
explicit boundary: the template frame owns exactly the fresh FnEntry protector,
and its global protector table is the actual fresh registration. Installing the
proved final tree is exposed so a function trace can supply this memory update. -/
theorem complete {K U : Type} [DecidableEq K]
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
    (noFree : entry.allocation.extra.tagMapping.deassigned.back? = none)
    (room : entry.allocation.extra.tagMapping.mapping.size+1 ≤ 4294967295)
    (freshTag : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping nextTag)
    (freshProtector : GeneralBorrowProtector.Fresh entry.allocation.extra nextTag) (different : exprTag ≠ nextTag)
    (cleanFuture : Every (fun location : LocationTree => location.perms.get (GeneralBorrowFreshSharedNext.future entry.allocation.extra) = none)
      entry.allocation.extra.locations)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned entry.allocation.extra beforeTags target .Write)
      offset (offset+len) entry.allocation.extra.locations)
    (positive : offset.toNat < (offset+len).toNat)
    (exprUnheld : beforeTags.contains exprTag = false)
    (registeredTags : tracker.global.protectedTags = registered beforeTags nextTag true)
    (frameOwned : borrowFrame.protectedTags = #[(id,nextTag)]) :
    let choice := GeneralBorrowFreshSharedNext.next entry.allocation.extra beforeTags target exprTag nextTag offset len
      first noFree room freshTag freshProtector different cleanFuture owned
    let second := choice.val;
      index second = GeneralBorrowFreshSharedNext.future entry.allocation.extra ∧
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
  generalize nextEq : GeneralBorrowFreshSharedNext.next entry.allocation.extra beforeTags target exprTag nextTag offset len
    first noFree room freshTag freshProtector different cleanFuture owned = choice
  rcases choice with ⟨second,nextIndex⟩
  dsimp only at ⊢
  have initial : OwnedOn (Combined entry.allocation.extra beforeTags target (fun _ => true)) offset (offset+len) entry.allocation.extra.locations := by
    intro position valid pos lower upper
    exact write_combined entry.allocation.extra _ beforeTags target (owned position valid pos lower upper)
  have one := GeneralBorrowFreshSharedSequence.run entry.allocation.extra exprTag target offset len first beforeTags false (fun _ => true) initial
  have firstOwned := one.2.2.1
  have regFalse : registered beforeTags exprTag false = beforeTags := by simp only [registered,Bool.false_eq_true,↓reduceIte]
  rw [regFalse] at firstOwned
  have built := GeneralBorrowFreshStageMetadata.build entry.allocation.extra exprTag target offset len first beforeTags false (fun _ => true) initial
  obtain ⟨metadata⟩ : Nonempty (GeneralBorrowFreshStageMetadata.Output entry.allocation.extra exprTag target offset len first beforeTags false) := ⟨built⟩
  have allocator := metadata.allocator noFree
  obtain ⟨targetMiddle,targetMiddlePresent,_,_⟩ := GeneralBorrowFreshSharedStagePaths.old_node entry.allocation.extra exprTag target offset len
    first beforeTags false (fun _ => true) initial target first.parentNode first.parentPresent
  obtain ⟨exprMiddle,exprMiddlePresent,exprMiddleTag,_⟩ := metadata.node
  have firstAttach := fun location => GeneralBorrowFreshSharedStagePaths.attach entry.allocation.extra exprTag target offset len first beforeTags false
    (fun _ => true) initial noFree location location tracker.global.protectedTags
  have answer := finish_second globalKind globals sync state tracker frame borrowFrame enabled current framed id entry present
    entry.allocation.extra (child first beforeTags false).tree beforeTags target (index first) exprTag nextTag offset len second allocator.1
    firstOwned positive exprUnheld registeredTags different frameOwned targetMiddle exprMiddle targetMiddlePresent exprMiddlePresent exprMiddleTag firstAttach
  exact ⟨nextIndex,one.1,one.2.1,answer⟩
end DuplicatePrefix.GeneralBorrowFreshSharedPop
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshSharedPop." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved shared pop dependency {dependency}"
