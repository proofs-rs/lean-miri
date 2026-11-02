import duplicate_prefix.GenericSharedAcceptedForm
import duplicate_prefix.GenericSharedLenAcceptedStrong
import duplicate_prefix.GeneralBorrowFreshSharedTwoFuture
import duplicate_prefix.GenericFunctionEntryNumerics
namespace DuplicatePrefix.GenericSharedAcceptedRuntime
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralRangeMapOrigins GeneralRangeMapState GenericSharedAcceptedStages
set_option maxRecDepth 65536
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
attribute [local irreducible] GeneralBorrowFreshSharedSequence.child

private theorem fresh_after (tree after : BorrowTree) (protections : ProtectedTags) (child queryTag : BorTag) (query : UniIndex)
    (facts : GeneralBorrowFreshSharedTwoFuture.ReleasedFresh tree protections child query queryTag)
    (frame : (tree.releaseProtector child protections).tree = after) :
    GeneralBorrowFreshFutureClean.Clean after query ∧ GeneralBorrowTagMap.Fresh after.tagMapping queryTag ∧
      GeneralBorrowProtector.Fresh after queryTag := by
  have clean := facts.clean
  have mapping := facts.mapFresh
  have nodes := facts.nodeFresh
  rw [frame] at clean mapping nodes
  exact ⟨clean,mapping,nodes⟩

private theorem staged (s : GenericSharedAcceptedInput.Input) :
    Nonempty (GeneralBorrowFreshSharedReleasedMetadata.Output s.entry.allocation.extra (child s) s.target s.first.parentNode s.first.parentTag) := by
  exact GeneralBorrowFreshSharedReleasedMetadata.stages s.entry.allocation.extra s.tracker.global.protectedTags
    s.target s.tracker.global.nextPointerTag (one s).global.nextPointerTag s.offset s.len s.first s.noFree s.room
    s.tagFresh s.protectorFresh s.different s.cleanFuture s.owned

private theorem metadata_release (s : GenericSharedAcceptedInput.Input) (released : BorrowTree)
    (frame : released = {child s with locations := released.locations}) :
    Nonempty (GeneralBorrowFreshSharedReleasedMetadata.Output s.entry.allocation.extra released s.target s.first.parentNode s.first.parentTag) := by
  obtain ⟨metadata⟩ := staged s
  exact GeneralBorrowFreshSharedReleasedMetadata.of_frame s.entry.allocation.extra (child s) released
    s.target s.first.parentNode s.first.parentTag metadata frame

/-- Execute the real shared expression and len call/release/guard, then form
all data needed by the mutable/copy/physical-return suffix from one initial
PC2:11 contract. No post-state, successful operation or future Data is an input. -/
theorem prepare (s : GenericSharedAcceptedInput.Input) :
    ∃ ready : GenericAsMutDefaultToCall.Input,
      PreparedContracts.actualConfig ready.base.data.start.options () (ready.base.data.start.remaining+1) ready.base.data.start.span =
        PreparedContracts.actualConfig s.options () (s.remaining+1) s.span ∧ ready.base.data.start.limits = s.limits ∧
      SuccessfulTrace.Trace (PreparedContracts.actualConfig s.options () (s.remaining+1) s.span) s.limits
        (Storage.withCurrent #[] s.frame s.machine)
        (Storage.withCurrent #[] ready.base.caller ready.base.data.start.machine) := by
  obtain ⟨frame,machine,tree,tracker,previous,runtime,track,active,well,capacity,treeFrame,releaseFacts,frameFacts,memory⟩ :=
    GenericSharedLenAcceptedStrong.executes_full
    s.options s.limits s.remaining s.budget s.dispatchFuel s.span s.precise s.implicitWrites s.debug
    s.cmp s.dynamicFuel s.validityFuel s.dynamicEq s.validationEq s.id s.entry s.base s.offset
    s.len s.positive s.nonnull s.signedFits s.frame s.machine s.tracker s.enabled s.defaultMode
    s.fresh s.target s.first s.capacity s.owned s.noFree s.room s.fresh2 s.tagFresh
    s.protectorFresh s.different s.cleanFuture s.v1 s.v11 s.v12 s.sourceLive s.sourceCached s.lenLive
    s.lenUncached s.exprLive s.exprUncached s.body s.identity s.callee s.location s.frameRace s.race
    s.ghost s.shallow s.cached s.present s.metadata s.notConstructed s.backend s.thread s.active
    s.threadCache s.unchecked s.noGc s.fixed s.source s.rangePositive s.exprUnheld s.size s.count
    s.countPositive s.within s.all s.live0 s.cache0 s.live7 s.cache7 s.live8 s.cache8
    s.live9 s.cache9 s.live10 s.cache10 s.live13 s.cache13 s.dead15 s.cache15 s.dead16
    s.cache16 s.initialActive
  rcases previous with ⟨prefixTrace,location,tracked,present,body,identity,callee,extra,size,slot1,slot2,slot15,slot16,immediate,owned⟩
  have endedEq : tracker = ended_base s.toBase := releaseFacts.2
  let boundary : GenericSharedAcceptedForm.Boundary s frame machine tree := {
    location := location, tracked := by rw [←endedEq];exact tracked
    present := present, body := body, identity := identity, callee := callee, extra := extra, size := size
    slot1 := slot1, slot2 := slot2, slot15 := slot15, slot16 := slot16, immediate := immediate
    owned := by rw [←endedEq];exact owned
    runtime := runtime, track := track, active := active, well := well, capacity := capacity, facts := frameFacts, memory := memory }
  have structuralFrame : tree = {child s with locations := tree.locations} := by
    dsimp only [child,second,one]
    exact treeFrame
  obtain ⟨metadata⟩ := metadata_release s tree structuralFrame
  let query3 : UniIndex := ⟨UInt32.ofNat (s.entry.allocation.extra.tagMapping.mapping.size+2)⟩
  let query4 : UniIndex := ⟨UInt32.ofNat (s.entry.allocation.extra.tagMapping.mapping.size+3)⟩
  have bound3 : s.entry.allocation.extra.tagMapping.mapping.size+2 < 4294967296 := by have room:=s.roomFour;omega
  have bound4 : s.entry.allocation.extra.tagMapping.mapping.size+3 < 4294967296 := by have room:=s.roomFour;omega
  have at3 : s.entry.allocation.extra.tagMapping.mapping.size+2 ≤ query3.toNat := by
    simp only [query3,UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt bound3,Nat.le_refl]
  have at4 : s.entry.allocation.extra.tagMapping.mapping.size+2 ≤ query4.toNat := by
    simp only [query4,UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt bound4]
    omega
  have different := GenericFunctionEntryNumerics.four_tags_distinct s.tracker s.fresh s.fresh2 s.fresh3
  have future3 := GeneralBorrowFreshSharedTwoFuture.release s.entry.allocation.extra s.tracker.global.protectedTags s.target
    s.tracker.global.nextPointerTag (one s).global.nextPointerTag s.offset s.len s.first s.noFree s.room
    s.tagFresh s.protectorFresh s.different s.cleanFuture s.owned query3 at3 s.clean3
    (two s).global.nextPointerTag s.mapFresh3 s.nodeFresh3 different.2.1 s.different23 s.rangePositive
  have future4 := GeneralBorrowFreshSharedTwoFuture.release s.entry.allocation.extra s.tracker.global.protectedTags s.target
    s.tracker.global.nextPointerTag (one s).global.nextPointerTag s.offset s.len s.first s.noFree s.room
    s.tagFresh s.protectorFresh s.different s.cleanFuture s.owned query4 at4 s.clean4
    (three s).global.nextPointerTag s.mapFresh4 s.nodeFresh4 different.2.2.1 s.different24 s.rangePositive
  have actualRelease : (child s).releaseProtector (one s).global.nextPointerTag (held s).global.protectedTags = ⟨tree,.Released⟩ := releaseFacts.1
  have releaseFrame : ((child s).releaseProtector (one s).global.nextPointerTag (held s).global.protectedTags).tree = tree :=
    congrArg BorrowTree.ProtectorReleaseResult.tree actualRelease
  have next3 := fresh_after (child s) tree (held s).global.protectedTags (one s).global.nextPointerTag (two s).global.nextPointerTag query3 future3 releaseFrame
  have next4 := fresh_after (child s) tree (held s).global.protectedTags (one s).global.nextPointerTag (three s).global.nextPointerTag query4 future4 releaseFrame
  obtain ⟨ready,frameEq,machineEq,configEq,limitsEq⟩ := GenericSharedAcceptedForm.form s frame machine tree boundary metadata
    next3.2.1 next3.2.2 next3.1 next4.2.1 next4.2.2 next4.1
  rw [←frameEq,←machineEq] at prefixTrace
  exact ⟨ready,configEq,limitsEq,prefixTrace⟩
end DuplicatePrefix.GenericSharedAcceptedRuntime
