import duplicate_prefix.CurrentCallPostEntryCheckpoint
import duplicate_prefix.CurrentCallSpatialEntryControl
import duplicate_prefix.PositiveRootInstalledFrame
import duplicate_prefix.PushThread

/-! Assemble the common checkpoint from actual current entry resources and
the canonical installed root frame. Original call execution is separate prefix
evidence supplied by the entry producer. -/
namespace DuplicatePrefix.CurrentCallInstalledCheckpoint
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization CurrentCallPostEntryCheckpoint
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

private theorem present_of_live (machine : Before) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (live : machine.memory.live.find? (fun row => row.1 == id) = some (id, entry)) :
    Present (ActualWorld machine) id entry.allocation := by
  simp only [Present, ActualWorld, Array.toList_map]
  exact List.mem_map.mpr ⟨(id, entry), Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live), rfl⟩

def assemble {options remaining span machine tracker offset len count place}
    (tracked : machine.borrowTracker = some tracker) (mode : tracker.retagMode = .Default)
    (model : DuplicatePrefixCallModel.Model options remaining span machine)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins machine.user.payload.payload.user.types)
    (source : Source machine tracker offset len) (copyReady : CopyReady source)
    (output : Return machine tracker place)
    (differentTags : source.tag ≠ output.node.tag)
    (absent : output.id ≠ source.role.backing.id → ∀ index node,
      output.window.allocation.extra.nodes.get index = some node → node.tag ≠ source.tag)
    (separate : output.id = source.role.backing.id → ∀ byte,
      Window source.role.backing.id offset len.toNat byte → Window output.id output.offset 1 byte → False)
    (ids : (machine.memory.live.toList.map Prod.fst).Nodup)
    (tags : tracker.global.nextPointerTag.value.toNat + 6 < 18446744073709551615)
    (initial : Before) (race : initial.dataRace = none)
    (stackReady : CurrentCallPush.StackReadiness initial #[])
    (threads : machine.threads = (CurrentCallPush.preparedMachine initial #[]).threads)
    (validationFuel dynamicFuel : Nat)
    (validationEq : options.limits.validation = validationFuel + 1)
    (dynamicEq : options.place.dynamicFuel = dynamicFuel + 1) :
    Checkpoint options remaining span len count place := by
  classical
  let root := CurrentCallSpatialEntryControl.root initial #[] place race
  let adjusted := (CurrentCallTypedSourceCopy.value options remaining span source.role.family.value len).imm
  let installed := PositiveRootInstalledFrame.installed root adjusted count {} source.role.backing.id source.tag output.id output.node.tag
  let entry := Classical.choose source.binding
  have live : machine.memory.live.find? (fun row => row.1 == source.role.backing.id) =
      some (source.role.backing.id, entry) := by
    obtain ⟨base, hit, _⟩ := Classical.choose_spec source.binding
    exact hit
  have allocation : entry.allocation = source.role.backing.allocation := by
    apply CandidateCurrentUniformOwnerWindow.same_id (ActualWorld machine).toList
      (by simpa only [ActualWorld, Array.toList_map, List.map_map, Function.comp_def] using ids)
      source.role.backing.id entry.allocation source.role.backing.allocation
      (present_of_live machine _ entry live) source.role.backing.live
  have raw : root.frame.locals = Array.replicate 25 (⟨.dead, none⟩ : LocalState Provenance LocalLayout) :=
    RootEntryFrame.raw_locals _ _ _
  have metadata := PositiveRootInstalledFrame.metadata root adjusted count {} source.role.backing.id source.tag output.id output.node.tag
  let oldThread := Classical.choose stackReady
  have oldActive : initial.threads.activeThread? = some oldThread := (Classical.choose_spec stackReady).1
  let thread := {oldThread with topUserRelevantFrame := some 0}
  have active : machine.threads.activeThread? = some thread := by
    rw [threads]
    exact PushThread.cache_top_active (CallEntryFacts.freshRoot initial).1 oldThread 0 oldActive
  let borrowFrame := (({} : FrameState).addProtector source.role.backing.id source.tag).addProtector output.id output.node.tag
  exact {
    machine := machine, tracker := tracker, tracked := tracked, mode := mode, model := model, origins := origins,
    offset := offset, source := source, sourceEntry := entry, sourceLive := live, sourceAllocation := allocation,
    copyReady := copyReady, output := output, sourceBoolTags := differentTags, sourceTagAbsentBool := absent,
    separate := separate, ids := ids, tags := tags, frame := installed,
    body := metadata.1.trans root.body, identity := metadata.2.1.trans root.identity,
    callee := metadata.2.2.1.trans root.callee, location := metadata.2.2.2.2.2.2.2.2,
    size := PositiveRootInstalledFrame.size _ _ _ _ _ _ _ _,
    sourceLocal := by simpa [installed, adjusted] using
      PositiveRootInstalledFrame.slot_option root raw adjusted count {} source.role.backing.id source.tag output.id output.node.tag ⟨1, by decide⟩,
    countLocal := by simpa [installed] using
      PositiveRootInstalledFrame.slot_option root raw adjusted count {} source.role.backing.id source.tag output.id output.node.tag ⟨2, by decide⟩,
    slots := PositiveRootInstalledFrame.slot_option root raw adjusted count {} source.role.backing.id source.tag output.id output.node.tag,
    immediate := PositiveRootInstalledFrame.immediate _ raw _ _ _ _ _ _ _,
    noClocks := metadata.2.2.2.2.2.2.1.trans root.noClocks,
    track := by rw [PositiveRootInstalledFrame.track]; rfl,
    relevance := by rw [PositiveRootInstalledFrame.relevance]; rfl,
    destination := by rw [metadata.2.2.2.2.1]; rfl,
    stop := metadata.2.2.2.1.trans (by rfl), varargs := metadata.2.2.2.2.2.1.trans (by rfl),
    borrowFrame := borrowFrame, frameTracked := metadata.2.2.2.2.2.2.2.1, protectors := rfl,
    thread := thread, active := active, top := rfl, validationFuel := validationFuel, validationEq := validationEq,
    dynamicFuel := dynamicFuel, dynamicEq := dynamicEq }

end
end DuplicatePrefix.CurrentCallInstalledCheckpoint

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "CurrentCallInstalledCheckpoint.").length != 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved installed checkpoint dependency {name}: {dependency}"
