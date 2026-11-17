import duplicate_prefix.ActualRetagContext

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
namespace DuplicatePrefix.ReturnProtection
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures Miri.TreeBorrows
open Miri.Input Miri.Interpreter
open CanonicalConfigFacts ActualReferenceContext TypedBorrowSteps ReferenceBorrowDriver

noncomputable def borrowedState
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (tracker : MachineHooks.BorrowState)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (tree : BorrowTree) : RootState :=
  Storage.withCurrent frames (registeredFrame frame borrowFrame id tracker.global.nextPointerTag)
    {registeredMachine (allocatedMachine machine tracker fresh) (allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory machine.memory id entry tree}

/-- Internal composition of exact tree certificates with the real return-slot
retag. The return-pointer's source mode is preserved, including Default mode. -/
theorem retag_bool_from_tree
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualRetagContext.Context options remaining span) (budget : Nat)
    (place : MPlaceTy Provenance) (layout : place.layout = RootCompilerFacts.boolLayout)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker)
    (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base : UInt64) (rootTag : BorTag)
    (pointer : place.mplace.ptr = Pointer.new (some (.concrete id rootTag)) (Size.ofBytes base))
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩)
    (bounds : 1 ≤ entry.allocation.byteSize.bytes.toNat)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (race : machine.dataRace = none) (parentTree finalTree : BorrowTree)
    (readTree : (entry.allocation.extra.performBorrowAccessRange (.concrete rootTag) Size.ZERO
      (Size.ofBytes 1) .Read (registeredGlobal (allocatedTracker tracker fresh) tracker.global.nextPointerTag).protectedTags
      .VisitChildrenOfAccessed).tree = parentTree)
    (readDone : (entry.allocation.extra.performBorrowAccessRange (.concrete rootTag) Size.ZERO
      (Size.ofBytes 1) .Read (registeredGlobal (allocatedTracker tracker fresh) tracker.global.nextPointerTag).protectedTags
      .VisitChildrenOfAccessed).status = .Completed)
    (child : parentTree.newChild Size.ZERO (.concrete rootTag) tracker.global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes 1) ChildBorrow.fnEntryLocation)
      MachineHooks.protectionPolicy.outsidePermission MachineHooks.protectionPolicy.protector.isSome =
      ⟨finalTree, .ok ()⟩) :
    TypedRetag.retagPlace (config options remaining span).retag budget place MachineHooks.protectionPolicy
      (Storage.withCurrent frames frame machine) =
      .ok (TypedRetagGeneric.retaggedPlace place id tracker.global.nextPointerTag)
        (borrowedState frames frame borrowFrame machine tracker fresh id entry finalTree) := by
  have frozen : (config options remaining span).retag.typeIsFreeze place.layout.ty = pure true := by
    rw [layout]
    exact ActualRetagContext.bool_freeze options remaining span ctx
  have allocated : (allocatedMachine machine tracker fresh).borrowTracker = some (allocatedTracker tracker fresh) := rfl
  have reborrow := protected_read_from_fields (config options remaining span).retag ReferenceMetadataFacts.prepared
    (config options remaining span).access (config options remaining span).projection ctx.table ctx.pointers ctx.choice ctx.source
    budget place frames frame borrowFrame (allocatedMachine machine tracker fresh) (allocatedTracker tracker fresh)
    allocated frameBorrow id entry base 0 1 rootTag tracker.global.nextPointerTag ChildBorrow.fnEntryLocation
    MachineHooks.protectionPolicy rfl rfl (by decide) frozen rfl
    (by simpa only [UInt64.add_zero] using pointer) ctx.resolve ctx.arithmetic cached (by decide)
    (by simpa using bounds) .global ctx.globals ctx.ensure ctx.synchronize present race parentTree finalTree readTree readDone child
  have provenance : place.mplace.ptr.provenance = some (.concrete id rootTag) := by rw [pointer]; rfl
  have result := retag_place_of_reborrow (config options remaining span).retag budget place
    MachineHooks.protectionPolicy (Size.ofBytes 1) Align.ONE (Storage.withCurrent frames frame machine)
    (borrowedState frames frame borrowFrame machine tracker fresh id entry finalTree) tracker enabled fresh id
    (.concrete id rootTag) provenance (ActualRetagContext.bool_size options remaining span ctx place layout) reborrow
  exact result


theorem slot_tree (root child : BorTag) : TypedRetagGeneric.childTree root child 1 0 1 =
    BorrowRangeAccess.canonicalChildTree root child
      (DedupRangeMap.new (Size.ofBytes 1) (BorrowRangeAccess.childLocation false)) := by
  with_unfolding_all rfl

/-- The concrete fresh one-byte return allocation derives both tree steps from
its root shape and the protected-tag map; no tree operation success is assumed. -/
theorem retag_bool_root
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualRetagContext.Context options remaining span) (budget : Nat)
    (place : MPlaceTy Provenance) (layout : place.layout = RootCompilerFacts.boolLayout)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker)
    (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base : UInt64) (rootTag : BorTag)
    (pointer : place.mplace.ptr = Pointer.new (some (.concrete id rootTag)) (Size.ofBytes base))
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩)
    (root : entry.allocation.extra = BorrowTree.new rootTag (Size.ofBytes 1))
    (size : entry.allocation.byteSize = Size.ofBytes 1)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (race : machine.dataRace = none)
    (distinct : rootTag ≠ tracker.global.nextPointerTag)
    (unprotected : tracker.global.protectedTags.contains rootTag = false) :
    TypedRetag.retagPlace (config options remaining span).retag budget place MachineHooks.protectionPolicy
      (Storage.withCurrent frames frame machine) =
      .ok (TypedRetagGeneric.retaggedPlace place id tracker.global.nextPointerTag)
        (borrowedState frames frame borrowFrame machine tracker fresh id entry
          (BorrowRangeAccess.canonicalChildTree rootTag tracker.global.nextPointerTag
            (DedupRangeMap.new (Size.ofBytes 1) (BorrowRangeAccess.childLocation false)))) := by
  have protectedRoot : (registeredGlobal (allocatedTracker tracker fresh) tracker.global.nextPointerTag).protectedTags.contains rootTag = false := by
    change (tracker.global.protectedTags.insert tracker.global.nextPointerTag .StrongProtector).contains rootTag = false
    simp only [ProtectedTags.contains]
    rw [ProtectedTagsFacts.insert_preserves_other tracker.global.protectedTags rootTag tracker.global.nextPointerTag .StrongProtector distinct]
    exact unprotected
  have read := ParentBorrowAccess.parent_range_result rootTag 1 0 1 .Read
    (registeredGlobal (allocatedTracker tracker fresh) tracker.global.nextPointerTag).protectedTags protectedRoot
    (by decide) (by decide)
  have child := ChildConstructor.new_child_partition_exact rootTag tracker.global.nextPointerTag distinct 1 0 1
    (by decide) (by decide)
  change _ = (⟨TypedRetagGeneric.childTree rootTag tracker.global.nextPointerTag 1 0 1, .ok ()⟩ : BorrowTree.ChildInsertResult) at child
  rw [slot_tree] at child
  apply retag_bool_from_tree options remaining span ctx budget place layout frames frame borrowFrame machine tracker
    enabled frameBorrow fresh id entry base rootTag pointer cached _ present race _ _ _ _ child
  · rw [size]; decide
  · rw [root]; exact read.1
  · rw [root]; exact read.2


/-- Internal composition with the physical uninitializing write. The source
writes through the new protected child and then discards that pointer. -/
theorem protect_bool_from_write
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualRetagContext.Context options remaining span) (budget : Nat)
    (place : MPlaceTy Provenance) (layout : place.layout = RootCompilerFacts.boolLayout)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker)
    (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base : UInt64) (rootTag : BorTag)
    (pointer : place.mplace.ptr = Pointer.new (some (.concrete id rootTag)) (Size.ofBytes base))
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩)
    (root : entry.allocation.extra = BorrowTree.new rootTag (Size.ofBytes 1))
    (size : entry.allocation.byteSize = Size.ofBytes 1)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (race : machine.dataRace = none)
    (distinct : rootTag ≠ tracker.global.nextPointerTag)
    (unprotected : tracker.global.protectedTags.contains rootTag = false)
    (after : RootState)
    (write : (config options remaining span).retag.writeUninit
      (TypedRetagGeneric.retaggedPlace place id tracker.global.nextPointerTag)
      (borrowedState frames frame borrowFrame machine tracker fresh id entry
        (BorrowRangeAccess.canonicalChildTree rootTag tracker.global.nextPointerTag
          (DedupRangeMap.new (Size.ofBytes 1) (BorrowRangeAccess.childLocation false)))) = .ok () after) :
    TypedRetag.protectInPlaceFunctionArgument (config options remaining span).retag budget place
      (Storage.withCurrent frames frame machine) = .ok () after := by
  have retag := retag_bool_root options remaining span ctx budget place layout frames frame borrowFrame machine tracker enabled
    frameBorrow fresh id entry base rootTag pointer cached root size present race distinct unprotected
  unfold TypedRetag.protectInPlaceFunctionArgument TypedRetag.protectPlace
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, Storage.withCurrent,
    enabled, Option.isSome_some, ↓reduceIte]
  erw [retag]
  exact write


theorem actual_call_protection (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (place : MPlaceTy Provenance) :
    (ExecutionMachine.callHooks (config options remaining span) limits).protectArgument () place =
      TypedRetag.protectInPlaceFunctionArgument (config options remaining span).retag limits.retag place := by
  rfl

end DuplicatePrefix.ReturnProtection
open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.ReturnProtection.retag_bool_from_tree,
      ``DuplicatePrefix.ReturnProtection.retag_bool_root,
      ``DuplicatePrefix.ReturnProtection.protect_bool_from_write,
      ``DuplicatePrefix.ReturnProtection.actual_call_protection] do
   for dependency in (← collectAxioms declaration) do
     unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
       throwError "unapproved return protection dependency {dependency}"
