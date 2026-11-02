import duplicate_prefix.GeneralBorrowForestMixedSharedEntryValidity
import duplicate_prefix.LenArgumentCopy
namespace DuplicatePrefix.GeneralBorrowForestMixedSharedArgumentCopy
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def copiedFrame (frame : CompilerFrameContext.ActualFrame) (localId : MIR.LocalId)
    (value : Immediate Provenance) (valid : localId < frame.locals.size) :=
  {frame with locals := (frame.locals.set localId
    {value := .live (.immediate value),layout := frame.locals[localId].layout} valid)}

def finalTree (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (parentTag : BorTag) (offset len : UInt64) :=
  let registered := TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag
  let read := tree.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read registered.protectedTags .VisitChildrenOfAccessed
  (read.tree.newChild (Size.ofBytes offset) (.concrete parentTag) tracker.global.nextPointerTag
    (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes len) NestedConstruction.frozenRead) (.Frozen) true).tree

/-- The exact memory tree installed by shared argument copy retains mixed
labels and forest context. These are derived from pre-copy ownership and real
Strong registration, independently of physical caller metadata. -/
theorem final_owned
    (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (borrowFrame : FrameState) (id : AllocId)
    (parentTag : BorTag) (parent primary : UniIndex) (extras : List UniIndex) (offset len : UInt64)
    (context : GeneralBorrowForestAccessData.Context tree parent primary extras)
    (covered : GeneralBorrowGraph.RootsCover tree)
    (tagPresent : tree.indexOfTag parentTag = some parent)
    (tagFresh : GeneralBorrowTagMap.Fresh tree.tagMapping tracker.global.nextPointerTag)
    (nodeTags : ∀ index node, tree.nodeAt index = some node → tree.indexOfTag node.tag = some index)
    (unheld : tracker.global.protectedTags.get tracker.global.nextPointerTag = none)
    (slot : GeneralBorrowFreshReborrowStages.Slot tree context.depth parent)
    (fits : tree.nodes.data.size ≤ 4294967296) (writable : Nat → Bool) (nonzero : len ≠ 0)
    (well : tree.locations.WellFormed) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (owned : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (GeneralBorrowForestMixedAccess.Data tree location tracker.global.protectedTags parent primary extras writable))
      offset (offset+len) tree.locations) :
    Nonempty (GeneralBorrowForestAccessData.Context (finalTree tree tracker parentTag offset len)
      (GeneralBorrowFreshMetadataChildSlot.index slot) primary extras) ∧
    GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (GeneralBorrowForestMixedAccess.Data (finalTree tree tracker parentTag offset len) location
        (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags
        (GeneralBorrowFreshMetadataChildSlot.index slot) primary extras
        (GeneralBorrowFreshMixedChild.extend writable (GeneralBorrowFreshMetadataChildSlot.index slot).toNat)))
      offset (offset+len) (finalTree tree tracker parentTag offset len).locations := by
  have registration := GeneralBorrowForestMixedRegister.registered tree tracker.global borrowFrame id
    tracker.global.nextPointerTag .StrongProtector parent primary extras writable tagFresh nodeTags unheld offset (offset+len) owned
  have result := GeneralBorrowForestMixedShared.run tree
    (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags
    parentTag tracker.global.nextPointerTag true parent primary extras offset len .VisitChildrenOfAccessed
    context covered tagPresent tagFresh slot fits writable nonzero well bounds registration.2.2.2
  simpa only [finalTree,GeneralBorrowForestMixedShared.child,GeneralBorrowForestMixedShared.read,
    GeneralBorrowFreshAnchor.sharedState,NestedConstruction.frozenRead] using result.2.2

/-- Actual shared MIR argument copy with real protected FnEntry runtime validation on
a general multiple-root forest. Every borrow success is derived from the
initial stable mutable Data; physical/compiler/fuel premises stay explicit. -/
theorem copy_argument
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (parentTag : BorTag)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .FnEntry)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (parent primary : UniIndex) (extras : List UniIndex)
    (context : GeneralBorrowForestAccessData.Context entry.allocation.extra parent primary extras)
    (covered : GeneralBorrowGraph.RootsCover entry.allocation.extra)
    (tagPresent : entry.allocation.extra.indexOfTag parentTag = some parent)
    (tagFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping tracker.global.nextPointerTag)
    (nodeTags : ∀ index node, entry.allocation.extra.nodeAt index = some node → entry.allocation.extra.indexOfTag node.tag = some index)
    (unheld : tracker.global.protectedTags.get tracker.global.nextPointerTag = none)
    (slot : GeneralBorrowFreshReborrowStages.Slot entry.allocation.extra context.depth parent)
    (fits : entry.allocation.extra.nodes.data.size ≤ 4294967296)
    (writable : Nat → Bool) (well : entry.allocation.extra.locations.WellFormed)
    (owned : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (GeneralBorrowForestMixedAccess.Data entry.allocation.extra location tracker.global.protectedTags parent primary extras writable))
      offset (offset+len) entry.allocation.extra.locations)
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (localId : MIR.LocalId) (valid : localId < frame.locals.size)
    (old : Immediate Provenance)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some SharedReferenceMetadata.sharedLayout)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false)
    (view : RuntimeStackPlace Provenance)
    (destination : view.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size frame localId SharedReferenceMetadata.sharedLayout) :
    let cfg := config options remaining span
    let value := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm
    let copied := copiedFrame frame localId value valid
    let finalTree := GeneralBorrowForestMixedSharedArgumentCopy.finalTree entry.allocation.extra tracker parentTag offset len
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine machine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory machine.memory id entry finalTree}
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
      ⟨.immediate value,SharedReferenceMetadata.sharedLayout⟩ view (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames
        {(TypedBorrowSteps.registeredFrame copied borrowFrame id tracker.global.nextPointerTag) with
          locals := copied.locals.set localId
            {value := .live (.immediate (RetagReferencePlace.sliceValue cfg.access.runtime.base
              (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm),
             layout := (copied.locals[localId]'(by simpa only [copied,copiedFrame,Array.size_set] using valid)).layout}
            (by simpa only [copied,copiedFrame,Array.size_set] using valid)} resultMachine) := by
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm
  let copied := copiedFrame frame localId value valid
  have postValid : localId < copied.locals.size := by simpa only [copied,copiedFrame,Array.size_set] using valid
  have postLive : copied.locals[localId].value = .live (.immediate value) := by simp [copied,copiedFrame]
  have postCached : copied.locals[localId].layout = some SharedReferenceMetadata.sharedLayout := by
    simpa only [copied,copiedFrame,Array.getElem_set_self] using cached
  have checked := (GeneralBorrowForestMixedSharedEntryValidity.positive options remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq
    id entry base offset len parentTag positive nonzero signedFits bounds frames copied machine
    tracker enabled mode borrowFrame frameBorrow fresh parent primary extras context covered tagPresent tagFresh nodeTags unheld slot fits writable well owned capacity localId postValid postLive postCached ghost shallow
    cachedAddress present race metadata notConstructed).1
  apply LenArgumentCopy.copy_with_nested_validation options limits remaining span debugOff frames frame machine
    localId old value valid live cached noClocks ghost shallow view destination _
  rw [validationEq]
  exact checked

#print axioms copy_argument
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``copy_argument) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved asmut argument dependency {dependency}"
end
end DuplicatePrefix.GeneralBorrowForestMixedSharedArgumentCopy
