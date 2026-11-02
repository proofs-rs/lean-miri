import duplicate_prefix.S03FinalReturnInputBounds
import duplicate_prefix.S03EmptyTagState

namespace DuplicatePrefix.S03SeparateLiveInstalledPacket
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open CanonicalConfigFacts ActualReferenceContext DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
noncomputable section

/-- Current output of actual live empty initialization, consumed by the body
and original Return. Every field is produced from the initial contract. -/
structure Packet (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (place : MPlaceTy Provenance) (address count : UInt64) where
  tracker : MachineHooks.BorrowState
  borrowFrame : FrameState
  destination : S03FinalReturnInputBounds.Destination machine place
  argumentId : AllocId
  argumentEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind
  argumentBase : UInt64
  argumentLive : machine.memory.live.find? (fun row => row.1 == argumentId) = some (argumentId,argumentEntry)
  argumentCached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == argumentId) = some ⟨argumentId,argumentBase⟩
  separate : destination.id ≠ argumentId
  argumentRuntime : DuplicatePrefixBorrowContract.RuntimeFacts argumentEntry.allocation.extra tracker.global
  argumentRoom : argumentEntry.allocation.extra.nodes.size+2 ≤ 4294967295
  zeroTag : BorTag
  zeroIndex : UniIndex
  zero : S03EmptyTagState.Data argumentEntry.allocation.extra zeroTag zeroIndex
  quiet : S04ReturnReleaseInactive.Quiescent argumentEntry.allocation.extra zeroIndex
  returnTag : BorTag
  child : UniIndex
  selected : UniIndex
  maximum : Option BorTag
  returnNode : TreeNode
  defaultMode : tracker.retagMode = .Default
  enabled : machine.borrowTracker = some tracker
  frameTracked : frame.extra.borrowTracker = some borrowFrame
  owned : borrowFrame.protectedTags = #[(argumentId,zeroTag),(destination.id,returnTag)]
  returnTagged : destination.entry.allocation.extra.indexOfTag returnTag = some child
  returnPresent : destination.entry.allocation.extra.nodeAt child = some returnNode
  returnSame : returnNode.tag = returnTag
  returnEdge : returnNode.parent = some destination.parent
  returnHidden : returnNode.isExposed = false
  hiddenFrame : S04ReturnReleaseParent.HiddenFrame destination.entry.allocation.extra borrowFrame
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts destination.entry.allocation.extra tracker.global
  positive : DuplicatePrefixBorrowAuthorization.Positive destination.entry.allocation.extra tracker.global.protectedTags
    (some child) (some selected) maximum destination.offset 1
  distinct : destination.entry.allocation.extra.roots.toList.Nodup
  order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder destination.entry.allocation.extra
  short : destination.entry.allocation.extra.nodes.size < 65536
  fresh : tracker.global.nextPointerTag.value < 18446744073709551615
  tagRoomNext : tracker.global.nextPointerTag.value.toNat+1 < 18446744073709551615
  activity : GeneralBorrowFreshActiveWithin.ActiveWithin destination.entry.allocation.extra child .Write
    destination.offset (destination.offset+1)
  thread : Miri.Concurrency.ThreadRecord
  active : machine.threads.activeThread? = some thread
  topZero : thread.topUserRelevantFrame = some 0
  race : machine.dataRace = none
  backend : machine.user.payload.payload.user.backend = .none
  ghost : machine.user.payload.ghost = false
  shallow : machine.user.payload.validation = .Shallow
  extras : machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == destination.id) =
    some (destination.id,⟨none,#[]⟩)
  metadata : machine.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime
  notConstructed : machine.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false
  sourceBody : frame.body = RootBody.reflected.body.body
  identity : frame.bodyIdentity = RootBody.reflected.body.identity
  callee : frame.functionInstance = RootBody.reflected.functionInstance
  location : frame.location = .mir ⟨0,0⟩
  frameSize : frame.locals.size = 25
  slots : ∀ i : Fin 25, (frame.locals[i.val]'(by rw [frameSize]; exact i.isLt)) =
    if 14 = i.val ∨ 13 = i.val ∨ 6 = i.val ∨ 0 = i.val then ⟨.live (.immediate .uninit),none⟩
    else if 2 = i.val then ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩
    else if 1 = i.val then ⟨.live (.immediate (RetagReferencePlace.sliceValue (ActualReferenceContext.config options remaining span).access.runtime.base
      (Pointer.new (.concrete argumentId zeroTag) (Size.ofBytes address)) 0 ActualReferenceMetadata.reference).imm),some ActualReferenceMetadata.reference⟩
    else ⟨.dead,none⟩
  noLocalClocks : frame.extra.dataRace = none
  returnPlace : frame.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩
  continuation : frame.returnContinuation = .stop true
  immediateLocals : CopyHelperCleanup.AllImmediate frame
  varargs : frame.vaList = #[]
  unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false
  noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0
  fixed : machine.threads.fixedScheduling = true

/-- The actual frame owns the zero argument and return protectors. -/
def Packet.argument {options : EvalConfigurationCore.Options} {remaining : Nat}
    {span : PreparedContracts.FixedSpanQuery} {frame : CompilerFrameContext.ActualFrame}
    {machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser}
    {place : MPlaceTy Provenance} {address count : UInt64}
    (packet : Packet options remaining span frame machine place address count) :
    S04FinalReturnVariantsInput.ArgumentProtection machine.memory packet.borrowFrame
      packet.destination.id packet.destination.entry packet.returnTag :=
  .separate packet.argumentId packet.argumentEntry packet.zeroTag packet.zeroIndex packet.zero.node
    packet.separate packet.argumentLive packet.owned packet.zero.tagged packet.zero.present packet.zero.hidden packet.quiet


end
end DuplicatePrefix.S03SeparateLiveInstalledPacket
