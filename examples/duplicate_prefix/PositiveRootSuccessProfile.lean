import duplicate_prefix.RootReferenceBorrow
import duplicate_prefix.AddOutput
import duplicate_prefix.CopyHelperCleanup
namespace DuplicatePrefix.PositiveRootSuccessProfile
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency

structure FrameShape (before after : CompilerFrameContext.ActualFrame)
    (pointer destinationValue : Scalar Provenance) (count : UInt64) : Prop where
  body : after.body=before.body
  identity : after.bodyIdentity=before.bodyIdentity
  callee : after.functionInstance=before.functionInstance
  extra : after.extra=before.extra
  destination : after.returnPlace=before.returnPlace
  continuation : after.returnContinuation=before.returnContinuation
  varargs : after.vaList=before.vaList
  localsIdentity : after.localsIdentity=before.localsIdentity
  trackedCaller : after.trackCallerArg=before.trackCallerArg
  size : after.locals.size=25
  location : after.location=.mir ⟨8,4⟩
  slot0 : after.locals[0]?=before.locals[0]?
  slot1 : after.locals[1]?=before.locals[1]?
  slot2 : after.locals[2]?=before.locals[2]?
  slot13 : after.locals[13]?=some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩
  slot15 : after.locals[15]?=some ⟨.live (.immediate (.scalar pointer)),some CopyCompilerFacts.destPointerLayout⟩
  slot17 : after.locals[17]?=some ⟨.live (.immediate .uninit),none⟩
  slot18 : after.locals[18]?=some ⟨.live (.immediate .uninit),none⟩
  slot19 : after.locals[19]?=some ⟨.live (.immediate (.scalar pointer)),some CopyCompilerFacts.sourcePointerLayout⟩
  slot21 : after.locals[21]?=some ⟨.live (.immediate (.scalar destinationValue)),some CopyCompilerFacts.destPointerLayout⟩
  slot24 : after.locals[24]?=some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩
  immediate : CopyHelperCleanup.AllImmediate after

structure MachineShape (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before after : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (thread : ThreadRecord) (tags : Fin 6→BorTag)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (capacity offset len : UInt64) : Prop where
  tracked : after.borrowTracker=some tracker
  mask : ProtectedBorrowAccess.SixMask tags tracker.global.protectedTags false
  buffer : after.memory.live.find? (fun row=>row.1==id)=some (id,{entry with allocation:=(entry.allocation.setExtra
    (NestedBorrowAccess.nestedTree tags (BorrowRangeAccess.partitionWithInside capacity offset (offset+len) BorrowRangeAccess.rootLocation (NestedBorrowAccess.nestedLocation false))))})
  other : ∀other otherEntry,other≠id→before.memory.live.find? (fun row=>row.1==other)=some (other,otherEntry)→
    after.memory.live.find? (fun row=>row.1==other)=some (other,otherEntry)
  addresses : after.user.addresses=before.user.addresses
  types : after.user.payload.payload.user.types=before.user.payload.payload.user.types
  backend : after.user.payload.payload.user.backend=before.user.payload.payload.user.backend
  extras : after.user.payload.payload.user.runtime.extras=before.user.payload.payload.user.runtime.extras
  ghost : after.user.payload.ghost=false
  shallow : after.user.payload.validation=.Shallow
  race : after.dataRace=none
  fixed : after.threads.fixedScheduling=true
  unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl after.user).checkedArithmetic=false
  noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl after.user).gcInterval=0
  active : after.threads.activeThread?=some thread

end DuplicatePrefix.PositiveRootSuccessProfile
