import duplicate_prefix.CurrentCallSpatialCover
import duplicate_prefix.CurrentCallResourceEntrySourceStorage
import duplicate_prefix.CurrentCallBoolScalarWrite

/-! Current resources at the installed root frame.  Initial call execution is
prefix evidence, rather than an index of these body resources.  In particular,
the source keeps its fixed spatial cover instead of choosing one completion
for the whole request. -/
namespace DuplicatePrefix.CurrentCallPostEntryCheckpoint
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures
open Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization CurrentCallSpatialCover
set_option autoImplicit false
noncomputable section

/-- The positive source at a body checkpoint.  Concrete pointer identity does
not force its fixed per-cell completion witnesses to coincide. -/
structure Source (machine : Before) (tracker : MachineHooks.BorrowState)
    (offset : Nat) (len : UInt64) where
  context : Context machine
  role : RoleCover machine tracker context .mut offset len.toNat
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global
  distinct : role.backing.allocation.extra.roots.toList.Nodup
  tag : BorTag
  concrete : role.family.value.provenance=.concrete role.backing.id tag
  grant : UniIndex
  node : TreeNode
  nodeAt : role.backing.allocation.extra.nodes.get grant=some node
  nodeTag : node.tag=tag
  hidden : node.isExposed=false
  activity : GeneralBorrowFreshActiveWithin.ActiveWithin role.backing.allocation.extra grant .Write
    (UInt64.ofNat offset) (UInt64.ofNat offset+len)
  binding : CandidateCallBindings.WindowBinding machine role.family.value role.backing.id offset len.toNat
  positive : 0<len.toNat
  signedFits : len.toNat<9223372036854775808
  nodes : role.backing.allocation.extra.nodes.size+6<65536

/-- Physical copy readiness is separate from the logical source cover.  The
existing direct provenance checks permit partial pointer fragments. -/
structure CopyReady {machine tracker offset len} (source : Source machine tracker offset len) : Prop where
  storage : CurrentCallResourceEntrySourceStorage.Data source.role.backing.allocation (UInt64.ofNat offset) len
  profile : CurrentCallBoolProtection.WindowReady machine source.role.backing.id offset len.toNat

/-- The uniform specialization is an adapter into the same source interface;
there is no converse assertion about ordinary callers. -/
def Source.ofUniform {machine tracker data owner id offset len}
    (window : UniformWindow machine tracker data owner id offset len.toNat .mut)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts window.allocation.extra tracker.global)
    (distinct : window.allocation.extra.roots.toList.Nodup)
    (tag : BorTag) (concrete : window.pointer.value.provenance=.concrete id tag)
    (node : TreeNode) (nodeAt : window.allocation.extra.nodes.get window.pointer.grant=some node)
    (nodeTag : node.tag=tag) (hidden : node.isExposed=false)
    (activity : GeneralBorrowFreshActiveWithin.ActiveWithin window.allocation.extra window.pointer.grant .Write
      (UInt64.ofNat offset) (UInt64.ofNat offset+len))
    (binding : CandidateCallBindings.WindowBinding machine window.pointer.value id offset len.toNat)
    (positive : 0<len.toNat) (signedFits : len.toNat<9223372036854775808)
    (nodes : window.allocation.extra.nodes.size+6<65536) : Source machine tracker offset len where
  context:=uniformContext window
  role:=CurrentCallSpatialCover.ofUniform window
  runtime:=runtime
  distinct:=distinct
  tag:=tag
  concrete:=concrete
  grant:=window.pointer.grant
  node:=node
  nodeAt:=nodeAt
  nodeTag:=nodeTag
  hidden:=hidden
  activity:=activity
  binding:=binding
  positive:=positive
  signedFits:=signedFits
  nodes:=nodes

/-- The temporary protected Bool child and the original destination are
different resources.  Only the child has current raw rights; the original
destination retains its binding and allocation license for release/reanchor. -/
structure Return (machine : Before) (tracker : MachineHooks.BorrowState)
    (place : MPlaceTy Provenance) where
  data : Identities
  owner : Nat
  id : AllocId
  offset : Nat
  window : UniformWindow machine tracker data owner id offset 1 .ret
  physical : CurrentCallBoolScalarWrite.Window machine place
  physicalId : physical.id=id
  physicalOffset : physical.offset.toNat=offset
  physicalAllocation : physical.entry.allocation=window.allocation
  binding : CandidateCallBindings.WindowBinding machine physical.pointer id offset 1
  original : PointerInstance
  originalId : original.allocation=id
  originalPointer : original.value=physical.pointer
  originalIssued : SpatialDelegation machine tracker id window.allocation window.precise.completion original.grant
  originalBinding : PointerBinds window.allocation original
  edge : window.precise.completion.parents[window.pointer.grant.toNat]?=some (some original.grant)
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts window.allocation.extra tracker.global
  distinct : window.allocation.extra.roots.toList.Nodup
  short : window.allocation.extra.nodes.size<65536
  node : TreeNode
  nodeAt : window.allocation.extra.nodes.get window.pointer.grant=some node
  leaf : node.children=#[]
  hidden : node.isExposed=false
  activity : GeneralBorrowFreshActiveWithin.ActiveWithin window.allocation.extra window.pointer.grant .Write
    physical.offset (physical.offset+1)
  profile : CurrentCallBoolProtection.WindowReady machine id offset 1

/-- Body inputs refer only to the actual installed state.  A representation
producer separately retains its original initStackFrame equation.  This
positive-source checkpoint is not a definition of OrdinaryInput. -/
structure Checkpoint (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (len count : UInt64) (place : MPlaceTy Provenance) where
  machine : Before
  tracker : MachineHooks.BorrowState
  tracked : machine.borrowTracker=some tracker
  mode : tracker.retagMode=.Default
  model : DuplicatePrefixCallModel.Model options remaining span machine
  origins : DuplicatePrefixTypeCacheOrigins.Origins machine.user.payload.payload.user.types
  offset : Nat
  source : Source machine tracker offset len
  sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind
  sourceLive : machine.memory.live.find? (fun row=>row.1==source.role.backing.id)=some (source.role.backing.id,sourceEntry)
  sourceAllocation : sourceEntry.allocation=source.role.backing.allocation
  copyReady : CopyReady source
  output : Return machine tracker place
  sourceBoolTags : source.tag≠output.node.tag
  sourceTagAbsentBool : output.id≠source.role.backing.id → ∀ index node,
    output.window.allocation.extra.nodes.get index=some node → node.tag≠source.tag
  separate : output.id=source.role.backing.id → ∀ byte,
    Window source.role.backing.id offset len.toNat byte → Window output.id output.offset 1 byte → False
  ids : (machine.memory.live.toList.map Prod.fst).Nodup
  tags : tracker.global.nextPointerTag.value.toNat+6<18446744073709551615
  frame : CompilerFrameContext.ActualFrame
  body : frame.body=RootBody.reflected.body.body
  identity : frame.bodyIdentity=RootBody.reflected.body.identity
  callee : frame.functionInstance=RootBody.reflected.functionInstance
  location : frame.location=.mir ⟨0,0⟩
  size : frame.locals.size=25
  sourceLocal : frame.locals[1]?=some ⟨.live (.immediate
    (CurrentCallTypedSourceCopy.value options remaining span source.role.family.value len).imm),
    some ActualReferenceMetadata.reference⟩
  countLocal : frame.locals[2]?=some ⟨.live (.immediate
    (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩
  slots : ∀ i : Fin 25, frame.locals[i.val]?=some (
    if 14=i.val ∨ 13=i.val ∨ 6=i.val ∨ 0=i.val then ⟨.live (.immediate .uninit),none⟩
    else if 2=i.val then ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩
    else if 1=i.val then ⟨.live (.immediate
      (CurrentCallTypedSourceCopy.value options remaining span source.role.family.value len).imm),some ActualReferenceMetadata.reference⟩
    else ⟨.dead,none⟩)
  immediate : CopyHelperCleanup.AllImmediate frame
  noClocks : frame.extra.dataRace=none
  track : frame.trackCallerArg=none
  relevance : frame.extra.userRelevance=255
  destination : frame.returnPlace.toRuntimePlace=⟨.memory place.mplace,place.layout⟩
  stop : frame.returnContinuation=.stop true
  varargs : frame.vaList=#[]
  borrowFrame : FrameState
  frameTracked : frame.extra.borrowTracker=some borrowFrame
  protectors : borrowFrame.protectedTags=#[(source.role.backing.id,source.tag),(output.id,output.node.tag)]
  thread : Miri.Concurrency.ThreadRecord
  active : machine.threads.activeThread?=some thread
  top : thread.topUserRelevantFrame=some 0
  validationFuel : Nat
  validationEq : options.limits.validation=validationFuel+1
  dynamicFuel : Nat
  dynamicEq : options.place.dynamicFuel=dynamicFuel+1

end
end DuplicatePrefix.CurrentCallPostEntryCheckpoint

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallPostEntryCheckpoint" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved post-entry checkpoint dependency {dependency}"
