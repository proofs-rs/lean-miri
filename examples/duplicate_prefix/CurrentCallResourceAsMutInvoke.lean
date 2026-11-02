import duplicate_prefix.CurrentCallResourceAsMutCall
import duplicate_prefix.CurrentCallResourceDefaultMutable

namespace DuplicatePrefix.CurrentCallResourceAsMutInvoke
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources CurrentCallResourceNormalization CurrentCallResourceEntryBody
open CanonicalConfigFacts
open GeneralBorrowExposedNonleafPrimaryPath GeneralRangeMapOrigins S05ConcreteProtectedChildCompletion
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- The actual Default-mut operation, not an initial success condition. -/
structure DefaultStage {before tracker data owner id offset length}
    (Q : UniformWindow before tracker data owner id offset length .mut)
    (tag : BorTag) (room : tracker.global.nextPointerTag.value<18446744073709551615) (start amount : UInt64) where
  readDone : (GeneralBorrowRawDefaultExpression.read Q.allocation.extra tracker.global.protectedTags tag start amount .VisitChildrenOfAccessed).status=.Completed
  childDone : (GeneralBorrowRawDefaultExpression.child Q.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed).outcome=.ok ()
  childIndex : UniIndex
  lookup : (GeneralBorrowRawDefaultExpression.child Q.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed).tree.indexOfTag tracker.global.nextPointerTag=some childIndex
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts (GeneralBorrowRawDefaultExpression.child Q.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed).tree (GeneralBorrowFnEntryRegistration.advanced tracker.global room)
  capacity : (GeneralBorrowRawDefaultExpression.child Q.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed).tree.locations.size=Q.allocation.extra.locations.size
  growth : (GeneralBorrowRawDefaultExpression.child Q.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed).tree.nodes.size≤Q.allocation.extra.nodes.size+1
  parents : ParentInterpretation (GeneralBorrowRawDefaultExpression.child Q.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed).tree (extend Q.precise.completion childIndex Q.pointer.grant)
  owned : OwnedOn (S05CompletedAncestryReadMutable.Authority
    (GeneralBorrowRawDefaultExpression.child Q.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed).tree
    (extend Q.precise.completion childIndex Q.pointer.grant) (GeneralBorrowFnEntryRegistration.advanced tracker.global room).protectedTags childIndex)
    start (start+amount) (GeneralBorrowRawDefaultExpression.child Q.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed).tree.locations
  leaf : LeafFrame (GeneralBorrowRawDefaultExpression.read Q.allocation.extra tracker.global.protectedTags tag start amount .VisitChildrenOfAccessed).tree
    (GeneralBorrowRawDefaultExpression.child Q.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed).tree childIndex Q.pointer.grant
  node : TreeNode
  nodeAt : (GeneralBorrowRawDefaultExpression.child Q.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed).tree.nodes.get childIndex=some node
  nodeTag : node.tag=tracker.global.nextPointerTag
  nodeHidden : node.isExposed=false
  nodeParent : node.parent=some Q.pointer.grant
  activity : GeneralBorrowFreshActiveWithin.ActiveWithin
    (GeneralBorrowRawDefaultExpression.child Q.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed).tree childIndex .Write start (start+amount)
  targetActivity : ∀ target,GeneralBorrowFreshActiveWithin.ActiveWithin Q.allocation.extra target .Write start (start+amount) →
    GeneralBorrowFreshActiveWithin.ActiveWithin (GeneralBorrowRawDefaultExpression.child Q.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed).tree target .Write start (start+amount)
  oldNodes : ∀ query node,Q.allocation.extra.nodes.get query=some node →∃ next,
    (GeneralBorrowRawDefaultExpression.child Q.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed).tree.nodes.get query=some next ∧
    next.tag=node.tag ∧next.parent=node.parent ∧next.isExposed=node.isExposed ∧next.defaultInitialPermission=node.defaultInitialPermission
  roots : (GeneralBorrowRawDefaultExpression.child Q.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed).tree.roots=Q.allocation.extra.roots
  unheld : (GeneralBorrowFnEntryRegistration.advanced tracker.global room).protectedTags.contains tracker.global.nextPointerTag=false

theorem default_prepare {before tracker data owner id offset length}
    (Q : UniformWindow before tracker data owner id offset length .mut)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts Q.allocation.extra tracker.global)
    (tag : BorTag) (concrete : Q.pointer.value.provenance=.concrete id tag)
    (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (distinct : Q.allocation.extra.roots.toList.Nodup) (short : Q.allocation.extra.nodes.size<65536)
    (nodeRoom : Q.allocation.extra.nodes.size+1≤4294967295)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
    (nonzero : amount≠0) (bounds : start.toNat+amount.toNat≤Q.allocation.extra.locations.size.bytes.toNat) :
    Nonempty (DefaultStage Q tag room start amount) := by
  obtain ⟨readDone,childDone,afterRuntime,capacity,growth,child,lookup,parents,owned,leaf,⟨node,nodeAt,nodeTag,nodeHidden⟩,order,activity,targetActivity,oldNodes⟩:=
    CurrentCallResourceDefaultMutable.prepare Q runtime tag concrete room distinct short nodeRoom start amount startEq amountEq nonzero bounds
  obtain ⟨actual,actualAt,edge⟩:=leaf.childLive
  have same : actual=node:=Option.some.inj (actualAt.symm.trans nodeAt)
  have nodeParent : node.parent=some Q.pointer.grant:=same ▸ edge
  have frame:=GeneralBorrowFreshReadFrame.frame Q.allocation.extra (.concrete tag) (Size.ofBytes start) (Size.ofBytes amount) .Read tracker.global.protectedTags .VisitChildrenOfAccessed
  have readRoots:=congrArg BorrowTree.roots frame
  have roots : (GeneralBorrowRawDefaultExpression.child Q.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed).tree.roots=Q.allocation.extra.roots:=leaf.roots.trans readRoots
  have high:=GeneralBorrowForestTagHighWater.complete Q.allocation.extra _ _ runtime.below runtime.formed.allocator.nodeTags
  obtain ⟨_,_,unheld⟩:=GenericFunctionTagFormation.fresh_above Q.allocation.extra _ _ tracker.global.nextPointerTag high (Nat.le_refl _)
  exact ⟨⟨readDone,childDone,child,lookup,afterRuntime,capacity,growth,parents,owned,leaf,node,nodeAt,nodeTag,nodeHidden,nodeParent,activity,targetActivity,oldNodes,roots,unheld⟩⟩


abbrev defaultTree {before tracker data owner id offset length}
    (Q : UniformWindow before tracker data owner id offset length .mut)
    (tag : BorTag) (start amount : UInt64) :=
  (GeneralBorrowRawDefaultExpression.child Q.allocation.extra tracker.global.protectedTags tag
    tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed).tree

abbrev defaultTracker (tracker : MachineHooks.BorrowState)
    (room : tracker.global.nextPointerTag.value<18446744073709551615) : MachineHooks.BorrowState :=
  {tracker with global:=GeneralBorrowFnEntryRegistration.advanced tracker.global room}

private theorem local_token (state : LocationState) (held : Bool)
    (realized : Realized state held) (right : OrdinaryBorrowAuthority.LocalWrite state held) :
    .exclusive ∈ tokens (denote state held) := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflicted => cases conflicted <;> cases accessed <;> cases held <;>
      simp_all [OrdinaryBorrowAuthority.LocalWrite,Realized,WellFormed,denote,tokens,LocationState.possible]
  | Cell | ReservedIM | Unique | Frozen | Disabled => cases accessed <;> cases held <;>
      simp_all [OrdinaryBorrowAuthority.LocalWrite,Realized,WellFormed,denote,tokens,LocationState.possible,Permission.isUnique]

private theorem foreign_no_clash (state : LocationState) (held : Bool)
    (realized : Realized state held) (right : OrdinaryBorrowAuthority.ForeignWrite state held) :
    ¬Clash (guard (denote state held)) .exclusive := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflicted => cases conflicted <;> cases accessed <;> cases held <;>
      simp_all [OrdinaryBorrowAuthority.ForeignWrite,Realized,WellFormed,denote,CandidateCurrentGrantResources.guard,Clash,LocationState.possible]
  | Cell | ReservedIM | Unique | Frozen | Disabled => cases accessed <;> cases held <;>
      simp_all [OrdinaryBorrowAuthority.ForeignWrite,Realized,WellFormed,denote,CandidateCurrentGrantResources.guard,Clash,LocationState.possible,Permission.isUnique]


/-- The actual Default child is issued in the actual installed world. -/
theorem default_issued {before tracker data owner id offset length}
    (Q : UniformWindow before tracker data owner id offset length .mut)
    (tag : BorTag) (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (start amount : UInt64) (stage : DefaultStage Q tag room start amount)
    (post : Before)
    (present : Present (ActualWorld post) id (Q.allocation.setExtra (defaultTree Q tag start amount))) :
    SpatialDelegation post (defaultTracker tracker room) id (Q.allocation.setExtra (defaultTree Q tag start amount))
      (extend Q.precise.completion stage.childIndex Q.pointer.grant) stage.childIndex := by
  have readFrame:=GeneralBorrowFreshReadFrame.frame Q.allocation.extra (.concrete tag)
    (Size.ofBytes start) (Size.ofBytes amount) .Read tracker.global.protectedTags .VisitChildrenOfAccessed
  have nodesEq:=congrArg BorrowTree.nodes readFrame
  have vacant : Q.allocation.extra.nodes.get stage.childIndex=none := by
    have empty:=stage.leaf.vacant
    dsimp only [GeneralBorrowRawDefaultExpression.read, GeneralBorrowRawSharedExpression.read] at empty
    rw [nodesEq] at empty
    exact empty
  have parentIssued:=CurrentCallResourceInstallation.spatial Q.issued Q.parents post (defaultTracker tracker room)
    (defaultTree Q tag start amount) present rfl stage.capacity
    (fun position root slot=>by rw [stage.roots];exact slot) stage.oldNodes stage.childIndex Q.pointer.grant vacant
  obtain ⟨parent,parentAt,_,_⟩:=Q.binding
  obtain ⟨current,currentAt,_⟩:=stage.oldNodes Q.pointer.grant parent parentAt
  exact SpatialDelegation.concrete parentIssued (.step (.refl _ current currentAt) stage.node stage.nodeAt stage.nodeParent)

/-- A technical child view keeps the same address and the SAME real parent-map
extension. Presence names the installed heap, rather than a synthetic world. -/
theorem default_window {before tracker data owner id offset length}
    (Q : UniformWindow before tracker data owner id offset length .mut)
    (tag : BorTag) (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (start amount : UInt64) (stage : DefaultStage Q tag room start amount)
    (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
    (bounds : start.toNat+amount.toNat≤Q.allocation.extra.locations.size.bytes.toNat)
    (post : Before)
    (present : Present (ActualWorld post) id (Q.allocation.setExtra (defaultTree Q tag start amount))) :
    ∃ nextData nextOwner,
      ∃ current : UniformWindow post (defaultTracker tracker room) nextData nextOwner id offset length .mut,
        current.pointer=CurrentCallResourceFnEntry.child_pointer Q tracker.global.nextPointerTag stage.childIndex ∧
        current.allocation=Q.allocation.setExtra (defaultTree Q tag start amount) ∧
        current.precise.completion=extend Q.precise.completion stage.childIndex Q.pointer.grant := by
  let pointer:=CurrentCallResourceFnEntry.child_pointer Q tracker.global.nextPointerTag stage.childIndex
  let precise:={Q.precise with completion:=extend Q.precise.completion stage.childIndex Q.pointer.grant}
  let nextData : Identities:={data with interpretation:={data.interpretation with
    pointers:=data.interpretation.pointers.push pointer
    loans:=data.interpretation.loans.push ⟨data.interpretation.pointers.size,some owner,Q.loan.depth⟩
    precise:=data.interpretation.precise.push (id,precise)}}
  have binding : PointerBinds (Q.allocation.setExtra (defaultTree Q tag start amount)) pointer := by
    refine ⟨stage.node,stage.nodeAt,stage.runtime.formed.allocator.nodeTags _ _ stage.nodeAt,?_⟩
    exact ⟨rfl,stage.nodeTag.symm⟩
  have embedding : ∀ byte,Window id offset length byte→byte.2<Q.allocation.len ∧
      Embeds (Q.allocation.setExtra (defaultTree Q tag start amount))
        (defaultTracker tracker room).global.protectedTags precise.completion stage.childIndex byte.2 .exclusive := by
    intro byte inside
    refine ⟨(Q.window byte inside).1,?_⟩
    have noWrap : start.toNat+amount.toNat<2^64:=Nat.lt_of_le_of_lt bounds (UInt64.toNat_lt _)
    have endEq : (start+amount).toNat=start.toNat+amount.toNat:=by simp only [UInt64.toNat_add,Nat.mod_eq_of_lt noWrap]
    have lowerByte : start.toNat≤byte.2:=by have interval:=inside.2;omega
    have upperByte : byte.2<(start+amount).toNat:=by have interval:=inside.2;omega
    intro segment member lower upper index node found
    simp only [Allocation.setExtra,Allocation.mapExtra,defaultTree] at member lower upper found ⊢
    obtain ⟨position,valid,same⟩:=Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
    subst segment
    have rights:=stage.owned position valid (by omega) (by omega) (by omega) index node found
    have realized:=CandidateCurrentGrantRuntime.realized _ _ (stage.runtime.possible position valid index node found)
      ((stage.runtime.formed.profile position valid).present index node found)
    constructor
    · intro below
      exact local_token _ _ realized (rights.1 below)
    · intro clash
      apply Classical.byContradiction
      intro outside
      exact foreign_no_clash _ _ realized (rights.2 outside) clash
  let current : UniformWindow post (defaultTracker tracker room) nextData data.interpretation.loans.size id offset length .mut := {
    loan:=⟨data.interpretation.pointers.size,some owner,Q.loan.depth⟩
    pointer:=pointer
    allocation:=Q.allocation.setExtra (defaultTree Q tag start amount)
    precise:=precise
    loanAt:=by simp [nextData]
    pointerAt:=by simp [nextData]
    pointerId:=rfl
    present:=present
    preciseAt:=by simp [nextData]
    binding:=binding
    issued:=default_issued Q tag room start amount stage post present
    parents:=stage.parents
    window:=embedding}
  exact ⟨nextData,data.interpretation.loans.size,current,rfl,rfl,rfl⟩


/-- Exact machine update used by the actual Default-mut MIR statement. -/
def defaultMachine (before : Before) (tracker : MachineHooks.BorrowState)
    (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (tree : BorrowTree) : Before :=
  {ReferenceBorrowDriver.allocatedMachine before tracker room with
    memory:=RetagEntry.updatedMemory before.memory id entry tree}

theorem installed_window {before tracker data owner id offset length}
    (Q : UniformWindow before tracker data owner id offset length .mut)
    (tag : BorTag) (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (start amount : UInt64) (stage : DefaultStage Q tag room start amount)
    (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
    (bounds : start.toNat+amount.toNat≤Q.allocation.extra.locations.size.bytes.toNat)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (allocationEq : Q.allocation=entry.allocation) :
    ∃ nextData nextOwner,
      ∃ current : UniformWindow (defaultMachine before tracker room id entry (defaultTree Q tag start amount))
        (defaultTracker tracker room) nextData nextOwner id offset length .mut,
        current.pointer=CurrentCallResourceFnEntry.child_pointer Q tracker.global.nextPointerTag stage.childIndex ∧
        current.allocation=Q.allocation.setExtra (defaultTree Q tag start amount) ∧
        current.precise.completion=extend Q.precise.completion stage.childIndex Q.pointer.grant := by
  have live : (defaultMachine before tracker room id entry (defaultTree Q tag start amount)).memory.live.find?
      (fun row=>row.1==id)=some (id,{entry with allocation:=entry.allocation.setExtra (defaultTree Q tag start amount)}) :=
    MemoryCopyBridge.live_lookup_replaced before.memory id _
  have present : Present (ActualWorld (defaultMachine before tracker room id entry (defaultTree Q tag start amount)))
      id (Q.allocation.setExtra (defaultTree Q tag start amount)) := by
    simp only [Present,ActualWorld,Array.toList_map]
    have member:=Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live)
    apply List.mem_map.mpr
    refine ⟨(id,{entry with allocation:=entry.allocation.setExtra (defaultTree Q tag start amount)}),member,?_⟩
    simp only [allocationEq]
  exact default_window Q tag room start amount stage startEq amountEq bounds _ present


theorem default_step
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (preciseOff : options.retag.preciseInteriorMut = false)
    (implicitOff : options.retag.implicitWrites = false)
    (debugOff : options.place.debugAssertions = false)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationFuel : options.limits.validation = validityFuel+1)
    (base offset len : UInt64)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourceBody : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (located : frame.location = .mir (RootReferenceFacts.location false))
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    {data : Identities} {owner : Nat}
    (Q : UniformWindow machine tracker data owner id offset.toNat len.toNat .mut)
    (allocationEq : Q.allocation=entry.allocation)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts Q.allocation.extra tracker.global)
    (distinct : Q.allocation.extra.roots.toList.Nodup)
    (short : Q.allocation.extra.nodes.size<65536)
    (nodeRoom : Q.allocation.extra.nodes.size+1≤4294967295)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (parentTag : BorTag) (concrete : Q.pointer.value.provenance=.concrete id parentTag)
    (bounds : offset.toNat+len.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat)
    (validSource : (1 : MIR.LocalId) < frame.locals.size) (validDest : (RootReferenceFacts.destination false) < frame.locals.size)
    (sourceLive : frame.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm))
    (sourceCached : frame.locals[1].layout = some ActualReferenceMetadata.reference)
    (destLive : frame.locals[RootReferenceFacts.destination false].value = .live (.immediate .uninit))
    (destUncached : frame.locals[RootReferenceFacts.destination false].layout = none)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (cacheOrigins : DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine))) :
    ∃ _stage : DefaultStage Q parentTag fresh offset len,
    let inner := ActualReferenceContext.config options remaining span
    let value := RetagReferencePlace.sliceValue inner.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len (RootReferenceInfo.layout false)
    let resultMachine := defaultMachine machine tracker fresh id entry (defaultTree Q parentTag offset len)
    ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
      (Storage.withCurrent frames frame machine) =
      (Storage.withCurrent frames (CopyHelperSteps.advance
        (ActualLocalCopy.written frame (RootReferenceFacts.destination false) (RootReferenceInfo.layout false) validDest value.imm)
        (RootReferenceFacts.location false)) resultMachine,.ok true) := by
  have qBounds : offset.toNat+len.toNat≤Q.allocation.extra.locations.size.bytes.toNat:=by rw [allocationEq];exact bounds
  obtain ⟨stage⟩:=default_prepare Q runtime parentTag concrete fresh distinct short nodeRoom offset len rfl rfl
    (by intro zero;rw [zero] at positive;exact UInt64.lt_irrefl _ positive) qBounds
  have readDone:=stage.readDone
  have childDone:=stage.childDone
  rw [allocationEq] at readDone childDone
  have capacity : entry.allocation.extra.locations.size=entry.allocation.byteSize:=by
    rw [←allocationEq];exact Q.issued.capability.treeExtent
  have step:=CurrentCallResourceAsMutCall.default_statement options limits remaining span preciseOff implicitOff debugOff cmp
    dynamicFuel validityFuel fuelEq validationFuel base offset len id entry positive nonzero signedFits frames frame machine
    sourceBody identity callee located tracker enabled defaultMode fresh parentTag bounds readDone childDone capacity
    validSource validDest sourceLive sourceCached destLive destUncached noClocks ghost shallow cachedAddress present race metadata cacheOrigins
  rw [←allocationEq] at step
  refine ⟨stage,?_⟩
  simpa only [defaultMachine,defaultTree] using step


private def atOffset {before tracker data owner id offset length}
    (window : UniformWindow before tracker data owner id offset length .mut)
    (nextOffset : Nat) (same : nextOffset=offset) : UniformWindow before tracker data owner id nextOffset length .mut :=
  {window with window:=fun byte inside=>window.window byte (by simpa only [same] using inside)}

private theorem tick_model (options remaining span machine)
    (model : DuplicatePrefixCallModel.Model options remaining span machine) :
    DuplicatePrefixCallModel.Model options remaining span (RootZeroCompleteState.tick options remaining span machine) := by
  have flags:=RootZeroCompleteState.tick_flags options remaining span machine
  have unchecked:=model.unchecked
  have noGc:=model.noGc
  rw [(actual_fields options () (remaining+1) span).terminators] at unchecked noGc
  unfold RootZeroCompleteState.tick SourceControl.accounted at flags ⊢
  rw [(actual_fields options () (remaining+1) span).terminators] at flags ⊢
  exact {model with
    unchecked:=by rw [(actual_fields options () (remaining+1) span).terminators];exact flags.1.trans unchecked,
    noGc:=by rw [(actual_fields options () (remaining+1) span).terminators];exact flags.2.trans noGc}

variable {options remaining span root before tracker data owner id offset len W place limits count}
    {C : Conditions options remaining span #[] root before tracker data owner id offset len W place}
    {out : Output limits C count} {ready : CurrentCallResourceBodyReadiness.Ready C} {nextData nextOwner}
    {Q : UniformWindow (CurrentCallResourceSharedStage.machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ nextData nextOwner id offset len.toNat .mut}
    {stage : CurrentCallResourceSharedResources.Stage Q out.sourceOutput.tag (UInt64.ofNat offset) len (CurrentCallResourceBodyReadiness.current_room out ready)}
    (result : CurrentCallResourceLenReturn.Result out ready Q stage)

abbrev beforeDefault := RootZeroCompleteState.tick options remaining span (RootZeroCompleteState.tick options remaining span result.machine)

/-- Actual q resources at the accepted statement boundary; the two guard ticks
change control accounting and preserve this SAME source view. -/
theorem current_before_default : ∃ currentData currentOwner,
    ∃ current : UniformWindow (beforeDefault result) (CurrentCallResourceLenReturn.postTracker out ready)
      currentData currentOwner id (UInt64.ofNat offset).toNat len.toNat .mut,
      current.pointer=Q.pointer ∧ current.allocation=CurrentCallResourceLenCapability.sourceAllocation out ready ∧
      current.precise.completion=result.completion ∧
      DuplicatePrefixBorrowContract.RuntimeFacts current.allocation.extra (CurrentCallResourceLenReturn.postTracker out ready).global ∧
      current.allocation.extra.roots.toList.Nodup ∧ current.allocation.extra.nodes.size+4<65536 := by
  obtain ⟨currentData,currentOwner,current,pointer,allocation,completion⟩:=CurrentCallResourceAsMut.current out ready result
  let first:=CurrentCallResourceAsMutCall.accountedWindow options remaining span current
  let second:=CurrentCallResourceAsMutCall.accountedWindow options remaining span first
  let adjusted:=atOffset second (UInt64.ofNat offset).toNat (CurrentCallResourceSharedStage.source_bounds out).1
  have pointerEq : adjusted.pointer=Q.pointer:=pointer
  have allocationEq : adjusted.allocation=CurrentCallResourceLenCapability.sourceAllocation out ready:=allocation
  have completionEq : adjusted.precise.completion=result.completion:=completion
  have actualRuntime : DuplicatePrefixBorrowContract.RuntimeFacts adjusted.allocation.extra (CurrentCallResourceLenReturn.postTracker out ready).global := by
    rw [allocationEq]
    simpa only [CurrentCallResourceLenCapability.sourceAllocation,Allocation.setExtra,Allocation.mapExtra] using result.runtime
  have distinct : adjusted.allocation.extra.roots.toList.Nodup := by
    rw [allocationEq]
    simpa only [CurrentCallResourceLenCapability.sourceAllocation,Allocation.setExtra,Allocation.mapExtra] using CurrentCallResourceLenRoots.rootsDistinct out ready result
  have margin : adjusted.allocation.extra.nodes.size+4<65536 := by
    rw [allocationEq]
    simpa only [CurrentCallResourceLenCapability.sourceAllocation,Allocation.setExtra,Allocation.mapExtra] using CurrentCallResourceAsMutCall.nodes_margin result
  exact ⟨currentData,currentOwner,adjusted,pointerEq,allocationEq,completionEq,actualRuntime,distinct,margin⟩


/-- The accepted guard's actual physical statement boundary. -/
structure StatementInput where
  frame : CompilerFrameContext.ActualFrame
  trace : SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
    (Storage.withCurrent #[] result.rootFrame result.machine) (Storage.withCurrent #[] frame (beforeDefault result))
  body : frame.body=RootBody.reflected.body.body
  identity : frame.bodyIdentity=RootBody.reflected.body.identity
  callee : frame.functionInstance=RootBody.reflected.functionInstance
  clocks : frame.extra.dataRace=none
  location : frame.location=.mir ⟨6,7⟩
  size : frame.locals.size=25
  source : frame.locals[1]?=some ⟨.live (.immediate (RetagReferencePlace.sliceValue
    (ActualReferenceContext.config options remaining span).access.runtime.base Q.pointer.value len ActualReferenceMetadata.reference).imm),some ActualReferenceMetadata.reference⟩
  dest15 : frame.locals[15]?=some ⟨.live (.immediate .uninit),none⟩
  dest16 : frame.locals[16]?=some ⟨.live (.immediate .uninit),none⟩
  extra : frame.extra=result.rootFrame.extra
  returnPlace : frame.returnPlace=result.rootFrame.returnPlace
  continuation : frame.returnContinuation=result.rootFrame.returnContinuation
  vaList : frame.vaList=result.rootFrame.vaList
  second : frame.locals[2]?=result.rootFrame.locals[2]?
  facts : GenericLenAcceptedPrelude.FrameFacts result.rootFrame frame
  track : frame.trackCallerArg=result.rootFrame.trackCallerArg
  immediate : CopyHelperCleanup.AllImmediate frame

theorem statement_input (nonzero : count≠0) (within : count≤len/2) : Nonempty (StatementInput result) := by
  obtain ⟨frame,trace,⟨body,identity,callee,extra,returnPlace,continuation,varargs,localsId,callerArg,size,location,source,second,dest15,dest16,immediate⟩,facts⟩:=
    CurrentCallResourceAsMutCall.accepted_prefix result nonzero within
  obtain ⟨rootBody,rootIdentity,rootCallee,rootClocks,rest⟩:=CurrentCallResourceLenFacts.root_metadata result
  have sourcePair:=CurrentCallResourceAsMutCall.source_pair result
  rw [←result.sourcePointer] at sourcePair
  exact ⟨⟨frame,trace,body.trans rootBody,identity.trans rootIdentity,callee.trans rootCallee,
    (congrArg MachineHooks.FrameExtra.dataRace extra).trans rootClocks,location,size,
    source.trans sourcePair,dest15,dest16,extra,returnPlace,continuation,varargs,second,facts,callerArg,immediate⟩⟩

theorem model_before_default : DuplicatePrefixCallModel.Model options remaining span (beforeDefault result) :=
  tick_model _ _ _ _ (tick_model _ _ _ _ (CurrentCallResourceLenFacts.model result))

private theorem tick_addresses (options remaining span machine) :
    (RootZeroCompleteState.tick options remaining span machine).user.addresses=machine.user.addresses := by
  unfold RootZeroCompleteState.tick SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  rfl

private theorem tick_types (options remaining span machine) :
    (RootZeroCompleteState.tick options remaining span machine).user.payload.payload.user.types=machine.user.payload.payload.user.types := by
  unfold RootZeroCompleteState.tick SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  rfl

include result in
theorem source_address_before_default : ∃ base : UInt64,
    (beforeDefault result).user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩ ∧
    Q.pointer.value=Pointer.new (.concrete id out.sourceOutput.tag) (Size.ofBytes (base+UInt64.ofNat offset)) ∧
    base+UInt64.ofNat offset≠0 := by
  obtain ⟨base,cached,pointer,nonzero⟩:=CurrentCallResourceAsMutCall.source_address result
  refine ⟨base,?_,pointer,nonzero⟩
  rw [beforeDefault,tick_addresses,tick_addresses]
  exact cached


private theorem window_bounds {before tracker data owner id offset length}
    (window : UniformWindow before tracker data owner id offset length .mut)
    (positive : 0<length) : offset+length≤window.allocation.extra.locations.size.bytes.toNat := by
  have last:= (window.window (id,offset+length-1) ⟨rfl,by omega,by omega⟩).1
  have extent:=window.issued.capability.extent
  have capacity:=window.issued.capability.treeExtent
  rw [extent,←capacity] at last
  omega

private theorem fetched {frame : CompilerFrameContext.ActualFrame} {index : Nat} {slot : LocalState Provenance LocalLayout}
    (valid : index<frame.locals.size) (found : frame.locals[index]?=some slot) : frame.locals[index]=slot :=
  Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans found)

abbrev sourceEntry := {(CurrentCallResourceLenInvoke.entry out) with allocation:=CurrentCallResourceLenCapability.sourceAllocation out ready}

def defaultFrame (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frame : CompilerFrameContext.ActualFrame) (valid16 : (16 : MIR.LocalId)<frame.locals.size)
    (id : AllocId) (tag : BorTag) (base start len : UInt64) : CompilerFrameContext.ActualFrame :=
  CopyHelperSteps.advance (ActualLocalCopy.written frame 16 (RootReferenceInfo.layout false) valid16
    (RetagReferencePlace.sliceValue (ActualReferenceContext.config options remaining span).access.runtime.base
      (Pointer.new (.concrete id tag) (Size.ofBytes (base+start))) len (RootReferenceInfo.layout false)).imm)
    (RootReferenceFacts.location false)

/-- Output of the actual accepted guard and Default-mut statement. All resources
and the concrete helper argument name the SAME installed machine. -/
structure DefaultResult where
  qData : Identities
  qOwner : Nat
  qWindow : UniformWindow (beforeDefault result) (CurrentCallResourceLenReturn.postTracker out ready)
    qData qOwner id (UInt64.ofNat offset).toNat len.toNat .mut
  qPointer : qWindow.pointer=Q.pointer
  qAllocation : qWindow.allocation=(sourceEntry (out:=out) (ready:=ready)).allocation
  qCompletion : qWindow.precise.completion=result.completion
  input : StatementInput result
  base : UInt64
  cached : (beforeDefault result).user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩
  address : Q.pointer.value=Pointer.new (.concrete id out.sourceOutput.tag) (Size.ofBytes (base+UInt64.ofNat offset))
  nonzero : base+UInt64.ofNat offset≠0
  room : (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag.value<18446744073709551615
  stage : DefaultStage qWindow out.sourceOutput.tag room (UInt64.ofNat offset) len
  qRuntime : DuplicatePrefixBorrowContract.RuntimeFacts qWindow.allocation.extra (CurrentCallResourceLenReturn.postTracker out ready).global
  qDistinct : qWindow.allocation.extra.roots.toList.Nodup
  qMargin : qWindow.allocation.extra.nodes.size+4<65536
  valid16 : (16 : MIR.LocalId)<input.frame.locals.size
  machine : Before
  machineEq : machine=defaultMachine (beforeDefault result) (CurrentCallResourceLenReturn.postTracker out ready) room id
    (sourceEntry (out:=out) (ready:=ready)) (defaultTree qWindow out.sourceOutput.tag (UInt64.ofNat offset) len)
  frame : CompilerFrameContext.ActualFrame
  frameEq : frame=defaultFrame options remaining span input.frame valid16 id
    (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag base (UInt64.ofNat offset) len
  trace : SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
    (Storage.withCurrent #[] result.rootFrame result.machine) (Storage.withCurrent #[] frame machine)
  currentData : Identities
  currentOwner : Nat
  current : UniformWindow machine (defaultTracker (CurrentCallResourceLenReturn.postTracker out ready) room)
    currentData currentOwner id (UInt64.ofNat offset).toNat len.toNat .mut
  pointer : current.pointer=CurrentCallResourceFnEntry.child_pointer qWindow (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag stage.childIndex
  allocation : current.allocation=qWindow.allocation.setExtra (defaultTree qWindow out.sourceOutput.tag (UInt64.ofNat offset) len)
  completion : current.precise.completion=extend qWindow.precise.completion stage.childIndex qWindow.pointer.grant

theorem default_from_return (nonzero : count≠0) (within : count≤len/2) : Nonempty (DefaultResult result) := by
  obtain ⟨qData,qOwner,qWindow,qPointer,qAllocation,qCompletion,qRuntime,qDistinct,qMargin⟩:=current_before_default result
  obtain ⟨input⟩:=statement_input result nonzero within
  obtain ⟨base,cached,address,nonnull⟩:=source_address_before_default result
  have positive : (0 : UInt64)<len:=UInt64.lt_iff_toNat_lt.mpr (by simpa only [UInt64.toNat_zero] using C.positive)
  have model:=model_before_default result
  have enabled : (beforeDefault result).borrowTracker=some (CurrentCallResourceLenReturn.postTracker out ready):=result.tracked
  obtain ⟨old,oldEnabled,oldMode⟩:=model.defaultTracker
  have sameTracker : old=CurrentCallResourceLenReturn.postTracker out ready:=Option.some.inj (oldEnabled.symm.trans enabled)
  subst old
  have room : (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag.value<18446744073709551615:=
    UInt64.lt_iff_toNat_lt.mpr (by
      change (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag.value.toNat<18446744073709551615
      have margin:=CurrentCallResourceAsMutCall.tags_margin (out:=out) (ready:=ready)
      omega)
  have concrete : qWindow.pointer.value.provenance=.concrete id out.sourceOutput.tag:=by rw [qPointer,address];rfl
  have valid1 : (1 : MIR.LocalId)<input.frame.locals.size:=by rw [input.size];decide
  have valid16 : (16 : MIR.LocalId)<input.frame.locals.size:=by rw [input.size];decide
  have source:=fetched valid1 input.source
  rw [address] at source
  have baseEq : (ActualReferenceContext.config options remaining span).access.runtime.base=
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base := by
    rw [CanonicalConfigFacts.actual_access_runtime,CanonicalConfigFacts.actual_access_runtime]
  rw [baseEq] at source
  have dest:=fetched valid16 input.dest16
  have bounds:=window_bounds qWindow C.positive
  have entryBounds : (UInt64.ofNat offset).toNat+len.toNat≤(sourceEntry (out:=out) (ready:=ready)).allocation.extra.locations.size.bytes.toNat:=by
    dsimp only [sourceEntry]
    rw [←qAllocation]
    exact bounds
  have live : (beforeDefault result).memory.live.find? (fun row=>row.1==id)=some (id,sourceEntry (out:=out) (ready:=ready)):=result.sourceLive
  have origins : DuplicatePrefixTypeCacheOrigins.Origins (beforeDefault result).user.payload.payload.user.types := by
    unfold beforeDefault RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact CurrentCallResourceLenFacts.origins result
  obtain ⟨defaultStage,step⟩:=default_step options limits remaining span model.preciseOff model.implicitOff model.debugOff
    model.nullComparator C.dynamicFuel C.validationFuel C.dynamicEq C.validationEq base (UInt64.ofNat offset) len id
    (sourceEntry (out:=out) (ready:=ready)) positive nonnull C.signedFits #[] input.frame (beforeDefault result)
    input.body input.identity input.callee input.location (CurrentCallResourceLenReturn.postTracker out ready) enabled
    qWindow qAllocation qRuntime qDistinct (by omega) (by omega) oldMode room out.sourceOutput.tag concrete entryBounds
    valid1 valid16 (congrArg LocalState.value source) (congrArg LocalState.layout source)
    (congrArg LocalState.value dest) (congrArg LocalState.layout dest) input.clocks model.ghostOff model.shallow cached live
    model.noDataRace model.metadata origins
  obtain ⟨currentData,currentOwner,current,pointer,allocation,completion⟩:=installed_window qWindow out.sourceOutput.tag room
    (UInt64.ofNat offset) len defaultStage rfl rfl bounds (sourceEntry (out:=out) (ready:=ready)) qAllocation
  exact ⟨{
    qData:=qData,qOwner:=qOwner,qWindow:=qWindow,qPointer:=qPointer,qAllocation:=qAllocation,qCompletion:=qCompletion,
    input:=input,base:=base,cached:=cached,address:=address,nonzero:=nonnull,room:=room,stage:=defaultStage,
    qRuntime:=qRuntime,qDistinct:=qDistinct,qMargin:=qMargin,valid16:=valid16,
    machine:=_,machineEq:=rfl,frame:=_,frameEq:=rfl,
    trace:=SuccessfulTrace.append input.trace (.next step (.refl _)),
    currentData:=currentData,currentOwner:=currentOwner,current:=current,pointer:=pointer,allocation:=allocation,completion:=completion}⟩


namespace DefaultResult
variable (done : DefaultResult result)

abbrev nextTracker := defaultTracker (CurrentCallResourceLenReturn.postTracker out ready) done.room
abbrev entry := {sourceEntry (out:=out) (ready:=ready) with allocation:=done.current.allocation}

theorem enabled : done.machine.borrowTracker=some done.nextTracker := by
  rw [done.machineEq]
  rfl

theorem live : done.machine.memory.live.find? (fun row=>row.1==id)=some (id,done.entry) := by
  have allocationEq:=done.allocation.trans (congrArg (fun allocation : Allocation Provenance BorrowTree=>
    allocation.setExtra (defaultTree done.qWindow out.sourceOutput.tag (UInt64.ofNat offset) len)) done.qAllocation)
  rw [done.machineEq]
  dsimp only [entry]
  rw [allocationEq]
  exact MemoryCopyBridge.live_lookup_replaced _ _ _

theorem model : DuplicatePrefixCallModel.Model options remaining span done.machine := by
  rw [done.machineEq]
  obtain ⟨old,enabled,mode⟩:=(model_before_default result).defaultTracker
  have oldEq : old=CurrentCallResourceLenReturn.postTracker out ready :=
    Option.some.inj (enabled.symm.trans result.tracked)
  subst old
  exact {model_before_default result with defaultTracker:=⟨done.nextTracker,rfl,mode⟩}

theorem origins : DuplicatePrefixTypeCacheOrigins.Origins done.machine.user.payload.payload.user.types := by
  have typesEq:=congrArg (fun machine : Before=>machine.user.payload.payload.user.types) done.machineEq
  dsimp only [defaultMachine,ReferenceBorrowDriver.allocatedMachine] at typesEq
  rw [typesEq,beforeDefault,tick_types,tick_types]
  exact CurrentCallResourceLenFacts.origins result

theorem active : ∃ thread,done.machine.threads.activeThread?=some thread ∧ thread.topUserRelevantFrame=some 0 := by
  rw [done.machineEq]
  exact result.active

theorem pointer_value : done.current.pointer.value=Pointer.new
    (.concrete id (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag)
    (Size.ofBytes (done.base+UInt64.ofNat offset)) := by
  rw [done.pointer]
  dsimp only [CurrentCallResourceFnEntry.child_pointer]
  rw [done.qPointer,done.address]
  rfl

theorem runtime : DuplicatePrefixBorrowContract.RuntimeFacts done.current.allocation.extra done.nextTracker.global := by
  rw [done.allocation]
  simpa only [Allocation.setExtra,Allocation.mapExtra] using done.stage.runtime

theorem distinct : done.current.allocation.extra.roots.toList.Nodup := by
  rw [done.allocation]
  dsimp only [Allocation.setExtra,Allocation.mapExtra]
  rw [done.stage.roots]
  exact done.qDistinct

theorem margin : done.current.allocation.extra.nodes.size+3<65536 := by
  have growth:=done.stage.growth
  have initial:=done.qMargin
  rw [done.allocation]
  dsimp only [Allocation.setExtra,Allocation.mapExtra,defaultTree]
  omega

theorem fresh : done.nextTracker.global.nextPointerTag.value<18446744073709551615 := by
  apply UInt64.lt_iff_toNat_lt.mpr
  change done.nextTracker.global.nextPointerTag.value.toNat<18446744073709551615
  have successor : done.nextTracker.global.nextPointerTag.value.toNat=
      (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag.value.toNat+1:=
    GenericFunctionEntryNumerics.successor_value _ done.room
  have reserve:=CurrentCallResourceAsMutCall.tags_margin (out:=out) (ready:=ready)
  omega

theorem cachedPost : done.machine.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,done.base⟩ := by
  rw [done.machineEq]
  exact done.cached

private theorem written_same (frame : CompilerFrameContext.ActualFrame) (index : MIR.LocalId)
    (layout : LocalLayout) (valid : index<frame.locals.size) (value : Immediate Provenance) :
    (ActualLocalCopy.written frame index layout valid value).locals[index]?=some ⟨.live (.immediate value),some layout⟩ := by
  simp [ActualLocalCopy.written,LocalPlaces.cachePlaceLayout]

private theorem written_other (frame : CompilerFrameContext.ActualFrame) (index query : MIR.LocalId)
    (layout : LocalLayout) (valid : index<frame.locals.size) (value : Immediate Provenance) (different : query≠index) :
    (ActualLocalCopy.written frame index layout valid value).locals[query]?=frame.locals[query]? := by
  simp [ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Ne.symm different]

theorem size : done.frame.locals.size=25 := by
  rw [done.frameEq]
  simpa only [defaultFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.size_set] using done.input.size

theorem body : done.frame.body=RootBody.reflected.body.body := by rw [done.frameEq];exact done.input.body
 theorem identity : done.frame.bodyIdentity=RootBody.reflected.body.identity := by rw [done.frameEq];exact done.input.identity
 theorem callee : done.frame.functionInstance=RootBody.reflected.functionInstance := by rw [done.frameEq];exact done.input.callee
 theorem location : done.frame.location=.mir ⟨6,8⟩ := by rw [done.frameEq];rfl
 theorem clocks : done.frame.extra.dataRace=none := by rw [done.frameEq];exact done.input.clocks

 theorem slot15 : done.frame.locals[15]?=some ⟨.live (.immediate .uninit),none⟩ := by
  rw [done.frameEq]
  dsimp only [defaultFrame,CopyHelperSteps.advance]
  rw [written_other _ 16 15 _ _ _ (by decide)]
  exact done.input.dest15

 theorem slot16 : done.frame.locals[16]?=some ⟨.live (.immediate (RetagReferencePlace.sliceValue
    (ActualReferenceContext.config options remaining span).access.runtime.base
    (Pointer.new (.concrete id (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag)
      (Size.ofBytes (done.base+UInt64.ofNat offset))) len ActualReferenceMetadata.reference).imm),some ActualReferenceMetadata.reference⟩ := by
  rw [done.frameEq]
  dsimp only [defaultFrame,CopyHelperSteps.advance]
  exact written_same _ _ _ _ _

end DefaultResult

/-- The SAME actual Default-mut result immediately enters and runs the real
as_mut_ptr helper. No operation-success certificate is supplied by a caller. -/
theorem seed_from_default (done : DefaultResult result) (budget : Nat) (dispatch : limits.callDispatch=budget+1) :
    ∃ (fresh : done.nextTracker.global.nextPointerTag.value<18446744073709551615)
      (valid15 : (15 : MIR.LocalId)<done.frame.locals.size),
      Nonempty (CurrentCallResourceAsMutCall.Seed options limits remaining span done.current done.entry done.frame done.base
        (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15) := by
  have model:=done.model
  obtain ⟨old,oldEnabled,oldMode⟩:=model.defaultTracker
  have oldEq : old=done.nextTracker:=Option.some.inj (oldEnabled.symm.trans done.enabled)
  subst old
  have valid15 : (15 : MIR.LocalId)<done.frame.locals.size:=by rw [done.size];decide
  have valid16 : (16 : MIR.LocalId)<done.frame.locals.size:=by rw [done.size];decide
  have slot15:=fetched valid15 done.slot15
  have slot16:=fetched valid16 done.slot16
  have positive : (0 : UInt64)<len:=UInt64.lt_iff_toNat_lt.mpr (by simpa only [UInt64.toNat_zero] using C.positive)
  have bounds:=window_bounds done.current C.positive
  have capacity:=done.current.issued.capability.treeExtent
  have physicalBounds : (UInt64.ofNat offset).toNat+len.toNat≤done.entry.allocation.byteSize.bytes.toNat := by
    rw [←capacity]
    exact bounds
  obtain ⟨thread,active,topZero⟩:=done.active
  let caller:=AsMutUncachedCall.cachedCaller done.frame valid15
  let next:=AsMutPtrReturn.accountedMachine options remaining span done.machine
  let destination:=(LocalPlaces.localRuntimePlace 0 caller 15 CopyCompilerFacts.destPointerLayout).stackView
  let pushed:=AsMutPush.pushed options.userRelevantCrates (Storage.withCurrent #[] caller next) destination
  have pushedSize : pushed.stack.frames.size=2:=rfl
  obtain ⟨index,current,top,present⟩:=RelevanceCurrent.exists_current pushed.stack.frames thread
    (by rw [pushedSize];decide) (by
      intro index cached
      have same : index=0:=Option.some.inj (cached.symm.trans topZero)
      rw [same,pushedSize]
      decide)
  have pointerEq:=done.pointer_value
  have concrete := congrArg Pointer.provenance pointerEq
  have fresh:=done.fresh
  have room:=done.margin
  obtain ⟨ctx⟩:=ActualReferenceContext.exists_context options remaining span model.preciseOff model.implicitOff
  obtain ⟨seed⟩:=CurrentCallResourceAsMutCall.seed_from_window options limits remaining budget dispatch span ctx model.debugOff model.nullComparator
    C.dynamicFuel C.validationFuel C.dynamicEq C.validationEq id done.entry done.base (UInt64.ofNat offset) len
    (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag positive done.nonzero C.signedFits physicalBounds
    done.frame done.machine done.nextTracker done.enabled oldMode fresh done.current rfl concrete pointerEq done.runtime done.distinct
    (by omega) (by omega) (by omega) capacity valid15 (congrArg LocalState.value slot15) (congrArg LocalState.layout slot15)
    done.clocks model.ghostOff model.shallow done.cachedPost done.live model.noDataRace model.metadata done.origins
    thread index current active top present (DuplicatePrefixCallModel.sourceComparator options remaining span done.machine model)
    done.body done.identity done.callee done.location valid16 (congrArg LocalState.value slot16) (congrArg LocalState.layout slot16)
    model.noBackend model.unchecked model.noGc model.fixedScheduler
  exact ⟨fresh,valid15,⟨seed⟩⟩


namespace DefaultResult
variable (done : DefaultResult result)

theorem addresses : done.machine.user.addresses=result.machine.user.addresses := by
  have addressEq:=congrArg (fun machine : Before=>machine.user.addresses) done.machineEq
  dsimp only [defaultMachine,ReferenceBorrowDriver.allocatedMachine] at addressEq
  exact addressEq.trans ((tick_addresses _ _ _ _).trans (tick_addresses _ _ _ _))

theorem types : done.machine.user.payload.payload.user.types=result.machine.user.payload.payload.user.types := by
  have typesEq:=congrArg (fun machine : Before=>machine.user.payload.payload.user.types) done.machineEq
  dsimp only [defaultMachine,ReferenceBorrowDriver.allocatedMachine] at typesEq
  exact typesEq.trans ((tick_types _ _ _ _).trans (tick_types _ _ _ _))

private theorem tick_extras (options remaining span machine) :
    (RootZeroCompleteState.tick options remaining span machine).user.payload.payload.user.runtime.extras=machine.user.payload.payload.user.runtime.extras := by
  unfold RootZeroCompleteState.tick SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  rfl

theorem extras : done.machine.user.payload.payload.user.runtime.extras=result.machine.user.payload.payload.user.runtime.extras := by
  have extraEq:=congrArg (fun machine : Before=>machine.user.payload.payload.user.runtime.extras) done.machineEq
  dsimp only [defaultMachine,ReferenceBorrowDriver.allocatedMachine] at extraEq
  exact extraEq.trans ((tick_extras _ _ _ _).trans (tick_extras _ _ _ _))

theorem other (index : MIR.LocalId) (different : index≠16) : done.frame.locals[index]?=done.input.frame.locals[index]? := by
  rw [done.frameEq]
  dsimp only [defaultFrame,CopyHelperSteps.advance]
  exact written_other _ _ _ _ _ _ different

theorem root_metadata : done.frame.returnPlace=result.rootFrame.returnPlace ∧
    done.frame.returnContinuation=result.rootFrame.returnContinuation ∧done.frame.vaList=result.rootFrame.vaList := by
  rw [done.frameEq]
  exact ⟨done.input.returnPlace,done.input.continuation,done.input.vaList⟩

theorem count_slot : done.frame.locals[2]?=result.rootFrame.locals[2]? :=
  (DefaultResult.other (result:=result) done 2 (by decide)).trans done.input.second

theorem slot0 : done.frame.locals[0]?=result.rootFrame.locals[0]? :=
  (DefaultResult.other (result:=result) done 0 (by decide)).trans done.input.facts.slot0

theorem slot13 : done.frame.locals[13]?=some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩ :=
  (DefaultResult.other (result:=result) done 13 (by decide)).trans done.input.facts.slot13

theorem high (index : Nat) (bound : 17≤index) : done.frame.locals[index]?=result.rootFrame.locals[index]? :=
  (DefaultResult.other (result:=result) done index (by
    intro same
    subst index
    exact Nat.not_le_of_lt (by decide : 16<17) bound)).trans (done.input.facts.high index bound)


theorem immediate : CopyHelperCleanup.AllImmediate done.frame := by
  rw [done.frameEq]
  exact CopyHelperCleanup.all_immediate_written _ _ _ _ _ done.input.immediate

end DefaultResult

/-- The complete actual accepted prefix from the SAME returned Len state to
as_mut_ptr's helper Return. The public input contains no successful operation. -/
theorem invoke (nonzero : count≠0) (within : count≤len/2) (budget : Nat) (dispatch : limits.callDispatch=budget+1) :
    ∃ done : DefaultResult result,
    ∃ (fresh : done.nextTracker.global.nextPointerTag.value<18446744073709551615)
      (valid15 : (15 : MIR.LocalId)<done.frame.locals.size),
    ∃ seed : CurrentCallResourceAsMutCall.Seed options limits remaining span done.current done.entry done.frame done.base
        (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15,
      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent #[] result.rootFrame result.machine)
        (Storage.withCurrent #[(AsMutUncachedCall.cachedCaller done.frame valid15)] seed.helper seed.machine) := by
  obtain ⟨done⟩:=default_from_return result nonzero within
  obtain ⟨fresh,valid15,⟨seed⟩⟩:=seed_from_default result done budget dispatch
  exact ⟨done,fresh,valid15,seed,SuccessfulTrace.append done.trace seed.trace⟩

end
end DuplicatePrefix.CurrentCallResourceAsMutInvoke
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallResourceAsMutInvoke.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual resource AsMut invocation dependency {dependency}"
