import duplicate_prefix.CurrentCallSpatialSourceInstall
import duplicate_prefix.CurrentCallSourceInstallState

/-! The actual spatial source copy retains the existing full finite State and
all-live high-water facts. Source retagging changes only tree extras and keeps
byte storage/provenance; this asserts no such full invariant after Bool clear. -/
namespace DuplicatePrefix.CurrentCallSpatialSourceState
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Input Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallSpatialCover CurrentCallResourceNormalization GeneralRangeMapOrigins
open GeneralBorrowFnEntryRegistration TypedBorrowSteps ReferenceBorrowDriver
open CanonicalConfigFacts ActualReferenceContext CurrentCallTypedFnEntry CurrentCallTypedSourceCopy CurrentCallSpatialSourceInstall
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
noncomputable section

/-- Root uniqueness follows from the one actual allocator construction, without
any per-cell completion being selected as a whole-request origin. -/
private theorem roots {before tracker ctx mode offset length}
    (role : RoleCover before tracker ctx mode offset length) (exclusive : demandOf mode=.exclusive)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup)
    (short : role.backing.allocation.extra.nodes.size<65536) (nodeRoom : role.backing.allocation.extra.nodes.size+1≤4294967295)
    (frame : FrameState) (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
    (nonzero : amount≠0) (bounds : start.toNat+amount.toNat≤role.backing.allocation.extra.locations.size.bytes.toNat) :
    (CurrentCallSpatialEntryRead.output role frame room start amount).child.tree.roots.toList.Nodup := by
  obtain ⟨contract,afterRuntime,_⟩ := CurrentCallSpatialEntryRead.invoke role exclusive runtime distinct short frame room start amount startEq amountEq nonzero bounds
  have positive : 0<length := by
    have pos : 0<amount.toNat := Nat.pos_of_ne_zero (fun zero=>nonzero (UInt64.toNat_inj.mp zero))
    omega
  have request : Window role.backing.id offset length (role.backing.id,offset) := ⟨rfl,by omega,by omega⟩
  obtain ⟨i,cell⟩ := role.covered _ request
  have overlap : ∃byte,Window role.backing.id offset length byte ∧Window role.backing.id role.backing.cells[i].offset role.backing.cells[i].length byte := ⟨_,request,cell⟩
  obtain ⟨node,present,_,binding⟩ := (role.roles i overlap).binding
  have afterAt : (CurrentCallSpatialEntryRead.read role frame room start amount).tree.nodes.get (role.roles i overlap).grant=some node := by rw [contract.nodes];exact present
  have fresh := (GeneralBorrowFnEntryRegistrationRuntime.prepare role.backing.allocation.extra tracker.global frame role.backing.id room runtime).2.2.2.2.2
  have freshAfter : GeneralBorrowTagMap.Fresh (CurrentCallSpatialEntryRead.read role frame room start amount).tree.tagMapping tracker.global.nextPointerTag := by rw [contract.tags];exact fresh
  have afterRoom : (CurrentCallSpatialEntryRead.read role frame room start amount).tree.nodes.size+1≤4294967295 := by
    change (CurrentCallSpatialEntryRead.read role frame room start amount).tree.nodes.data.size+1≤_
    rw [contract.nodes];exact nodeRoom
  have afterBounds : start.toNat+amount.toNat≤(CurrentCallSpatialEntryRead.read role frame room start amount).tree.locations.size.bytes.toNat := by rw [contract.capacity];exact bounds
  cases value : role.family.value.provenance with
  | concrete id tag =>
    have tagEq : tag=node.tag := (show id=role.family.allocation ∧tag=node.tag from by simpa only [value,Family.at] using binding).2
    have tagged := afterRuntime.formed.allocator.nodeTags _ _ afterAt
    let tree := (CurrentCallSpatialEntryRead.read role frame room start amount).tree
    let depth := GeneralBorrowStructuralHistoryMutable.depth tree afterRuntime.formed.toState
    let slot := GeneralBorrowStructuralHistoryMutable.slot tree afterRuntime.formed.toState (role.roles i overlap).grant node afterAt afterRoom
    have metadata := GeneralBorrowFreshMetadataChildMutableSlot.build tree depth afterRuntime.formed.children afterRuntime.formed.covered
      node.tag tracker.global.nextPointerTag (role.roles i overlap).grant node tagged afterAt freshAfter slot start amount nonzero
      afterRuntime.formed.well afterRuntime.formed.fits afterBounds
    have unique : (GeneralBorrowFreshMetadataChildMutableSlot.result tree node.tag tracker.global.nextPointerTag start amount).roots.toList.Nodup := by
      rw [metadata.roots,contract.roots];exact distinct
    simpa only [CurrentCallSpatialEntryRead.output,CurrentCallSpatialRows.provenance,value,tagEq,GeneralBorrowFreshMetadataChildMutableSlot.result,tree] using unique
  | wildcard =>
    let tree := (CurrentCallSpatialEntryRead.read role frame room start amount).tree
    obtain ⟨mapping,index,inserted,_,vacant,_,_,_⟩ := GeneralBorrowWildcardConstructorSlot.select tree _ afterRuntime tracker.global.nextPointerTag freshAfter afterRoom (.ReservedFrz false) .None
    have exactCtor := GeneralBorrowWildcardConstructorExact.exact tree afterRuntime.formed.toState tracker.global.nextPointerTag freshAfter afterRoom mapping index inserted
      (.ReservedFrz false) .None GeneralBorrowFreshChild.inside true rfl rfl rfl rfl rfl start amount nonzero afterBounds
    have outside : index∉tree.roots.toList := by
      intro member
      obtain ⟨node,present,_⟩ := afterRuntime.formed.rootNodes index member
      rw [vacant] at present
      contradiction
    have unique : tree.roots.toList.Nodup := by rw [contract.roots];exact distinct
    have appended : (tree.roots.push index).toList.Nodup := by
      rw [Array.toList_push]
      apply List.nodup_append.mpr
      refine ⟨unique,by simp,?_⟩
      intro query member other single equal
      have same : other=index := by simpa using single
      subst other
      subst query
      exact outside member
    simp only [CurrentCallSpatialEntryRead.output,CurrentCallSpatialRows.provenance,value]
    rw [exactCtor]
    exact appended

/-- Source-only installed cover, actual scoped argument copy, and full post-source State. -/
theorem invoke (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (ctx : ActualReferenceContext.Context options remaining span)
    (before : Before) (tracker : MachineHooks.BorrowState) (cover : CurrentCallSpatialCover.Context before)
    (offset : Nat) (len : UInt64) (role : RoleCover before tracker cover .mut offset len.toNat)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (state : DuplicatePrefixRuntimeInput.State before tracker)
    (highwater : ∀row∈before.memory.live.toList,GeneralBorrowForestTagHighWater.Below row.2.allocation.extra
      tracker.global.protectedTags tracker.global.nextPointerTag)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup)
    (short : role.backing.allocation.extra.nodes.size<65536)
    (nodeRoom : role.backing.allocation.extra.nodes.size+1≤4294967295)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState)
    (frameBorrow : frame.extra.borrowTracker=some borrowFrame)
    (binding : CandidateCallBindings.WindowBinding before role.family.value role.backing.id offset len.toNat)
    (positive : 0<len.toNat) (signedFits : len.toNat<9223372036854775808)
    (room : tracker.global.nextPointerTag.value<18446744073709551615) (race : before.dataRace=none)
    (nullComparator : ProjectionMetadataFacts.NullComparator) (dynamicFuel validationFuel : Nat)
    (fuelEq : options.place.dynamicFuel=dynamicFuel+1) (validationEq : options.limits.validation=validationFuel+1)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame before)).metadata=PreparedReflection.actual.runtime)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame before)))
    (debugOff : options.place.debugAssertions=false) (ghostOff : before.user.payload.ghost=false)
    (shallowMode : before.user.payload.validation=.Shallow)
    (localId : MIR.LocalId) (valid : localId<frame.locals.size) (old : Immediate Provenance)
    (live : frame.locals[localId].value=.live (.immediate old))
    (cached : frame.locals[localId].layout=some ActualReferenceMetadata.reference) (noClocks : frame.extra.dataRace=none) :
    let output := CurrentCallSpatialEntryRead.output role borrowFrame room (UInt64.ofNat offset) len
    ∃(entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (doneFrame : CompilerFrameContext.ActualFrame) (child : UniIndex)
      (installed : CellResources role (copiedMachine role borrowFrame room (UInt64.ofNat offset) len entry)
        ⟨output.global,tracker.retagMode⟩ output.child.tree output.tag child),
      before.memory.live.find? (fun row=>row.1==role.backing.id)=some (role.backing.id,entry) ∧
      entry.allocation=role.backing.allocation ∧
      MachineHooks.withRetagMode .FnEntry
        ((ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
          ⟨.immediate (value options remaining span role.family.value len).imm,ActualReferenceMetadata.reference⟩
          (LocalPlaces.localRuntimePlace frames.size frame localId ActualReferenceMetadata.reference).stackView)
        (Storage.withCurrent frames frame before)=
        .ok () (Storage.withCurrent frames doneFrame (copiedMachine role borrowFrame room (UInt64.ofNat offset) len entry)) ∧
      output.child.tree.indexOfTag output.tag=some child ∧
      doneFrame.extra.borrowTracker=some output.frame ∧ doneFrame.returnPlace=frame.returnPlace ∧
      doneFrame.returnContinuation=frame.returnContinuation ∧doneFrame.body=frame.body ∧doneFrame.bodyIdentity=frame.bodyIdentity ∧
      doneFrame.functionInstance=frame.functionInstance ∧doneFrame.location=frame.location ∧
      DuplicatePrefixRuntimeInput.State (copiedMachine role borrowFrame room (UInt64.ofNat offset) len entry) ⟨output.global,tracker.retagMode⟩ ∧
      (∀row∈(copiedMachine role borrowFrame room (UInt64.ofNat offset) len entry).memory.live.toList,
        GeneralBorrowForestTagHighWater.Below row.2.allocation.extra output.global.protectedTags output.global.nextPointerTag) ∧
      ∃(current : Present (ActualWorld (copiedMachine role borrowFrame room (UInt64.ofNat offset) len entry)) role.backing.id
          (role.backing.allocation.setExtra output.child.tree))
        (view : RoleCover (copiedMachine role borrowFrame room (UInt64.ofNat offset) len entry) ⟨output.global,tracker.retagMode⟩
          (CurrentCallSpatialSourceCover.context role current (updates role rfl installed)) .mut offset len.toNat),
        view.family=childFamily role output.tag ∧view.backing=CurrentCallSpatialSourceCover.backing role current (updates role rfl installed) := by
  have worldIds : ((ActualWorld before).toList.map Prod.fst).Nodup := by
    simpa only [ActualWorld,Array.toList_map,List.map_map,Function.comp_def] using state.allocationIds
  obtain ⟨entry,child,sourceLive,allocation,actual,tag,global,outputFrame,lookup,readDone,childDone,afterRuntime,capacity,growth,oldRoots,oldFields,node,typed,copied,cellModels⟩ :=
    CurrentCallSpatialTypedSourceCopy.invoke options limits remaining span ctx before tracker cover offset len role runtime worldIds distinct short nodeRoom
      frames frame borrowFrame state.enabled frameBorrow binding positive signedFits room race nullComparator dynamicFuel validationFuel
      fuelEq validationEq metadata origins debugOff ghostOff shallowMode localId valid old live cached noClocks
  obtain ⟨checked,copy,scopedCopy,tracked,postLive,frameBorrowed,frameSize,localValue,ghost,types,addresses,threads,dataRace⟩ := copied
  let output := CurrentCallSpatialEntryRead.output role borrowFrame room (UInt64.ofNat offset) len
  let copied := copiedFrame options remaining span frame localId valid role.family.value len
  let validCopied : localId<copied.locals.size := by simpa only [copied,copiedFrame,Array.size_set] using valid
  let doneFrame := writtenFrame options remaining span copied borrowFrame localId validCopied role.family.value len role.backing.id tracker.global.nextPointerTag
  let post := copiedMachine role borrowFrame room (UInt64.ofNat offset) len entry
  let next : MachineHooks.BorrowState := ⟨output.global,tracker.retagMode⟩
  obtain ⟨physicalEntry,base,physicalLive,address,length,addressFits,sourceBounds,addressEq,nonnull,provenance⟩ := binding
  have same : physicalEntry=entry := (Prod.mk.inj (Option.some.inj (physicalLive.symm.trans sourceLive))).2
  subst physicalEntry
  have offsetFits : offset<2^64 := by omega
  have startEq : (UInt64.ofNat offset).toNat=offset := by simp only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt offsetFits]
  have treeLength := state.treeLength (role.backing.id,entry) (Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some sourceLive))
  have bounds : (UInt64.ofNat offset).toNat+len.toNat≤role.backing.allocation.extra.locations.size.bytes.toNat := by
    rw [startEq,←allocation,treeLength,←length]
    exact sourceBounds
  have nonzero : len≠0 := by intro zero;rw [zero] at positive;cases positive
  have afterDistinct := roots role (by rfl) runtime distinct short nodeRoom borrowFrame room (UInt64.ofNat offset) len startEq rfl nonzero bounds
  have keys := CurrentCallSpatialEntryConstructor.key_origin role (by rfl) runtime distinct short nodeRoom borrowFrame room (UInt64.ofNat offset) len startEq rfl nonzero bounds
  have keyOrigin : ∀key index,(key,index)∈output.child.tree.tagMapping.mapping → key=tracker.global.nextPointerTag ∨
      ∃oldIndex,(key,oldIndex)∈entry.allocation.extra.tagMapping.mapping := by
    rw [allocation]
    exact keys
  have capacityEntry : output.child.tree.locations.size=entry.allocation.extra.locations.size := by rw [allocation];exact capacity
  obtain ⟨postState,postHighwater⟩ := CurrentCallSourceInstallState.install before post tracker next state highwater role.backing.id entry sourceLive
    borrowFrame room global output.child.tree afterRuntime afterDistinct capacityEntry keyOrigin rfl rfl
  obtain ⟨resChild,resLookup,installed⟩ := CurrentCallSpatialSourceInstall.copied_resources role rfl runtime distinct short nodeRoom borrowFrame room
    (UInt64.ofNat offset) len startEq rfl nonzero bounds entry allocation
  have sameChild : resChild=child := Option.some.inj (resLookup.symm.trans lookup)
  subst resChild
  have current := copied_present role borrowFrame room (UInt64.ofNat offset) len entry allocation
  exact ⟨entry,doneFrame,child,installed,sourceLive,allocation,scopedCopy,lookup,frameBorrowed,rfl,rfl,rfl,rfl,rfl,rfl,
    postState,postHighwater,current,sourceCover role rfl current installed,rfl,rfl⟩

end
end DuplicatePrefix.CurrentCallSpatialSourceState
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallSpatialSourceState" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved spatial source State dependency {dependency}"
