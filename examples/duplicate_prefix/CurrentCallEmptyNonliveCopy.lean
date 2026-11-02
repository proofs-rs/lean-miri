import duplicate_prefix.CurrentCallEmptyProtocolControl
import duplicate_prefix.ConcreteEmptyReferenceArgumentCopy
import duplicate_prefix.S03NonliveEmptyMetadata
namespace DuplicatePrefix.CurrentCallEmptyNonliveCopy
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateCurrentJointCall CanonicalConfigFacts ActualReferenceContext RootFrameData EmptyRootArguments
open TypedBorrowSteps
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- All metadata-backed absent targets share this SAME actual source-copy
producer. Function/va-list/nondata/dead are supplied by the ordinary classifier;
none needs a source tree, grant, family, permission or mapped parent. -/
theorem copy (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (before : Before) (tracker : MachineHooks.BorrowState)
    (model : DuplicatePrefixCallModel.Model options remaining span before)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins before.user.payload.payload.user.types)
    (frames : Array CompilerFrameContext.ActualFrame) (root : RootFrame) (borrow : FrameState)
    (frameBorrow : root.frame.extra.borrowTracker=some borrow)
    (id : AllocId) (parentTag : BorTag) (base offset : UInt64) (nonzero : base+offset≠0)
    (cached : before.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩)
    (metadata : DuplicatePrefixEmptyReferenceInput.Metadata before.memory id (some parentTag))
    (absent : before.memory.live.find? (fun row=>row.1==id)=none)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (dynamicFuel fuel : Nat) (dynamicEq : options.place.dynamicFuel=dynamicFuel+1)
    (fuelEq : options.limits.validation=fuel+1) :
    let input:=(RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm
    let updated:=(RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm
    let sourceFrame:=borrow.addProtector id tracker.global.nextPointerTag
    ∃post : Before,
      (ExecutionMachine.callHooks (config options (remaining+1) span) limits).copyAllowTransmute ()
        ⟨.immediate input,ActualReferenceMetadata.reference⟩
        (LocalPlaces.localRuntimePlace frames.size (firstLive root).frame 1 ActualReferenceMetadata.reference).stackView
        (Storage.withCurrent frames (firstLive root).frame (ScopedFrame.entered before tracker .FnEntry))=
        .ok () (Storage.withCurrent frames (CurrentCallEmptyProtocolControl.sourceRoot root updated sourceFrame).frame post) ∧
      post.memory=before.memory ∧post.user=before.user ∧post.threads=before.threads ∧post.dataRace=before.dataRace ∧
      post.borrowTracker=some ⟨(GeneralBorrowFnEntryRegistration.registered tracker.global borrow id fresh).1,.FnEntry⟩ := by
  dsimp only
  let input:=(RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm
  let updated:=(RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm
  let copied:=ConcreteEmptyReferenceArgumentCopy.copiedFrame (firstLive root).frame 1 input ((firstLive root).valid i1)
  let entered:=ScopedFrame.entered before tracker .FnEntry
  let afterFrame:=registeredFrame copied borrow id tracker.global.nextPointerTag
  let afterMachine:=(ActualConcreteEmptyReference.nonliveRetagState frames copied entered borrow tracker.global fresh id).machine
  let post:={afterMachine with user:={afterMachine.user with payload:={afterMachine.user.payload with ghost:=false}}}
  have live1 : ((firstLive root).frame.locals[1]'((firstLive root).valid i1)).value=.live (.immediate .uninit) := by
    simp only [firstLive,live,write,Array.getElem_set_self,i1]
  have cache1 : ((firstLive root).frame.locals[1]'((firstLive root).valid i1)).layout=some ActualReferenceMetadata.reference := by
    simp only [firstLive,firstCache,live,write,cache,atSpan,LocalOperands.cachedLayoutFrame,Array.getElem_set_self,i1]
  obtain ⟨info,known,notLive⟩:=S03NonliveEmptyMetadata.known before.memory id (some parentTag) metadata absent
  have actual:=ConcreteEmptyReferenceArgumentCopy.copy_nonlive_argument options limits remaining span ctx model.debugOff model.nullComparator
    dynamicFuel fuel dynamicEq fuelEq id parentTag tracker.global base offset nonzero frames (firstLive root).frame entered 1
    ((firstLive root).valid i1) .uninit live1 cache1 (firstLive root).noClocks model.ghostOff model.shallow cached borrow frameBorrow rfl fresh
    info known notLive model.metadata (DuplicatePrefixTypeCacheOrigins.slice_not_constructed _ model.metadata origins)
    afterFrame afterMachine rfl rfl rfl rfl (LocalPlaces.localRuntimePlace frames.size (firstLive root).frame 1 ActualReferenceMetadata.reference).stackView rfl
  have postValid : 1<afterFrame.locals.size := by
    simpa [afterFrame,registeredFrame,TypedRetagEntry.frameWithBorrow,copied,ConcreteEmptyReferenceArgumentCopy.copiedFrame,i1] using (firstLive root).valid i1
  have frameEq : {afterFrame with locals:=(afterFrame.locals.set 1
      {value:=.live (.immediate updated),layout:=(afterFrame.locals[1]'postValid).layout} postValid)}=
      (CurrentCallEmptyProtocolControl.sourceRoot root updated (borrow.addProtector id tracker.global.nextPointerTag)).frame := by
    simp [afterFrame,registeredFrame,TypedRetagEntry.frameWithBorrow,copied,ConcreteEmptyReferenceArgumentCopy.copiedFrame,
      CurrentCallEmptyProtocolControl.sourceRoot,write,i1]
  have userEq : post.user=before.user := by
    change {before.user with payload:={before.user.payload with ghost:=false}}=before.user
    rw [←model.ghostOff]
  refine ⟨post,?_,rfl,userEq,rfl,rfl,rfl⟩
  change _=EStateM.Result.ok () (Storage.withCurrent frames {afterFrame with locals:=(afterFrame.locals.set 1
    {value:=.live (.immediate updated),layout:=(afterFrame.locals[1]'postValid).layout} postValid)} post) at actual
  rw [frameEq] at actual
  exact actual
end
end DuplicatePrefix.CurrentCallEmptyNonliveCopy
