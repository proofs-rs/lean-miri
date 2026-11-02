import duplicate_prefix.GenericSharedRejectedStages
import duplicate_prefix.GenericSharedLenAccepted
import duplicate_prefix.GeneralBorrowFreshSharedReleasedMetadata
namespace DuplicatePrefix.GenericSharedRejectedForm
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralRangeMapOrigins GeneralRangeMapState GenericSharedRejectedStages
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
noncomputable section

def value (s : GenericSharedRejectedInput.Base) :=
  (RetagReferencePlace.sliceValue (ActualReferenceContext.config s.options s.remaining s.span).access.runtime.base
    (Pointer.new (.concrete s.id s.tracker.global.nextPointerTag) (Size.ofBytes (s.base+s.offset))) s.len SharedReferenceMetadata.sharedLayout).imm

set_option autoImplicit false in
/-- Fields projected from the actual pre-guard shared/len endpoint, formed
inside the public runtime wrapper rather than supplied to its safety theorem. -/
structure Boundary (s : GenericSharedRejectedInput.Base) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (tree : BorrowTree) : Prop where
  tracked : machine.borrowTracker = some (ended_base s)
  present : machine.memory.live.find? (fun row => row.1 == s.id) = some (s.id,GeneralBorrowFreshSharedPop.withTree s.entry tree)
  owned : OwnedOn (GeneralBorrowRange.LocationOwned tree (ended_base s).global.protectedTags s.target .Write) s.offset (s.offset+s.len) tree.locations
  runtime : GenericSharedLenAccepted.RuntimeFacts s.options s.remaining s.span s.machine machine
  facts : GenericSharedLenAccepted.PreGuardFrameFacts s.frame frame s.len (value s)
  active : GeneralBorrowFreshActiveWithin.ActiveWithin tree s.target .Write s.offset (s.offset+s.len)
  well : tree.locations.WellFormed
  memory : machine.memory = RetagEntry.updatedMemory s.machine.memory s.id s.entry tree

set_option autoImplicit false in
/-- Only the graph and old-parent facts used by root cleanup; allocator policy
is deliberately absent, so append and arbitrary free-pool prefixes share it. -/
structure Metadata (s : GenericSharedRejectedInput.Base) (tree : BorrowTree) where
  certificates : GeneralBorrowFreshMetadataChildAttach.Certificates tree
  roots : tree.roots = s.entry.allocation.extra.roots
  nodeFits : tree.nodes.data.size ≤ 4294967296
  node : ∃ node, tree.nodeAt s.target = some node ∧ node.tag = s.first.parentNode.tag ∧ node.isExposed = s.first.parentNode.isExposed
  tagPresent : tree.indexOfTag s.first.parentTag = some s.target

/-- Form a data-only arbitrary-buffer false physical-return input from the
actual len endpoint. The public wrapper obtains every boundary projection and
metadata witness from initial data and successful source proofs. -/
def form_data (s : GenericSharedRejectedInput.Base) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (tree : BorrowTree)
    (b : Boundary s frame machine tree)
    (metadata : Metadata s tree) :
    Σ' ready : GenericRootRejectedPhysical.Input,
      ready.before=frame ∧ ready.machine=machine ∧
      PreparedContracts.actualConfig ready.options () (ready.remaining+1) ready.span =
        PreparedContracts.actualConfig s.options () (s.remaining+1) s.span ∧ ready.limits=s.limits := by
  let node := Classical.choose metadata.node
  have nodeFacts := Classical.choose_spec metadata.node
  let release : GenericRootPhysicalReturnPlan.Input machine.memory (ended_base s).global.protectedTags := by
    refine {
      id := s.id,tag := s.first.parentTag,buffer := GeneralBorrowFreshSharedPop.withTree s.entry tree,present := b.present
      anchor := s.target,root := s.first.root,kind := .Write,lower := s.offset,upper := s.offset+s.len,positive := s.rangePositive
      fits := metadata.nodeFits,depth := metadata.certificates.depth,children := metadata.certificates.children,node := node
      anchorPresent := nodeFacts.1,notExposed := nodeFacts.2.2.trans s.targetNotExposed,roots := metadata.roots.trans s.first.roots
      covered := metadata.certificates.covered,tagPresent := metadata.tagPresent
      active := GeneralBorrowFreshActiveWithin.active_on tree s.target .Write s.offset (s.offset+s.len) b.well b.active,owned := b.owned
      slotId := s.slotId,separate := s.separate,slot := s.slot,slotPresent := ?_,slotRoot := s.slotRoot,slotChild := s.slotChild
      slotTree := s.slotTree,slotRootFree := ?_,slotChildHeld := ?_,slotDistinct := s.slotDistinct }
    · rw [b.memory]
      exact StackPopRelease.lookup_commit_other s.machine.memory s.id s.slotId s.entry s.slot tree s.separate s.slotPresent
    · rw [contains_base s s.slotRoot (Ne.symm s.slotRootDifferent2)]
      exact s.slotRootFree
    · rw [contains_base s s.slotChild s.slotChildDifferent2]
      exact s.slotChildHeld
  have valid (i : Fin 25) : i.val < frame.locals.size := by rw [b.facts.size];exact i.isLt
  have validBefore (i : Fin 25) : i.val < s.frame.locals.size := by rw [s.size];exact i.isLt
  have same (i : Fin 25) (n11 : i.val ≠ 11) (n12 : i.val ≠ 12) :
      (frame.locals[i.val]'(valid i)) = (s.frame.locals[i.val]'(validBefore i)) :=
    Option.some.inj ((Array.getElem?_eq_getElem (valid i)).symm.trans
      ((b.facts.kept i.val n11 n12).trans (Array.getElem?_eq_getElem (validBefore i))))
  have len11 : (frame.locals[11]'(valid ⟨11,by decide⟩)) =
      ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 s.len)))),some RootCompilerFacts.usizeLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem (valid ⟨11,by decide⟩)).symm.trans b.facts.len11)
  have expr12 : (frame.locals[12]'(valid ⟨12,by decide⟩)) =
      ⟨.live (.immediate (value s)),some SharedReferenceMetadata.sharedLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem (valid ⟨12,by decide⟩)).symm.trans b.facts.value12)
  let thread := Classical.choose b.runtime.active
  have threadFacts := Classical.choose_spec b.runtime.active
  let ready : GenericRootRejectedPhysical.Input := by
    refine {
      options := s.options,limits := s.limits,remaining := s.remaining,span := s.span,source := s.source,fuel := s.validityFuel
      debugOff := s.debug,validationFuel := s.validationEq,context := s.context,validationContext := s.validationContext
      accessEq := s.accessEq,validationWidth := s.validationWidth,validationRuntimeSize := s.validationRuntimeSize,sameRuntime := s.sameRuntime
      width := s.width,runtimeWidth := s.runtimeWidth,runtimeSize := s.runtimeSize,outerAccessEq := s.outerAccessEq,before := frame
      len := s.len,count := s.count,rejected := s.rejected,frameSize := b.facts.size,location := b.facts.location,all := b.facts.immediate,temp12 := value s
      live12 := congrArg LocalState.value expr12,live13 := ?_,cache13 := ?_,live0 := ?_,cache0 := ?_,live7 := ?_,live8 := ?_,cache8 := ?_
      live9 := ?_,cache9 := ?_,live10 := ?_,cache10 := ?_,live11 := congrArg LocalState.value len11,cache11 := congrArg LocalState.layout len11
      body := b.facts.body.trans s.body,identity := b.facts.identity.trans s.identity,callee := b.facts.callee.trans s.callee
      noLocalClocks := (congrArg (fun extra => extra.dataRace) b.facts.extra).trans s.frameRace
      continuation := b.facts.continuation.trans s.continuation,varargs := b.facts.varargs.trans s.varargs,machine := machine,tracker := ended_base s
      tracked := b.tracked,defaultMode := (ended_fields_base s).2.trans s.defaultMode,noClocks := b.runtime.race,noBackend := b.runtime.backend
      ghost := b.runtime.ghost,shallow := b.runtime.shallow,unchecked := b.runtime.unchecked,noGc := b.runtime.noGc,fixed := b.runtime.fixed
      thread := thread,active := threadFacts.1,release := release,frameTracked := ?_
      slotSize := s.slotSize,slotStorage := s.slotStorage,slotMask := s.slotMask,slotProvenance := s.slotProvenance,slotMutable := s.slotMutable
      place := s.place,layout := s.layout,slotBase := s.slotBase,slotPointer := s.slotPointer,aligned := s.aligned,fits := s.fits,cached := ?_,extras := ?_
      destination := (congrArg (fun place => place.toRuntimePlace) b.facts.destination).trans s.destination }
    · rw [same ⟨13,by decide⟩ (by decide) (by decide)];exact s.live13
    · rw [same ⟨13,by decide⟩ (by decide) (by decide)];exact s.cache13
    · rw [same ⟨0,by decide⟩ (by decide) (by decide)];exact s.live0
    · rw [same ⟨0,by decide⟩ (by decide) (by decide)];exact s.cache0
    · rw [same ⟨7,by decide⟩ (by decide) (by decide)];exact s.live7
    · rw [same ⟨8,by decide⟩ (by decide) (by decide)];exact s.live8
    · rw [same ⟨8,by decide⟩ (by decide) (by decide)];exact s.cache8
    · rw [same ⟨9,by decide⟩ (by decide) (by decide)];exact s.live9
    · rw [same ⟨9,by decide⟩ (by decide) (by decide)];exact s.cache9
    · rw [same ⟨10,by decide⟩ (by decide) (by decide)];exact s.live10
    · rw [same ⟨10,by decide⟩ (by decide) (by decide)];exact s.cache10
    · change frame.extra.borrowTracker = _
      rw [b.facts.extra]
      exact s.frameTracked
    · rw [b.runtime.addresses]
      exact s.slotCached
    · change machine.user.payload.payload.user.runtime.extras.allocations.find? _ = _
      rw [b.runtime.extras]
      exact s.extras
  exact ⟨ready,rfl,rfl,rfl,rfl⟩
/-- Compatibility wrapper for the existing append-only metadata boundary. -/
def form (s : GenericSharedRejectedInput.Input) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (tree : BorrowTree)
    (b : Boundary s frame machine tree)
    (metadata : GeneralBorrowFreshSharedReleasedMetadata.Output s.entry.allocation.extra tree s.target s.first.parentNode s.first.parentTag) :
    Σ' ready : GenericRootRejectedPhysical.Input,
      ready.before=frame ∧ ready.machine=machine ∧
      PreparedContracts.actualConfig ready.options () (ready.remaining+1) ready.span =
        PreparedContracts.actualConfig s.options () (s.remaining+1) s.span ∧ ready.limits=s.limits :=
  form_data s frame machine tree b
    ⟨metadata.certificates,metadata.roots,metadata.nodeFits,metadata.node,metadata.tagPresent⟩

end
end DuplicatePrefix.GenericSharedRejectedForm
