import duplicate_prefix.TypedRetagSharedNonFreezePolicy
import duplicate_prefix.WildcardGeneralHitReborrow
import duplicate_prefix.GeneralBorrowGcVacantClean
namespace DuplicatePrefix.S05ZeroSizedSharedNonFreezeRetag
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Input Miri.Interpreter
open TypedRetagSharedNonFreezePolicy
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- Thin reference representation for a general zero-sized pointee. No claim
is made that the fixed duplicate_prefix catalog contains such a shared type. -/
def value (target : TargetDataLayout) (pointer : Pointer Provenance) (reference : LocalLayout) : RvalueImmTy Provenance :=
  ⟨.scalar (Scalar.fromPointer target pointer),reference⟩
def place (pointer : Pointer Provenance) (pointee : LocalLayout) : MPlaceTy Provenance :=
  ⟨⟨pointer.withOptionalProvenance,.none,none⟩,pointee⟩
def index (tree : BorrowTree) : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
def resultTree (tree : BorrowTree) (tag : BorTag) : BorrowTree :=
  WildcardHitZeroConstructor.installed tree
    ⟨tree.tagMapping.mapping.push (tag,index tree),tree.tagMapping.deassigned⟩ (index tree) tag .Cell .Write

/-- Real zero-length wildcard insertion completes without parent access and
retains the original allocation locations. Its stored default is lazy Cell. -/
theorem constructor (tree : BorrowTree) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (noFree : tree.tagMapping.deassigned.back? = none)
    (fits : tree.tagMapping.mapping.size ≤ 4294967295) (offset : UInt64) :
    tree.newChild (Size.ofBytes offset) .wildcard tag (DedupRangeMap.new Size.ZERO location) .Cell false =
      ⟨resultTree tree tag,.ok ()⟩ := by
  exact WildcardHitZeroConstructor.append tree tag fresh noFree fits .Cell .Write false rfl rfl rfl location offset

/-- Clean vacant storage makes the new node's Cell default observable at EVERY
old allocation partition, although the typed borrow itself has size zero. -/
theorem cell_at_every_partition (tree : BorrowTree) (tag : BorTag)
    (aligned : tree.tagMapping.mapping.size = tree.nodes.data.size)
    (fits : tree.tagMapping.mapping.size ≤ 4294967295)
    (clean : GeneralBorrowGcVacantClean.VacantClean tree) :
    (resultTree tree tag).locations = tree.locations ∧
    (resultTree tree tag).nodeAt (index tree) = some (WildcardHitZeroConstructor.rootNode tag .Cell .Write) ∧
    ∀ position (valid : position < tree.locations.entries.size),
      (((resultTree tree tag).locations.entries[position]'valid).data.perms.get (index tree)).getD
        (WildcardHitZeroConstructor.rootNode tag .Cell .Write).defaultLocationState = location := by
  have atEnd : (index tree).toNat = tree.nodes.data.size := by
    simp only [index,UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega : tree.tagMapping.mapping.size < 2^32)]
    exact aligned
  have vacant : tree.nodes.get (index tree) = none := by
    simp only [UniValMap.get,atEnd,Array.getElem?_eq_none (Nat.le_refl _)]
  refine ⟨rfl,?_,?_⟩
  · exact GeneralBorrowFreshLocation.get_same _ _ _
  · intro position valid
    have absent := clean (index tree) vacant position valid
    change ((tree.locations.entries[position]'valid).data.perms.get (index tree)).getD _ = _
    rw [absent]
    rfl

private theorem construct_thin {K U C : Type} (access : ValidityMachine.Access K U)
    (prepared : CompilerFactAdapters.Prepared) (choice : C)
    (pointer : Pointer Provenance) (reference pointee : LocalLayout)
    (dereference : CompilerFacts.builtinDeref prepared.context reference.ty true = .ok (some pointee.ty))
    (pointeeLayout : CompilerFacts.layoutOf prepared.context pointee.ty = .ok pointee)
    (align : pointee.layout.align.abi = Align.ONE) :
    PointerPlaceMachine.fromImmediate access (CompilerExecutionProviders.pointerCompiler prepared) choice
      (value access.runtime.base pointer reference) = pure (place pointer pointee) := by
  funext state
  unfold PointerPlaceMachine.fromImmediate
  simp only [CompilerExecutionProviders.pointerCompiler,value]
  unfold_internal ".CompilerExecutionProviders.liftResult"
  unfold_internal ".CompilerExecutionProviders.query"
  simp only [dereference,pointeeLayout,Except.mapError,bind,EStateM.bind,pure,EStateM.pure,Immediate.toScalarAndMeta]
  unfold_internal ".PointerPlaceMachine.liftResult"
  simp only [CopyIntrinsic.pointer_scalar_roundtrip,Except.mapError,bind,EStateM.bind,pure,EStateM.pure]
  rw [RetagReferencePlace.with_metadata_align_one access _ _ pointee align]
  rfl

private theorem reconstruct_thin {K U : Type} [DecidableEq K]
    (access : ValidityMachine.Access K U) (h : TypedRetag.Hooks K (ValidityMachine.UserState U))
    (old : RvalueImmTy Provenance) (pointer : Pointer Provenance) (pointee : LocalLayout) :
    (TypedMachineBindings.retagHooks access h).reconstruct old (place pointer pointee) =
      pure (value access.runtime.base pointer old.layout) := by
  funext state
  simp [TypedMachineBindings.retagHooks,place,value,MemPlace.toRef,Immediate.newPointerWithMeta,
    ScalarPointers.from_some_pointer,Except.mapError,Except.bind,Except.pure,bind,EStateM.bind,pure,EStateM.pure]

/-- Actual typed Shared/Default pointer retag with explicit independent
compiler/type/layout leaves for a sized zero-sized non-Freeze pointee. The
pointer conversion, permission, tag allocation, zero reborrow and constructor
success are derived. No parent access, protector, Read/Write capability or
operation-success premise is supplied. This conditional lemma does not create
a fixed-metadata witness or prove reference validation/ordinary reachability. -/
theorem retag_pointer {K U C F A : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K (ValidityMachine.UserState U))
    (prepared : CompilerFactAdapters.Prepared) (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C)
    (sources : TypedRetagFields.SourceFields h prepared access projection vtable pointers choice)
    (budget : Nat) (reference pointee : LocalLayout)
    (shape : h.typeShape reference.ty = pure .reference)
    (pointeeQuery : h.referencePointee reference.ty = pure (pointee.ty,.Not))
    (unpinValue unsafeUnpinValue : Bool)
    (unpin : h.isUnpin pointee.ty = pure unpinValue)
    (unsafeUnpin : h.isUnsafeUnpin pointee.ty = pure unsafeUnpinValue)
    (nonfreeze : h.typeIsFreeze pointee.ty = pure false)
    (dereference : CompilerFacts.builtinDeref prepared.context reference.ty true = .ok (some pointee.ty))
    (pointeeLayout : CompilerFacts.layoutOf prepared.context pointee.ty = .ok pointee)
    (sized : pointee.layout.isSized = true) (zero : pointee.layout.size = Size.ZERO)
    (align : pointee.layout.align.abi = Align.ONE)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U)) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker)
    (tagRoom : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K) (address base : UInt64)
    (_nonnull : address ≠ 0)
    (geometry : WildcardGeneralHitReborrow.Geometry machine.user.addresses.intToPtrMap address base id entry.allocation.byteSize)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (mode : machine.user.addresses.provenanceMode ≠ .strict)
    (exposed : machine.user.addresses.exposed.contains id = true)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (fresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping tracker.global.nextPointerTag)
    (noFree : entry.allocation.extra.tagMapping.deassigned.back? = none)
    (fits : entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295)
    (globalKind : K) (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K (ValidityMachine.UserState U)))
    (extraWiring : pointers.ensureTreeExtra = GlobalAllocationMachine.ensure globalKind globals)
    (synchronize : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}}) :
    TypedRetag.retagPtrValue h budget (value access.runtime.base (Pointer.new .wildcard (Size.ofBytes address)) reference)
      reference.ty .Default (Storage.withCurrent frames frame machine) =
      .ok (some (value access.runtime.base (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes address)) reference))
        (Storage.withCurrent frames frame
          {(ReferenceBorrowDriver.allocatedMachine machine tracker tagRoom) with
            memory := RetagEntry.updatedMemory machine.memory id entry (resultTree entry.allocation.extra tracker.global.nextPointerTag)}) := by
  let before := Storage.withCurrent frames frame machine
  let allocated := ReferenceBorrowDriver.allocatedMachine machine tracker tagRoom
  let oldPointer := Pointer.new (.wildcard : Provenance) (Size.ofBytes address)
  let newPointer := Pointer.new (Provenance.concrete id tracker.global.nextPointerTag) (Size.ofBytes address)
  let oldPlace := place oldPointer pointee
  let after := Storage.withCurrent frames frame {allocated with memory := RetagEntry.updatedMemory machine.memory id entry (resultTree entry.allocation.extra tracker.global.nextPointerTag)}
  have check : h.checkPtrAccess oldPlace.mplace.ptr Size.ZERO (Storage.withCurrent frames frame allocated) =
      .ok () (Storage.withCurrent frames frame allocated) := by
    rw [sources.check]
    exact RetagPointerChecks.check_pointer_zero access _ _
  have resolve : h.resolveAllocation oldPlace.mplace.ptr (Storage.withCurrent frames frame allocated) =
      .ok (some ⟨id,Size.ofBytes (address-base),.wildcard⟩) (Storage.withCurrent frames frame allocated) := by
    rw [sources.resolve]
    exact WildcardGeneralHitReborrow.resolve pointers _ address base id entry geometry width mode exposed cached present
  have inside := inside_permissions h budget oldPlace Size.ZERO sources.precise nonfreeze
  have child := constructor entry.allocation.extra tracker.global.nextPointerTag fresh noFree fits (address-base)
  have reborrow := TypedBorrowSteps.unprotected_live_zero_of_steps h budget oldPlace frames frame allocated
    (ReferenceBorrowDriver.allocatedTracker tracker tagRoom) rfl id entry (address-base) .wildcard tracker.global.nextPointerTag location policy
    rfl check resolve (by rw [sources.log]) inside globalKind globals (sources.ensure.trans extraWiring) synchronize present
    (resultTree entry.allocation.extra tracker.global.nextPointerTag) child
  have sizing : h.sizeAndAlign oldPlace before = .ok (some (Size.ZERO,Align.ONE)) before := by
    rw [sources.sizing]
    cases fuel : projection.dynamicFuel <;> simp only [DynamicLayout.sizeAndAlignFromMeta,fuel,oldPlace,place,sized,zero,align,↓reduceIte,pure,EStateM.pure]
  have retag := TypedBorrowSteps.retag_place_at_of_reborrow h budget oldPlace policy Size.ZERO Align.ONE before after tracker enabled tagRoom id .wildcard rfl sizing reborrow
  have permission := new_permission_shared_nonfreeze h pointee.ty unpinValue unsafeUnpinValue unpin unsafeUnpin nonfreeze
  have construct : h.immPtrToMPlace (value access.runtime.base oldPointer reference) = pure oldPlace := by
    rw [sources.construct]
    exact construct_thin access prepared choice oldPointer reference pointee dereference pointeeLayout align
  have changed : TypedRetagGeneric.retaggedPlace oldPlace id tracker.global.nextPointerTag = place newPointer pointee := rfl
  have reconstruct : h.reconstruct (value access.runtime.base oldPointer reference)
      (TypedRetagGeneric.retaggedPlace oldPlace id tracker.global.nextPointerTag) = pure (value access.runtime.base newPointer reference) := by
    rw [sources.reconstruct,changed]
    exact reconstruct_thin access h _ newPointer pointee
  exact TypedBorrowSteps.reference_pointer_of_steps h budget _ _ oldPlace _ pointee.ty .Not .Default policy before after shape pointeeQuery
    (by change TypedRetag.newPermission h pointee.ty .Shared .Default before = _;exact congrFun permission before) construct retag reconstruct
end
end DuplicatePrefix.S05ZeroSizedSharedNonFreezeRetag
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05ZeroSizedSharedNonFreezeRetag." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved zero shared nonfreeze retag dependency {dependency}"
