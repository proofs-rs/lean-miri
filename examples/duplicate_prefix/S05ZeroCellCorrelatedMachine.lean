import duplicate_prefix.S05ZeroCellCorrelatedTyped
import duplicate_prefix.S05ZeroCellCorrelatedWrite

/-! Actual auxiliary-context operations in one stateful computation, with
source-derived success lemmas for its initial stages. A successful full prefix
and ordinary-input coverage remain separate obligations. No compiler metadata
is replaced while the computation is running. -/
namespace DuplicatePrefix.S05ZeroCellCorrelatedMachine
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Input Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open S05ZeroCellTypedGeneratedPrefix
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

def exposureInput (stage : Bool) : BorrowTree := if stage then v.tree else seed
def exposureOutput (stage : Bool) : BorrowTree := if stage then exposedV.tree else exposed.tree
def exposureTag (stage : Bool) : BorTag := if stage then tag 5 else tag 1

def exposedAddresses (addresses : AllocAddresses.GlobalAddressState) (id : AllocId) :
    AllocAddresses.GlobalAddressState :=
  {addresses with exposed := if addresses.exposed.contains id then addresses.exposed else addresses.exposed.push id}

theorem expose_from_fields {K U : Type} [DecidableEq K]
    (pointers : PointerMachine.Hooks K U)
    (state : PointerMachine.State K U)
    (tracker : MachineHooks.BorrowState)
    (enabled : state.machine.borrowTracker = some tracker)
    (protections : tracker.global.protectedTags = {})
    (mode : state.machine.user.addresses.provenanceMode = .permissive)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (stage : Bool) (tree : entry.allocation.extra = exposureInput stage)
    (globalKind : K) (globals : GlobalAllocationHooks Provenance BorrowTree K
      (PlaceMachine.AccessState K (PointerMachine.User U)))
    (extraWiring : pointers.ensureTreeExtra = GlobalAllocationMachine.ensure globalKind globals)
    (synchronize : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}}) :
    PointerMachine.exposeProvenance pointers (.concrete id (exposureTag stage)) state =
      .ok () {state with machine := {state.machine with
        user := {state.machine.user with addresses := exposedAddresses state.machine.user.addresses id}
        memory := RetagEntry.updatedMemory state.machine.memory id entry (exposureOutput stage)}} := by
  have live : state.machine.memory.isAllocLive id = true := by
    unfold MemoryState.isAllocLive
    rw [MemoryCopyBridge.live_any_of_present _ id entry present]
    rfl
  have info := MemoryCopyBridge.live_alloc_info state.machine.memory id entry present
  let addresses := exposedAddresses state.machine.user.addresses id
  let next : PointerMachine.State K U := {state with machine := {state.machine with user := {state.machine.user with addresses}}}
  have ensure := RetagPointerChecks.ensure_tree_live globalKind globals synchronize next id entry present
  have complete : entry.allocation.extra.exposeTag tracker.global.protectedTags (exposureTag stage) =
      ⟨exposureOutput stage,.ok ()⟩ := by
    rw [tree,protections]
    cases stage <;> cbv
  have stored := MemoryCopyBridge.set_live_exact state.machine.memory id entry
    (entry.allocation.setExtra (exposureOutput stage)) present
  unfold PointerMachine.exposeProvenance
  unfold_internal ".PointerMachine.addresses"
  unfold_internal ".PointerMachine.finish"
  unfold_internal ".PointerMachine.setAddresses"
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    mode, beq_iff_eq, reduceCtorEq, Bool.false_eq_true, ↓reduceIte, live, Bool.not_true,
    enabled, Option.isSome_some, info]
  simp only [AllocAddresses.GlobalAddressState.exposeProvenance, mode, beq_iff_eq, reduceCtorEq, Bool.false_eq_true, ↓reduceIte]
  simp only [reduceCtorEq, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
    bind, EStateM.bind, pure, EStateM.pure]
  simp only [Id.run, bind, EStateM.bind, pure, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, enabled, info, Option.isSome_some, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rw [extraWiring]
  simp only [next, addresses, exposedAddresses,mode,enabled] at ensure
  erw [ensure]
  simp only [bind, EStateM.bind, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, enabled, info, present, complete, stored]
  simp only [RetagEntry.updatedMemory, exposedAddresses, mode, enabled]

theorem expose_then_cell_from_fields {K U C F A : Type} [DecidableEq K]
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
    (mode : machine.user.addresses.provenanceMode = .permissive)
    (protections : tracker.global.protectedTags = {})
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (tree : entry.allocation.extra = seed)
    (next : tracker.global.nextPointerTag = tag 2)
    (globalKind : K) (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K (ValidityMachine.UserState U)))
    (extraWiring : pointers.ensureTreeExtra = GlobalAllocationMachine.ensure globalKind globals)
    (synchronize : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}}) :
    let exposedMachine := {machine with
      user := {machine.user with addresses := exposedAddresses machine.user.addresses id}
      memory := RetagEntry.updatedMemory machine.memory id entry exposed.tree}
    let exposedEntry := {entry with allocation := entry.allocation.setExtra exposed.tree}
    (do
      PointerMachine.exposeProvenance pointers (.concrete id (tag 1))
      TypedRetag.retagPtrValue h budget
        (S05ZeroSizedSharedNonFreezeRetag.value access.runtime.base
          (Pointer.new .wildcard (Size.ofBytes address)) reference)
        reference.ty .Default) (Storage.withCurrent frames frame machine) =
      .ok (some (S05ZeroSizedSharedNonFreezeRetag.value access.runtime.base
        (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes address)) reference))
        (Storage.withCurrent frames frame
          {ReferenceBorrowDriver.allocatedMachine exposedMachine tracker tagRoom with
            memory := RetagEntry.updatedMemory exposedMachine.memory id exposedEntry
              (S05ZeroSizedSharedNonFreezeRetag.resultTree exposedEntry.allocation.extra tracker.global.nextPointerTag)}) := by
  let exposedMachine := {machine with
    user := {machine.user with addresses := exposedAddresses machine.user.addresses id}
    memory := RetagEntry.updatedMemory machine.memory id entry exposed.tree}
  let exposedEntry := {entry with allocation := entry.allocation.setExtra exposed.tree}
  have exposure := expose_from_fields pointers (Storage.withCurrent frames frame machine)
    tracker enabled protections mode id entry present false tree globalKind globals extraWiring synchronize
  have exposedNow : exposedMachine.user.addresses.exposed.contains id = true := by
    dsimp only [exposedMachine, exposedAddresses]
    split
    · assumption
    · simp
  have nowPresent : exposedMachine.memory.live.find? (fun row => row.1 == id) = some (id,exposedEntry) :=
    MemoryCopyBridge.live_lookup_replaced machine.memory id exposedEntry
  have cell := S05ZeroCellCorrelatedTyped.cell_pointer_from_fields h prepared access projection vtable pointers choice sources
    budget reference pointee shape pointeeQuery unpinValue unsafeUnpinValue unpin unsafeUnpin nonfreeze
    dereference pointeeLayout sized zero align frames frame exposedMachine tracker enabled tagRoom id exposedEntry address base
    _nonnull geometry width (by simp [exposedMachine,exposedAddresses,mode]) exposedNow cached nowPresent
    false rfl next globalKind globals extraWiring synchronize
  change _ = _
  simp only [bind, EStateM.bind]
  simp only [exposureTag, exposureInput, exposureOutput, Bool.false_eq_true, ↓reduceIte] at exposure
  erw [exposure]
  exact cell

/-- Only layouts and operation configuration, with no operation-success fields.
The same typed hooks and place configuration are used throughout the prefix. -/
structure Config (K U : Type) where
  typed : TypedRetag.Hooks K (ValidityMachine.UserState U)
  pointers : PointerMachine.Hooks K (ValidityMachine.Control U)
  memory : PlaceMachine.AccessConfig K (ValidityMachine.UserState U)
  budget : Nat
  sharedReference : LocalLayout
  mutableReference : LocalLayout
  /-- A two-byte sized place reached through the original tag. -/
  original : MPlaceTy Provenance
  /-- An actual initialized two-byte immediate to write on each original access. -/
  writeValue : Immediate Provenance
  willValidate : MemoryOperandLayout → Bool

/-- Compiler-query and dictionary identities used at every stage. These
fields describe immutable metadata and source bindings, never runtime success. -/
structure RetagFacts {K U C F A : Type} [DecidableEq K]
    (config : Config K U) (prepared : CompilerFactAdapters.Prepared)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A) (choice : C) where
  sources : TypedRetagFields.SourceFields config.typed prepared config.memory projection vtable config.pointers choice
  cellLayout : LocalLayout
  sliceLayout : LocalLayout
  cellShape : config.typed.typeShape config.sharedReference.ty = pure .reference
  cellPointee : config.typed.referencePointee config.sharedReference.ty = pure (cellLayout.ty,.Not)
  cellUnpin : config.typed.isUnpin cellLayout.ty = pure true
  cellUnsafeUnpin : config.typed.isUnsafeUnpin cellLayout.ty = pure true
  cellNonfreeze : config.typed.typeIsFreeze cellLayout.ty = pure false
  cellDeref : CompilerFacts.builtinDeref prepared.context config.sharedReference.ty true = .ok (some cellLayout.ty)
  cellQuery : CompilerFacts.layoutOf prepared.context cellLayout.ty = .ok cellLayout
  cellSized : cellLayout.layout.isSized = true
  cellZero : cellLayout.layout.size = Size.ZERO
  cellAlign : cellLayout.layout.align.abi = Align.ONE
  sliceShape : config.typed.typeShape config.mutableReference.ty = pure .reference
  slicePointee : config.typed.referencePointee config.mutableReference.ty = pure (sliceLayout.ty,.Mut)
  sliceUnpin : config.typed.isUnpin sliceLayout.ty = pure true
  sliceUnsafeUnpin : config.typed.isUnsafeUnpin sliceLayout.ty = pure true
  sliceFreeze : config.typed.typeIsFreeze sliceLayout.ty = pure true
  sliceDeref : CompilerFacts.builtinDeref prepared.context config.mutableReference.ty true = .ok (some sliceLayout.ty)
  sliceQuery : CompilerFacts.layoutOf prepared.context sliceLayout.ty = .ok sliceLayout
  sliceAlign : sliceLayout.layout.align.abi = Align.ONE
  sliceMetadata : ∀ (pointer : Pointer Provenance) (len : UInt64), len = 0 ∨ len = 2 →
    TypedRetagEntry.SliceFacts projection choice (RetagReferencePlace.slicePlace pointer len sliceLayout) len
  pointerWiring : config.memory.resolvePointer = TypedMemoryProviders.resolvePointer config.pointers
  pointerWidth : config.pointers.arithmetic = ⟨Size.ofBytes 8⟩
  globalKind : K
  ensureWiring : config.pointers.ensureTreeExtra = GlobalAllocationMachine.ensure globalKind config.memory.globalHooks
  synchronize : config.memory.globalHooks.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}}

private def requireRetag {K U : Type} [DecidableEq K] (config : Config K U)
    (value : RvalueImmTy Provenance) :
    MachineHooks.M K (ValidityMachine.UserState U) (RvalueImmTy Provenance) := do
  let some value ← TypedRetag.retagPtrValue config.typed config.budget value value.layout.ty .Default
    | throw (.invalidProgram "correlated prefix: reference retag returned no value")
  return value

private def thin {K U : Type} (value : RvalueImmTy Provenance) :
    MachineHooks.M K (ValidityMachine.UserState U) (Scalar Provenance) := do
  let .scalar pointer := value.imm
    | throw (.invalidProgram "correlated prefix: shared reference is not a thin scalar")
  return pointer

private def data {K U : Type} (value : RvalueImmTy Provenance) :
    MachineHooks.M K (ValidityMachine.UserState U) (Scalar Provenance) := do
  let .scalarPair pointer _ := value.imm
    | throw (.invalidProgram "correlated prefix: slice reference is not a scalar pair")
  return pointer

/-- Reuse the returned data-pointer scalar, changing only the slice metadata.
In particular this does not recreate a hard-coded tag or allocation identity. -/
def slice (pointer : Scalar Provenance) (length : UInt64) (layout : LocalLayout) :
    RvalueImmTy Provenance :=
  ⟨.scalarPair pointer (Scalar.fromScalarInt (ScalarInt.ofUInt64 length)),layout⟩

private def exposeScalar {K U : Type} [DecidableEq K] (config : Config K U)
    (scalar : Scalar Provenance) : MachineHooks.M K (ValidityMachine.UserState U) Unit := do
  let pointer ← match scalar.toPointer config.memory.runtime.base with
    | .ok pointer => pure pointer
    | .error error => throw (.invalidProgram s!"correlated prefix pointer: {reprStr error}")
  let some provenance := pointer.provenance
    | throw (.invalidProgram "correlated prefix exposure has no provenance")
  PointerMachine.exposeProvenance config.pointers provenance

structure Output where
  /-- Copied out of the successful D retag, before the first original write. -/
  savedRawD : Scalar Provenance
  w : RvalueImmTy Provenance

/-- The first three operations, retaining the raw scalar copied from D. -/
def runToD {K U : Type} [DecidableEq K] (config : Config K U)
    (original : Provenance) (wildcard : Pointer Provenance) :
    MachineHooks.M K (ValidityMachine.UserState U) (Scalar Provenance) := do
  PointerMachine.exposeProvenance config.pointers original
  let a ← requireRetag config
    (S05ZeroSizedSharedNonFreezeRetag.value config.memory.runtime.base wildcard config.sharedReference)
  let aPointer ← thin a
  let d ← requireRetag config (slice aPointer 2 config.mutableReference)
  data d

def runFirstWrite {K U : Type} [DecidableEq K] (config : Config K U)
    (original : Provenance) (wildcard : Pointer Provenance) :
    MachineHooks.M K (ValidityMachine.UserState U) (Scalar Provenance) := do
  let savedRawD ← runToD config original wildcard
  PlaceMachine.writeMemory config.memory config.willValidate config.writeValue config.original
  return savedRawD

/-- Exact post-state descriptions. They do not stand for interpreter steps. -/
def withNext (tracker : MachineHooks.BorrowState) (next : BorTag) : MachineHooks.BorrowState :=
  {tracker with global := {tracker.global with nextPointerTag := next}}

def afterExposure {K U : Type}
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K) :
    MachineHooks.MachineState K (ValidityMachine.UserState U) :=
  {machine with
    user := {machine.user with addresses := exposedAddresses machine.user.addresses id}
    memory := RetagEntry.updatedMemory machine.memory id entry exposed.tree}

def afterRetag {K U : Type}
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (tracker : MachineHooks.BorrowState) (next : BorTag)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K) (tree : BorrowTree) :
    MachineHooks.MachineState K (ValidityMachine.UserState U) :=
  {machine with
    borrowTracker := some (withNext tracker next)
    memory := RetagEntry.updatedMemory machine.memory id entry tree}

theorem expose_a_d_from_fields {K U C F A : Type} [DecidableEq K]
    (config : Config K U) (prepared : CompilerFactAdapters.Prepared)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A) (choice : C)
    (facts : RetagFacts config prepared projection vtable choice)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker)
    (next : tracker.global.nextPointerTag = tag 2)
    (protections : tracker.global.protectedTags = {})
    (mode : machine.user.addresses.provenanceMode = .permissive)
    (noClocks : machine.dataRace = none)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K) (base : UInt64)
    (nonnull : base ≠ 0)
    (geometry : WildcardGeneralHitReborrow.Geometry machine.user.addresses.intToPtrMap base base id entry.allocation.byteSize)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (tree : entry.allocation.extra = seed)
    (bounds : (2 : UInt64).toNat ≤ entry.allocation.byteSize.bytes.toNat) :
    let exposedMachine := afterExposure machine id entry
    let exposedEntry := {entry with allocation := entry.allocation.setExtra exposed.tree}
    let machineA := afterRetag exposedMachine tracker (tag 3) id exposedEntry a.tree
    let entryA := {entry with allocation := entry.allocation.setExtra a.tree}
    let machineD := afterRetag machineA tracker (tag 4) id entryA d.tree
    runToD config (.concrete id (tag 1)) (Pointer.new .wildcard (Size.ofBytes base))
      (Storage.withCurrent frames frame machine) =
      .ok (Scalar.fromPointer config.memory.runtime.base
        (Pointer.new (.concrete id (tag 3)) (Size.ofBytes base)))
        (Storage.withCurrent frames frame machineD) := by
  let exposedMachine := afterExposure machine id entry
  let exposedEntry := {entry with allocation := entry.allocation.setExtra exposed.tree}
  let machineA := afterRetag exposedMachine tracker (tag 3) id exposedEntry a.tree
  let entryA := {entry with allocation := entry.allocation.setExtra a.tree}
  let trackerA := withNext tracker (tag 3)
  let machineD := afterRetag machineA tracker (tag 4) id entryA d.tree
  have room : tracker.global.nextPointerTag.value < 18446744073709551615 := by rw [next]; decide
  have roomA : trackerA.global.nextPointerTag.value < 18446744073709551615 := by
    change (3 : UInt64) < 18446744073709551615
    decide
  have exposure := expose_from_fields config.pointers (Storage.withCurrent frames frame machine)
    tracker enabled protections mode id entry present false tree facts.globalKind config.memory.globalHooks
    facts.ensureWiring facts.synchronize
  have exposedNow : exposedMachine.user.addresses.exposed.contains id = true := by
    dsimp only [exposedMachine, afterExposure, exposedAddresses]
    split
    · assumption
    · simp
  have exposedPresent : exposedMachine.memory.live.find? (fun row => row.1 == id) = some (id,exposedEntry) :=
    MemoryCopyBridge.live_lookup_replaced machine.memory id exposedEntry
  have cell := S05ZeroCellCorrelatedTyped.cell_pointer_from_fields config.typed prepared config.memory
    projection vtable config.pointers choice facts.sources config.budget config.sharedReference facts.cellLayout
    facts.cellShape facts.cellPointee true true facts.cellUnpin facts.cellUnsafeUnpin facts.cellNonfreeze
    facts.cellDeref facts.cellQuery facts.cellSized facts.cellZero facts.cellAlign frames frame exposedMachine
    tracker enabled room id exposedEntry base base nonnull geometry facts.pointerWidth
    (by simp [exposedMachine,afterExposure,exposedAddresses,mode]) exposedNow cached exposedPresent false rfl next
    facts.globalKind config.memory.globalHooks facts.ensureWiring facts.synchronize
  have cellTree : S05ZeroSizedSharedNonFreezeRetag.resultTree exposedEntry.allocation.extra tracker.global.nextPointerTag = a.tree := by
    rw [next]
    exact S05ZeroCellCorrelatedTyped.cell_result_tree false
  have allocated : ReferenceBorrowDriver.allocatedTracker tracker room = trackerA := by
    simp only [ReferenceBorrowDriver.allocatedTracker, TypedRetagEmpty.successorTag, next, trackerA,withNext]
    rfl
  rw [cellTree] at cell
  simp only [next,ReferenceBorrowDriver.allocatedMachine,allocated] at cell
  have aPresent : machineA.memory.live.find? (fun row => row.1 == id) = some (id,entryA) :=
    MemoryCopyBridge.live_lookup_replaced exposedMachine.memory id entryA
  let place := RetagReferencePlace.slicePlace
    (Pointer.new (.concrete id (tag 2)) (Size.ofBytes (base+0))) 2 facts.sliceLayout
  have mutableStep := S05ZeroCellCorrelatedTyped.mutable_pointer_from_fields config.typed prepared config.memory
    projection vtable config.pointers choice facts.sources config.budget place frames frame machineA trackerA rfl roomA
    id entryA base false rfl protections rfl facts.sliceFreeze rfl facts.pointerWiring facts.pointerWidth cached
    (by decide) (by simpa only [entryA,Allocation.setExtra,Allocation.mapExtra,Allocation.byteSize,UInt64.toNat_zero,Nat.zero_add] using bounds) facts.globalKind config.memory.globalHooks facts.ensureWiring facts.synchronize
    aPresent noClocks config.mutableReference facts.sliceShape facts.slicePointee facts.sliceUnpin facts.sliceUnsafeUnpin
    facts.sliceDeref facts.sliceQuery facts.sliceAlign rfl
    (facts.sliceMetadata _ 2 (Or.inr rfl))
  have allocatedA : ReferenceBorrowDriver.allocatedTracker trackerA roomA = withNext tracker (tag 4) := by rfl
  simp only [ReferenceBorrowDriver.allocatedMachine,allocatedA] at mutableStep
  unfold runToD requireRetag thin data
  simp only [bind,EStateM.bind]
  simp only [exposureTag,exposureOutput,Bool.false_eq_true,↓reduceIte] at exposure
  erw [exposure]
  dsimp only
  erw [cell]
  simp only [pure,EStateM.pure,bind,EStateM.bind,S05ZeroSizedSharedNonFreezeRetag.value]
  change _ = _
  simp only [UInt64.add_zero,S05ZeroCellCorrelatedTyped.mutableParent,S05ZeroCellCorrelatedTyped.mutableTag,Bool.false_eq_true,↓reduceIte] at mutableStep
  simp only [slice,RetagReferencePlace.sliceValue] at mutableStep ⊢
  erw [mutableStep]
  rfl

/-- The monadic bind carries every actual output state into the next operation:
expose original; wildcard A; mutable D; original write; wildcard B; zero V
through saved raw D; expose V; original write; mutable W through returned B.
D and V typed values are lexically scoped before the corresponding original
writes. The raw D scalar remains available; no tree node is removed to end a
handle's use. Frame-local storage/lifetime adequacy is a separate obligation. -/
def run {K U : Type} [DecidableEq K] (config : Config K U)
    (original : Provenance) (wildcard : Pointer Provenance) :
    MachineHooks.M K (ValidityMachine.UserState U) Output := do
  let savedRawD ← runFirstWrite config original wildcard
  let b ← requireRetag config
    (S05ZeroSizedSharedNonFreezeRetag.value config.memory.runtime.base wildcard config.sharedReference)
  let bPointer ← thin b
  do
    let v ← requireRetag config (slice savedRawD 0 config.mutableReference)
    let vPointer ← data v
    exposeScalar config vPointer
  PlaceMachine.writeMemory config.memory config.willValidate config.writeValue config.original
  let w ← requireRetag config (slice bPointer 2 config.mutableReference)
  return ⟨savedRawD,w⟩

abbrev Stored := EvalCoreMachine.Stored Unit Unit Unit Unit Unit Unit Unit Unit Machine.MinimalHost

/-- Production typed adapter with the actual auxiliary metadata catalog. -/
noncomputable def actualConfig {C F A : Type} (context : S05ZeroCellCorrelatedWrite.Context)
    (runtime : CompilerRuntimeQueries.Prepared)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State MiriMemoryKind Stored) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State MiriMemoryKind Stored) C F A) (choice : C)
    (baseHooks : TypedRetag.Hooks MiriMemoryKind Machine.RootUser)
    (budget : Nat) (id : AllocId) (base : UInt64) : Config MiriMemoryKind Stored where
  typed := TypedValidityProviders.retagHooks PriorCellMetadata.facts runtime context.access projection vtable context.pointers choice baseHooks
  pointers := context.pointers
  memory := context.access
  budget := budget
  sharedReference := PriorCellMetadata.sharedLayout
  mutableReference := PriorCellMetadata.sliceReferenceLayout
  original := ⟨⟨Pointer.new (some (.concrete id (tag 1))) (Size.ofBytes base),.none,none⟩,PriorCellMetadata.u16Layout⟩
  writeValue := .scalar S05ZeroCellCorrelatedWrite.word
  willValidate := fun _ => false

/-- A normalized exact machine description, preserving every field except
address exposure, the allocator's next tag, and the one live allocation. -/
def stageMachine
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (tree : BorrowTree) (next : BorTag) : MachineHooks.MachineState MiriMemoryKind Machine.RootUser :=
  {machine with
    user := {machine.user with addresses := exposedAddresses machine.user.addresses id}
    borrowTracker := some (withNext tracker next)
    memory := {machine.memory with live := (machine.memory.live.filter fun row => row.1 != id).push (id,{entry with allocation := S05ZeroCellCorrelatedWrite.sourceFor tree})}}

theorem source_extra (before after : BorrowTree) :
    (S05ZeroCellCorrelatedWrite.sourceFor before).setExtra after =
      S05ZeroCellCorrelatedWrite.sourceFor after := rfl

theorem exposure_membership (addresses : AllocAddresses.GlobalAddressState) (id : AllocId) :
    (exposedAddresses addresses id).exposed.contains id = true := by
  unfold exposedAddresses
  split
  · assumption
  · simp

theorem exposure_idempotent (addresses : AllocAddresses.GlobalAddressState) (id : AllocId) :
    exposedAddresses (exposedAddresses addresses id) id = exposedAddresses addresses id := by
  unfold exposedAddresses at *
  split <;> simp_all

theorem stage_lookup
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (tree : BorrowTree) (next : BorTag) :
    (stageMachine machine tracker id entry tree next).memory.live.find? (fun row => row.1 == id) =
      some (id,{entry with allocation := S05ZeroCellCorrelatedWrite.sourceFor tree}) :=
  MemoryCopyBridge.live_lookup_replaced machine.memory id _

theorem stage_replace
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (before after : BorrowTree) (next : BorTag) :
    let current := stageMachine machine tracker id entry before next
    {current with memory := {current.memory with live := (current.memory.live.filter fun row => row.1 != id).push (id,{entry with allocation := S05ZeroCellCorrelatedWrite.sourceFor after})}} =
      stageMachine machine tracker id entry after next := by
  dsimp only [stageMachine]
  rw [MemoryCopyBridge.live_update_twice]

theorem stage_retag
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (before after : BorrowTree) (oldNext newNext : BorTag) :
    afterRetag (stageMachine machine tracker id entry before oldNext) tracker newNext id
      {entry with allocation := S05ZeroCellCorrelatedWrite.sourceFor before} after =
      stageMachine machine tracker id entry after newNext := by
  dsimp only [afterRetag,stageMachine,RetagEntry.updatedMemory]
  rw [source_extra,MemoryCopyBridge.live_update_twice]

/-- Initial data for this one auxiliary-context finite execution. All fields
are compiler identities, initial geometry, or initial machine resources. -/
structure InitialFields (C F A : Type) where
  context : S05ZeroCellCorrelatedWrite.Context
  runtime : CompilerRuntimeQueries.Prepared
  projection : PlaceProjectionHooks Provenance (ValidityMachine.State MiriMemoryKind Stored) C MachineHooks.FrameExtra
  vtable : VTableHooks Provenance (ValidityMachine.State MiriMemoryKind Stored) C F A
  choice : C
  baseHooks : TypedRetag.Hooks MiriMemoryKind Machine.RootUser
  budget : Nat
  id : AllocId
  base : UInt64
  retag : RetagFacts (actualConfig context runtime projection vtable choice baseHooks budget id base)
    PriorCellMetadata.facts projection vtable choice
  compilerPin : context.prepared = PriorCellMetadata.actual.compiler
  imagePin : context.image = PriorCellMetadata.actual.prepared.image
  frames : Array CompilerFrameContext.ActualFrame
  frame : CompilerFrameContext.ActualFrame
  machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser
  tracker : MachineHooks.BorrowState
  entry : LocalAllocation Provenance BorrowTree MiriMemoryKind
  enabled : machine.borrowTracker = some tracker
  next : tracker.global.nextPointerTag = tag 2
  protections : tracker.global.protectedTags = {}
  root : tracker.global.rootPointerTags = #[(id,tag 1)]
  mode : machine.user.addresses.provenanceMode = .permissive
  noClocks : machine.dataRace = none
  noBackend : machine.user.payload.payload.user.backend = .none
  extras : (context.extras.get machine.user).allocations.find? (fun row => row.1 == id) = some (id,⟨none,#[]⟩)
  allocation : entry.allocation = S05ZeroCellCorrelatedWrite.sourceFor seed
  nonnull : base ≠ 0
  evenBase : base % 2 = 0
  geometry : WildcardGeneralHitReborrow.Geometry machine.user.addresses.intToPtrMap base base id entry.allocation.byteSize
  cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩
  present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry)
  runtimeWidth : context.access.runtime.base.pointerWidth = .w64
  little : context.access.runtime.base.endian = .little
  runtimeSize : context.access.runtime.pointerSize = Size.ofBytes 8

noncomputable def InitialFields.config {C F A : Type} (input : InitialFields C F A) : Config MiriMemoryKind Stored :=
  actualConfig input.context input.runtime input.projection input.vtable input.choice input.baseHooks input.budget input.id input.base

def InitialFields.at {C F A : Type} (input : InitialFields C F A) (tree : BorrowTree) (next : BorTag) :
    MachineHooks.State MiriMemoryKind Machine.RootUser :=
  Storage.withCurrent input.frames input.frame
    (stageMachine input.machine input.tracker input.id input.entry tree next)

theorem initial_to_d {C F A : Type} (input : InitialFields C F A) :
    runToD input.config (.concrete input.id (tag 1)) (Pointer.new .wildcard (Size.ofBytes input.base))
      (Storage.withCurrent input.frames input.frame input.machine) =
      .ok (Scalar.fromPointer input.context.access.runtime.base
        (Pointer.new (.concrete input.id (tag 3)) (Size.ofBytes input.base)))
        (input.at d.tree (tag 4)) := by
  have result := expose_a_d_from_fields input.config PriorCellMetadata.facts input.projection input.vtable
    input.choice input.retag input.frames input.frame input.machine input.tracker input.enabled input.next input.protections
    input.mode input.noClocks input.id input.entry input.base input.nonnull input.geometry input.cached input.present
    (by rw [input.allocation]; rfl) (by rw [input.allocation]; decide +kernel)
  simpa [InitialFields.config,actualConfig,afterRetag,afterExposure,InitialFields.at,stageMachine,
    RetagEntry.updatedMemory,input.allocation,source_extra,Array.filter_push,Array.filter_filter,withNext] using result

theorem first_write {C F A : Type} (input : InitialFields C F A) :
    PlaceMachine.writeMemory input.config.memory input.config.willValidate input.config.writeValue input.config.original
      (input.at d.tree (tag 4)) = .ok () (input.at firstWrite.tree (tag 4)) := by
  have result := S05ZeroCellCorrelatedWrite.write_from_fields input.context (input.at d.tree (tag 4)) input.config.original
    input.id input.base {input.entry with allocation := S05ZeroCellCorrelatedWrite.sourceFor d.tree}
    (withNext input.tracker (tag 4)) false rfl input.retag.pointerWidth input.cached
    (stage_lookup input.machine input.tracker input.id input.entry d.tree (tag 4))
    input.runtimeWidth input.little input.noClocks input.noBackend rfl input.protections input.extras
    rfl rfl rfl input.runtimeSize
  simpa only [InitialFields.config,actualConfig,InitialFields.at,Storage.withCurrent,
    S05ZeroCellCorrelatedWrite.outputTree,Bool.false_eq_true,↓reduceIte,stage_replace] using result

theorem through_first_write {C F A : Type} (input : InitialFields C F A) :
    runFirstWrite input.config (.concrete input.id (tag 1)) (Pointer.new .wildcard (Size.ofBytes input.base))
      (Storage.withCurrent input.frames input.frame input.machine) =
      .ok (Scalar.fromPointer input.context.access.runtime.base
        (Pointer.new (.concrete input.id (tag 3)) (Size.ofBytes input.base)))
        (input.at firstWrite.tree (tag 4)) := by
  unfold runFirstWrite
  simp only [bind,EStateM.bind]
  rw [initial_to_d input]
  dsimp only
  rw [first_write input]
  rfl

theorem cell_b {C F A : Type} (input : InitialFields C F A) :
    TypedRetag.retagPtrValue input.config.typed input.budget
      (S05ZeroSizedSharedNonFreezeRetag.value input.context.access.runtime.base
        (Pointer.new .wildcard (Size.ofBytes input.base)) PriorCellMetadata.sharedLayout)
      PriorCellMetadata.sharedLayout.ty .Default (input.at firstWrite.tree (tag 4)) =
      .ok (some (S05ZeroSizedSharedNonFreezeRetag.value input.context.access.runtime.base
        (Pointer.new (.concrete input.id (tag 4)) (Size.ofBytes input.base)) PriorCellMetadata.sharedLayout))
        (input.at b.tree (tag 5)) := by
  let machine := stageMachine input.machine input.tracker input.id input.entry firstWrite.tree (tag 4)
  let entry := {input.entry with allocation := S05ZeroCellCorrelatedWrite.sourceFor firstWrite.tree}
  let tracker := withNext input.tracker (tag 4)
  have room : tracker.global.nextPointerTag.value < 18446744073709551615 := by
    change (4 : UInt64) < 18446744073709551615
    decide
  have result := S05ZeroCellCorrelatedTyped.cell_pointer_from_fields input.config.typed PriorCellMetadata.facts input.config.memory
    input.projection input.vtable input.config.pointers input.choice input.retag.sources input.budget
    input.config.sharedReference input.retag.cellLayout input.retag.cellShape input.retag.cellPointee true true
    input.retag.cellUnpin input.retag.cellUnsafeUnpin input.retag.cellNonfreeze input.retag.cellDeref input.retag.cellQuery
    input.retag.cellSized input.retag.cellZero input.retag.cellAlign input.frames input.frame machine tracker rfl room
    input.id entry input.base input.base input.nonnull
    (by simpa only [machine,entry,stageMachine,exposedAddresses,input.allocation,S05ZeroCellCorrelatedWrite.sourceFor,Allocation.withExtra,Allocation.byteSize] using input.geometry)
    input.retag.pointerWidth (by change input.machine.user.addresses.provenanceMode ≠ .strict; rw [input.mode]; decide)
    (exposure_membership input.machine.user.addresses input.id) input.cached
    (stage_lookup input.machine input.tracker input.id input.entry firstWrite.tree (tag 4)) true rfl rfl
    input.retag.globalKind input.config.memory.globalHooks input.retag.ensureWiring input.retag.synchronize
  have child : S05ZeroSizedSharedNonFreezeRetag.resultTree entry.allocation.extra tracker.global.nextPointerTag = b.tree :=
    S05ZeroCellCorrelatedTyped.cell_result_tree true
  have advanced : ReferenceBorrowDriver.allocatedTracker tracker room = withNext input.tracker (tag 5) := rfl
  rw [child] at result
  simp only [ReferenceBorrowDriver.allocatedMachine,advanced] at result
  simpa [InitialFields.config,actualConfig,InitialFields.at,Storage.withCurrent,machine,entry,tracker,
    stageMachine,RetagEntry.updatedMemory,source_extra,Array.filter_push,Array.filter_filter,withNext] using result

theorem mutable_stage {C F A : Type} (input : InitialFields C F A) (stage : Bool) :
    TypedRetag.retagPtrValue input.config.typed input.budget
      (RetagReferencePlace.sliceValue input.context.access.runtime.base
        (Pointer.new (.concrete input.id (S05ZeroCellCorrelatedTyped.mutableParent stage)) (Size.ofBytes input.base)) 2
        PriorCellMetadata.sliceReferenceLayout)
      PriorCellMetadata.sliceReferenceLayout.ty .Default
      (input.at (S05ZeroCellCorrelatedTyped.mutableInput stage) (S05ZeroCellCorrelatedTyped.mutableTag stage)) =
      .ok (some (RetagReferencePlace.sliceValue input.context.access.runtime.base
        (Pointer.new (.concrete input.id (S05ZeroCellCorrelatedTyped.mutableTag stage)) (Size.ofBytes input.base)) 2
        PriorCellMetadata.sliceReferenceLayout))
        (input.at (S05ZeroCellCorrelatedTyped.mutableResult stage) (if stage then tag 7 else tag 4)) := by
  let machine := stageMachine input.machine input.tracker input.id input.entry
    (S05ZeroCellCorrelatedTyped.mutableInput stage) (S05ZeroCellCorrelatedTyped.mutableTag stage)
  let entry := {input.entry with allocation := S05ZeroCellCorrelatedWrite.sourceFor (S05ZeroCellCorrelatedTyped.mutableInput stage)}
  let tracker := withNext input.tracker (S05ZeroCellCorrelatedTyped.mutableTag stage)
  let place := RetagReferencePlace.slicePlace
    (Pointer.new (.concrete input.id (S05ZeroCellCorrelatedTyped.mutableParent stage)) (Size.ofBytes (input.base+0))) 2 input.retag.sliceLayout
  have room : tracker.global.nextPointerTag.value < 18446744073709551615 := by
    cases stage
    · change (3 : UInt64) < 18446744073709551615
      decide
    · change (6 : UInt64) < 18446744073709551615
      decide
  have result := S05ZeroCellCorrelatedTyped.mutable_pointer_from_fields input.config.typed PriorCellMetadata.facts input.config.memory
    input.projection input.vtable input.config.pointers input.choice input.retag.sources input.budget place
    input.frames input.frame machine tracker rfl room input.id entry input.base stage rfl input.protections rfl
    input.retag.sliceFreeze rfl input.retag.pointerWiring input.retag.pointerWidth input.cached (by decide)
    (by change (0 : UInt64).toNat + (2 : UInt64).toNat ≤ (2 : UInt64).toNat; decide)
    input.retag.globalKind input.config.memory.globalHooks input.retag.ensureWiring input.retag.synchronize
    (stage_lookup input.machine input.tracker input.id input.entry _ _) input.noClocks input.config.mutableReference
    input.retag.sliceShape input.retag.slicePointee input.retag.sliceUnpin input.retag.sliceUnsafeUnpin input.retag.sliceDeref
    input.retag.sliceQuery input.retag.sliceAlign rfl (input.retag.sliceMetadata _ 2 (Or.inr rfl))
  have advanced : ReferenceBorrowDriver.allocatedTracker tracker room =
      withNext input.tracker (if stage then tag 7 else tag 4) := by cases stage <;> rfl
  simp only [ReferenceBorrowDriver.allocatedMachine,advanced] at result
  simpa [InitialFields.config,actualConfig,InitialFields.at,Storage.withCurrent,machine,entry,tracker,
    stageMachine,RetagEntry.updatedMemory,source_extra,Array.filter_push,Array.filter_filter,withNext] using result

theorem zero_v {C F A : Type} (input : InitialFields C F A) :
    TypedRetag.retagPtrValue input.config.typed input.budget
      (RetagReferencePlace.sliceValue input.context.access.runtime.base
        (Pointer.new (.concrete input.id (tag 3)) (Size.ofBytes input.base)) 0 PriorCellMetadata.sliceReferenceLayout)
      PriorCellMetadata.sliceReferenceLayout.ty .Default (input.at b.tree (tag 5)) =
      .ok (some (RetagReferencePlace.sliceValue input.context.access.runtime.base
        (Pointer.new (.concrete input.id (tag 5)) (Size.ofBytes input.base)) 0 PriorCellMetadata.sliceReferenceLayout))
        (input.at v.tree (tag 6)) := by
  let machine := stageMachine input.machine input.tracker input.id input.entry b.tree (tag 5)
  let entry := {input.entry with allocation := S05ZeroCellCorrelatedWrite.sourceFor b.tree}
  let tracker := withNext input.tracker (tag 5)
  let place := RetagReferencePlace.slicePlace
    (Pointer.new (.concrete input.id (tag 3)) (Size.ofBytes (input.base+0))) 0 input.retag.sliceLayout
  have room : tracker.global.nextPointerTag.value < 18446744073709551615 := by
    change (5 : UInt64) < 18446744073709551615
    decide
  have result := S05ZeroCellCorrelatedTyped.zero_v_pointer_from_fields input.config.typed PriorCellMetadata.facts input.config.memory
    input.projection input.vtable input.config.pointers input.choice input.retag.sources input.budget place
    input.frames input.frame machine tracker rfl room input.id entry input.base rfl rfl input.retag.sliceFreeze rfl
    input.retag.pointerWiring input.retag.pointerWidth input.cached input.retag.globalKind input.config.memory.globalHooks
    input.retag.ensureWiring input.retag.synchronize (stage_lookup input.machine input.tracker input.id input.entry b.tree (tag 5))
    input.config.mutableReference input.retag.sliceShape input.retag.slicePointee input.retag.sliceUnpin input.retag.sliceUnsafeUnpin
    input.retag.sliceDeref input.retag.sliceQuery input.retag.sliceAlign rfl (input.retag.sliceMetadata _ 0 (Or.inl rfl))
  have advanced : ReferenceBorrowDriver.allocatedTracker tracker room = withNext input.tracker (tag 6) := rfl
  simp only [ReferenceBorrowDriver.allocatedMachine,advanced] at result
  simpa [InitialFields.config,actualConfig,InitialFields.at,Storage.withCurrent,machine,entry,tracker,
    stageMachine,RetagEntry.updatedMemory,source_extra,Array.filter_push,Array.filter_filter,withNext] using result

theorem expose_v {C F A : Type} (input : InitialFields C F A) :
    PointerMachine.exposeProvenance input.config.pointers (.concrete input.id (tag 5))
      (input.at v.tree (tag 6)) = .ok () (input.at exposedV.tree (tag 6)) := by
  have result := expose_from_fields input.config.pointers (input.at v.tree (tag 6))
    (withNext input.tracker (tag 6)) rfl input.protections input.mode input.id
    {input.entry with allocation := S05ZeroCellCorrelatedWrite.sourceFor v.tree}
    (stage_lookup input.machine input.tracker input.id input.entry v.tree (tag 6)) true rfl input.retag.globalKind
    input.config.memory.globalHooks input.retag.ensureWiring input.retag.synchronize
  simpa [exposureTag,exposureOutput,InitialFields.config,actualConfig,InitialFields.at,Storage.withCurrent,
    stageMachine,RetagEntry.updatedMemory,source_extra,exposure_idempotent,Array.filter_push,Array.filter_filter] using result

theorem second_write {C F A : Type} (input : InitialFields C F A) :
    PlaceMachine.writeMemory input.config.memory input.config.willValidate input.config.writeValue input.config.original
      (input.at exposedV.tree (tag 6)) = .ok () (input.at secondWrite.tree (tag 6)) := by
  have result := S05ZeroCellCorrelatedWrite.write_from_fields input.context (input.at exposedV.tree (tag 6)) input.config.original
    input.id input.base {input.entry with allocation := S05ZeroCellCorrelatedWrite.sourceFor exposedV.tree}
    (withNext input.tracker (tag 6)) true rfl input.retag.pointerWidth input.cached
    (stage_lookup input.machine input.tracker input.id input.entry exposedV.tree (tag 6))
    input.runtimeWidth input.little input.noClocks input.noBackend rfl input.protections input.extras
    rfl rfl rfl input.runtimeSize
  simpa only [InitialFields.config,actualConfig,InitialFields.at,Storage.withCurrent,
    S05ZeroCellCorrelatedWrite.outputTree,↓reduceIte,stage_replace] using result

/-- The requested finite route fixes the original tag once and reuses the
same wildcard address at both shared-reference creations. -/
def runFixed {K U : Type} [DecidableEq K] (config : Config K U)
    (id : AllocId) (address : UInt64) :
    MachineHooks.M K (ValidityMachine.UserState U) Output :=
  run config (.concrete id (tag 1)) (Pointer.new .wildcard (Size.ofBytes address))

/-- Success of the entire fixed finite operation route, including both actual
initialized writes and the returned W pointer. Ordinary-call acceptance and
frame-local lifetime validation are not conclusions of this theorem. -/
theorem run_fixed_from_fields {C F A : Type} (input : InitialFields C F A) :
    runFixed input.config input.id input.base (Storage.withCurrent input.frames input.frame input.machine) =
      .ok ⟨Scalar.fromPointer input.context.access.runtime.base
          (Pointer.new (.concrete input.id (tag 3)) (Size.ofBytes input.base)),
        RetagReferencePlace.sliceValue input.context.access.runtime.base
          (Pointer.new (.concrete input.id (tag 6)) (Size.ofBytes input.base)) 2 PriorCellMetadata.sliceReferenceLayout⟩
        (input.at w.tree (tag 7)) := by
  have bStep := cell_b input
  have vStep := zero_v input
  have wStep := mutable_stage input true
  simp only [S05ZeroCellCorrelatedTyped.mutableInput,S05ZeroCellCorrelatedTyped.mutableParent,
    S05ZeroCellCorrelatedTyped.mutableTag,S05ZeroCellCorrelatedTyped.mutableResult,↓reduceIte] at wStep
  unfold runFixed run
  simp only [bind,EStateM.bind]
  rw [through_first_write input]
  dsimp only
  unfold requireRetag thin data exposeScalar
  simp only [bind,EStateM.bind]
  erw [bStep]
  simp only [pure,EStateM.pure,bind,EStateM.bind,S05ZeroSizedSharedNonFreezeRetag.value]
  simp only [slice,RetagReferencePlace.sliceValue] at vStep wStep ⊢
  erw [vStep]
  have runtimeEq : input.config.memory.runtime.base = input.context.access.runtime.base := rfl
  simp only [runtimeEq,pure,EStateM.pure,bind,EStateM.bind,CopyIntrinsic.pointer_scalar_roundtrip,
    Pointer.withOptionalProvenance,Pointer.new]
  erw [expose_v input]
  dsimp only
  erw [second_write input]
  dsimp only
  erw [wStep]
  rfl

/-- The output pointer scalar is literally copied into the next slice input.
This says nothing about the permission of a positive-length dereference. -/
theorem slice_preserves_data (pointer : Scalar Provenance) (length : UInt64)
    (layout : LocalLayout) :
    (slice pointer length layout).imm =
      .scalarPair pointer (Scalar.fromScalarInt (ScalarInt.ofUInt64 length)) := rfl

end DuplicatePrefix.S05ZeroCellCorrelatedMachine

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05ZeroCellCorrelatedMachine." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved correlated-machine dependency {dependency}"
